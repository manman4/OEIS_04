/*
 * A400112 -- memoized exact search.
 *
 * Count self-avoiding lattice paths from (0,0) to (n,n) in an n by n
 * square for which adjacent maximal straight segments have unequal lengths.
 *
 * Version 01 enumerates every surviving continuation separately.  This
 * version memoizes a complete future state:
 *
 *   (visited vertices, endpoint, last direction,
 *    current segment length, previous segment length).
 *
 * Two valid prefixes with the same state have exactly the same unused grid
 * and the same constraint on the next turn, so their continuation counts are
 * identical.  Cache keys are compared in full after hashing; collisions
 * cannot change the answer.  The cache is bounded and direct-mapped.
 * Replacing an entry merely causes later recomputation and is therefore safe.
 * Each worker owns its cache, eliminating cache locks and data races.
 *
 * Reflection in y=x pairs east-first and north-first solutions.  For n>0 we
 * search east-first paths and double the checked unsigned 128-bit count.
 * Goal-disconnection pruning is applied only when a completion is impossible.
 *
 * Resource controls:
 *   - --cache-mib bounds the total requested memo-table memory;
 *   - failed cache allocations are retried at smaller powers of two;
 *   - prefix task storage has an explicit hard limit;
 *   - all exact-count additions and the final doubling are overflow-checked.
 *
 * Build (works with the Anaconda clang 14 used for this repository):
 *   clang -O3 -std=c11 -Wall -Wextra -Wpedantic -pthread \
 *       400112_02.c -o 400112_02
 *
 * Usage:
 *   ./400112_02 [OPTIONS] MAX_N
 *   ./400112_02 --self-test
 *
 * Examples:
 *   ./400112_02 7
 *   ./400112_02 --threads 8 --cache-mib 512 --start 8 8
 *
 * Results go to stdout as "n a(n)"; diagnostics go to stderr.
 */

#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <inttypes.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#if defined(__APPLE__)
extern int sysctlbyname(const char *, void *, size_t *, void *, size_t);
#endif

#if !defined(__SIZEOF_INT128__)
#error "400112_02.c requires unsigned __int128"
#endif

__extension__ typedef unsigned __int128 U128;

#define MAX_N 12U
#define MAX_SIDE (MAX_N + 1U)
#define MAX_VERTICES (MAX_SIDE * MAX_SIDE)
#define VISITED_WORDS ((MAX_VERTICES + 63U) / 64U)
#define MAX_THREADS 256U
#define DEFAULT_SPLIT_DEPTH 14U
#define MAX_SPLIT_DEPTH 24U
#define DEFAULT_CONNECTIVITY_INTERVAL 4U
#define DEFAULT_CACHE_MIB 256U
#define MAX_CACHE_MIB 4096U
#define MAX_PREFIX_TASKS UINT64_C(5000000)
#define SELF_TEST_MAX_N 4U

enum Direction {
    EAST = 0,
    NORTH = 1,
    WEST = 2,
    SOUTH = 3,
    DIRECTION_COUNT = 4
};

static const int direction_x[DIRECTION_COUNT] = {1, 0, -1, 0};
static const int direction_y[DIRECTION_COUNT] = {0, 1, 0, -1};

typedef struct {
    unsigned n;
    unsigned side;
    unsigned vertex_count;
    unsigned goal;
    unsigned connectivity_interval;
    int16_t neighbor[MAX_VERTICES][DIRECTION_COUNT];
} Grid;

typedef struct {
    uint64_t visited[VISITED_WORDS];
    uint16_t vertex;
    uint16_t depth;
    uint8_t last_direction;
    uint8_t current_length;
    uint8_t previous_length;
} Task;

typedef struct {
    Task *items;
    size_t count;
    size_t capacity;
    U128 early_count;
    bool overflow;
} TaskList;

typedef struct {
    uint64_t visited[VISITED_WORDS];
    U128 value;
    uint64_t hash;
    uint16_t vertex;
    uint8_t last_direction;
    uint8_t current_length;
    uint8_t previous_length;
    bool occupied;
} CacheEntry;

typedef struct {
    CacheEntry *entries;
    size_t capacity;
    size_t mask;
    U128 lookups;
    U128 hits;
    U128 stores;
} Cache;

typedef struct {
    const Grid *grid;
    const Task *tasks;
    size_t task_count;
    atomic_size_t *next_task;
    Cache cache;
    U128 count;
    bool overflow;
} Worker;

typedef struct {
    unsigned start;
    unsigned maximum;
    unsigned threads;
    unsigned split_depth;
    unsigned connectivity_interval;
    unsigned cache_mib;
    bool quiet;
    bool self_test;
    bool have_maximum;
} Options;

static const uint64_t known_prefix[] = {
    UINT64_C(1), UINT64_C(0), UINT64_C(4), UINT64_C(20),
    UINT64_C(266), UINT64_C(6080), UINT64_C(343354),
    UINT64_C(42466268), UINT64_C(11827271764)
};

static _Noreturn void die(const char *message)
{
    fprintf(stderr, "error: %s\n", message);
    exit(EXIT_FAILURE);
}

static void *xrealloc(void *pointer, size_t size)
{
    void *result = realloc(pointer, size == 0U ? 1U : size);
    if (result == NULL) {
        free(pointer);
        die("out of memory");
    }
    return result;
}

static unsigned parse_unsigned(const char *text, unsigned maximum,
                               const char *label)
{
    char *end = NULL;
    if (text == NULL || *text == '\0' || *text == '-') {
        fprintf(stderr, "error: invalid %s: %s\n", label,
                text == NULL ? "(null)" : text);
        exit(EXIT_FAILURE);
    }
    errno = 0;
    const unsigned long value = strtoul(text, &end, 10);
    if (errno == ERANGE || end == text || *end != '\0' || value > maximum) {
        fprintf(stderr, "error: %s must be in 0..%u: %s\n",
                label, maximum, text);
        exit(EXIT_FAILURE);
    }
    return (unsigned)value;
}

static unsigned default_thread_count(void)
{
#if defined(__APPLE__)
    int logical_cpus = 1;
    size_t size = sizeof(logical_cpus);
    if (sysctlbyname("hw.logicalcpu", &logical_cpus, &size, NULL, 0) != 0 ||
        logical_cpus < 1) {
        return 1U;
    }
    const long count = logical_cpus;
#else
    const long count = sysconf(_SC_NPROCESSORS_ONLN);
#endif
    if (count < 1L) return 1U;
    if (count > (long)MAX_THREADS) return MAX_THREADS;
    return (unsigned)count;
}

static double monotonic_seconds(void)
{
    struct timespec value;
    if (clock_gettime(CLOCK_MONOTONIC, &value) != 0)
        die("clock_gettime failed");
    return (double)value.tv_sec + 1.0e-9 * (double)value.tv_nsec;
}

static bool add_u128(U128 *target, U128 value)
{
    const U128 maximum = ~(U128)0;
    if (*target > maximum - value) return false;
    *target += value;
    return true;
}

static bool increment_u128(U128 *target)
{
    return add_u128(target, 1U);
}

static bool double_u128(U128 *value)
{
    const U128 maximum = ~(U128)0;
    if (*value > maximum / 2U) return false;
    *value *= 2U;
    return true;
}

static int print_u128(FILE *stream, U128 value)
{
    char reverse[40];
    char text[40];
    size_t length = 0U;
    do {
        reverse[length++] = (char)('0' + (unsigned)(value % 10U));
        value /= 10U;
    } while (value != 0U);
    for (size_t i = 0U; i < length; ++i)
        text[i] = reverse[length - 1U - i];
    text[length] = '\0';
    return fputs(text, stream) == EOF ? -1 : 0;
}

static inline bool bit_is_set(const uint64_t visited[VISITED_WORDS],
                              unsigned vertex)
{
    return (visited[vertex >> 6U] &
            (UINT64_C(1) << (vertex & 63U))) != 0U;
}

static inline void set_bit(uint64_t visited[VISITED_WORDS], unsigned vertex)
{
    visited[vertex >> 6U] |= UINT64_C(1) << (vertex & 63U);
}

static inline void clear_bit(uint64_t visited[VISITED_WORDS], unsigned vertex)
{
    visited[vertex >> 6U] &= ~(UINT64_C(1) << (vertex & 63U));
}

static unsigned vertex_of(const Grid *grid, unsigned x, unsigned y)
{
    return y * grid->side + x;
}

static void initialize_grid(Grid *grid, unsigned n,
                            unsigned connectivity_interval)
{
    memset(grid, 0, sizeof(*grid));
    grid->n = n;
    grid->side = n + 1U;
    grid->vertex_count = grid->side * grid->side;
    grid->goal = vertex_of(grid, n, n);
    grid->connectivity_interval = connectivity_interval;

    for (unsigned vertex = 0U; vertex < grid->vertex_count; ++vertex)
        for (unsigned direction = 0U; direction < DIRECTION_COUNT; ++direction)
            grid->neighbor[vertex][direction] = -1;

    for (unsigned y = 0U; y <= n; ++y) {
        for (unsigned x = 0U; x <= n; ++x) {
            const unsigned vertex = vertex_of(grid, x, y);
            for (unsigned direction = 0U; direction < DIRECTION_COUNT;
                 ++direction) {
                const int next_x = (int)x + direction_x[direction];
                const int next_y = (int)y + direction_y[direction];
                if (next_x >= 0 && next_x <= (int)n &&
                    next_y >= 0 && next_y <= (int)n) {
                    grid->neighbor[vertex][direction] =
                        (int16_t)vertex_of(grid, (unsigned)next_x,
                                           (unsigned)next_y);
                }
            }
        }
    }
}

static bool goal_has_entrance(const Grid *grid,
                              const uint64_t visited[VISITED_WORDS],
                              unsigned current)
{
    for (unsigned direction = 0U; direction < DIRECTION_COUNT; ++direction) {
        const int neighbor = grid->neighbor[grid->goal][direction];
        if (neighbor < 0) continue;
        if ((unsigned)neighbor == current ||
            !bit_is_set(visited, (unsigned)neighbor)) return true;
    }
    return false;
}

/* Keep only the unvisited region reachable from the current endpoint without
 * passing through the goal.  Other unvisited pockets can never occur in a
 * completion, so marking them unavailable is an exact state normalization.
 * The goal is reachable if and only if it is encountered by this flood-fill. */
static bool canonicalize_reachable_region(
    const Grid *grid, uint64_t visited[VISITED_WORDS], unsigned current)
{
    uint64_t seen[VISITED_WORDS] = {0U};
    uint16_t queue[MAX_VERTICES];
    unsigned begin = 0U;
    unsigned end = 0U;
    bool reached_goal = false;
    queue[end++] = (uint16_t)current;
    set_bit(seen, current);

    while (begin < end) {
        const unsigned vertex = queue[begin++];
        for (unsigned direction = 0U; direction < DIRECTION_COUNT;
             ++direction) {
            const int next = grid->neighbor[vertex][direction];
            if (next < 0) continue;
            const unsigned candidate = (unsigned)next;
            if (candidate == grid->goal) {
                reached_goal = true;
                set_bit(seen, candidate);
                continue;
            }
            if (bit_is_set(visited, candidate) ||
                bit_is_set(seen, candidate)) continue;
            set_bit(seen, candidate);
            queue[end++] = (uint16_t)candidate;
        }
    }
    if (!reached_goal) return false;
    for (unsigned vertex = 0U; vertex < grid->vertex_count; ++vertex)
        if (!bit_is_set(seen, vertex)) set_bit(visited, vertex);
    return true;
}

static bool state_can_continue(const Grid *grid,
                               uint64_t visited[VISITED_WORDS],
                               unsigned current, unsigned depth)
{
    if (!goal_has_entrance(grid, visited, current)) return false;
    if (grid->connectivity_interval == 0U ||
        depth % grid->connectivity_interval != 0U) return true;
    return canonicalize_reachable_region(grid, visited, current);
}

static bool extend_segment(unsigned last_direction, unsigned current_length,
                           unsigned previous_length, unsigned direction,
                           unsigned *new_current, unsigned *new_previous)
{
    if (direction == last_direction) {
        *new_current = current_length + 1U;
        *new_previous = previous_length;
        return true;
    }
    if (current_length == previous_length) return false;
    *new_current = 1U;
    *new_previous = current_length;
    return true;
}

static void append_task(TaskList *list,
                        const uint64_t visited[VISITED_WORDS],
                        unsigned vertex, unsigned depth,
                        unsigned last_direction, unsigned current_length,
                        unsigned previous_length)
{
    if ((uint64_t)list->count >= MAX_PREFIX_TASKS)
        die("prefix task limit reached; reduce --split-depth");
    if (list->count == list->capacity) {
        size_t new_capacity = list->capacity == 0U ? 1024U
                                                    : list->capacity * 2U;
        if (new_capacity > (size_t)MAX_PREFIX_TASKS)
            new_capacity = (size_t)MAX_PREFIX_TASKS;
        if (new_capacity <= list->capacity ||
            new_capacity > SIZE_MAX / sizeof(*list->items))
            die("task list size overflow");
        list->items = xrealloc(list->items,
                               new_capacity * sizeof(*list->items));
        list->capacity = new_capacity;
    }
    Task *task = &list->items[list->count++];
    memcpy(task->visited, visited, sizeof(task->visited));
    task->vertex = (uint16_t)vertex;
    task->depth = (uint16_t)depth;
    task->last_direction = (uint8_t)last_direction;
    task->current_length = (uint8_t)current_length;
    task->previous_length = (uint8_t)previous_length;
}

static void generate_tasks(const Grid *grid, TaskList *list,
                           uint64_t visited[VISITED_WORDS],
                           unsigned vertex, unsigned depth,
                           unsigned last_direction, unsigned current_length,
                           unsigned previous_length, unsigned split_depth)
{
    if (list->overflow) return;
    if (depth >= split_depth) {
        append_task(list, visited, vertex, depth, last_direction,
                    current_length, previous_length);
        return;
    }
    for (unsigned direction = 0U; direction < DIRECTION_COUNT; ++direction) {
        const int next = grid->neighbor[vertex][direction];
        if (next < 0 || bit_is_set(visited, (unsigned)next)) continue;
        unsigned new_current;
        unsigned new_previous;
        if (!extend_segment(last_direction, current_length, previous_length,
                            direction, &new_current, &new_previous)) continue;
        const unsigned candidate = (unsigned)next;
        if (candidate == grid->goal) {
            if (new_current != new_previous &&
                !increment_u128(&list->early_count)) {
                list->overflow = true;
                return;
            }
            continue;
        }
        uint64_t child_visited[VISITED_WORDS];
        memcpy(child_visited, visited, sizeof(child_visited));
        set_bit(child_visited, candidate);
        if (state_can_continue(grid, child_visited, candidate, depth + 1U))
            generate_tasks(grid, list, child_visited, candidate, depth + 1U,
                           direction, new_current, new_previous, split_depth);
    }
}

static uint64_t mix64(uint64_t value)
{
    value ^= value >> 30U;
    value *= UINT64_C(0xbf58476d1ce4e5b9);
    value ^= value >> 27U;
    value *= UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31U);
}

static uint64_t state_hash(const uint64_t visited[VISITED_WORDS],
                           unsigned vertex, unsigned last_direction,
                           unsigned current_length, unsigned previous_length)
{
    uint64_t hash = UINT64_C(0x6a09e667f3bcc909);
    for (unsigned i = 0U; i < VISITED_WORDS; ++i)
        hash ^= mix64(visited[i] + hash + (uint64_t)i);
    uint64_t tail = (uint64_t)vertex;
    tail |= (uint64_t)last_direction << 16U;
    tail |= (uint64_t)current_length << 24U;
    tail |= (uint64_t)previous_length << 32U;
    return mix64(hash ^ tail);
}

static bool cache_lookup(Cache *cache,
                         const uint64_t visited[VISITED_WORDS],
                         unsigned vertex, unsigned last_direction,
                         unsigned current_length, unsigned previous_length,
                         U128 *value)
{
    if (cache->capacity == 0U) return false;
    if (!increment_u128(&cache->lookups)) die("cache statistic overflow");
    const uint64_t hash = state_hash(visited, vertex, last_direction,
                                     current_length, previous_length);
    const CacheEntry *entry = &cache->entries[(size_t)hash & cache->mask];
    if (!entry->occupied || entry->hash != hash || entry->vertex != vertex ||
        entry->last_direction != last_direction ||
        entry->current_length != current_length ||
        entry->previous_length != previous_length ||
        memcmp(entry->visited, visited, sizeof(entry->visited)) != 0) {
        return false;
    }
    if (!increment_u128(&cache->hits)) die("cache statistic overflow");
    *value = entry->value;
    return true;
}

static void cache_store(Cache *cache,
                        const uint64_t visited[VISITED_WORDS],
                        unsigned vertex, unsigned last_direction,
                        unsigned current_length, unsigned previous_length,
                        U128 value)
{
    if (cache->capacity == 0U) return;
    const uint64_t hash = state_hash(visited, vertex, last_direction,
                                     current_length, previous_length);
    CacheEntry *entry = &cache->entries[(size_t)hash & cache->mask];
    memcpy(entry->visited, visited, sizeof(entry->visited));
    entry->value = value;
    entry->hash = hash;
    entry->vertex = (uint16_t)vertex;
    entry->last_direction = (uint8_t)last_direction;
    entry->current_length = (uint8_t)current_length;
    entry->previous_length = (uint8_t)previous_length;
    entry->occupied = true;
    if (!increment_u128(&cache->stores)) die("cache statistic overflow");
}

static U128 memoized_count(Worker *worker,
                           uint64_t visited[VISITED_WORDS],
                           unsigned vertex, unsigned depth,
                           unsigned last_direction, unsigned current_length,
                           unsigned previous_length)
{
    if (worker->overflow) return 0U;
    U128 cached;
    if (cache_lookup(&worker->cache, visited, vertex, last_direction,
                     current_length, previous_length, &cached)) return cached;

    U128 total = 0U;
    const Grid *grid = worker->grid;
    for (unsigned direction = 0U; direction < DIRECTION_COUNT; ++direction) {
        const int next = grid->neighbor[vertex][direction];
        if (next < 0 || bit_is_set(visited, (unsigned)next)) continue;
        unsigned new_current;
        unsigned new_previous;
        if (!extend_segment(last_direction, current_length, previous_length,
                            direction, &new_current, &new_previous)) continue;
        const unsigned candidate = (unsigned)next;
        if (candidate == grid->goal) {
            if (new_current != new_previous && !increment_u128(&total)) {
                worker->overflow = true;
                return 0U;
            }
            continue;
        }
        uint64_t child_visited[VISITED_WORDS];
        memcpy(child_visited, visited, sizeof(child_visited));
        set_bit(child_visited, candidate);
        if (state_can_continue(grid, child_visited, candidate, depth + 1U)) {
            const U128 child = memoized_count(
                worker, child_visited, candidate, depth + 1U, direction,
                new_current, new_previous);
            if (worker->overflow || !add_u128(&total, child)) {
                worker->overflow = true;
                return 0U;
            }
        }
    }
    cache_store(&worker->cache, visited, vertex, last_direction,
                current_length, previous_length, total);
    return total;
}

static void *worker_main(void *argument)
{
    Worker *worker = argument;
    for (;;) {
        const size_t index = atomic_fetch_add_explicit(
            worker->next_task, 1U, memory_order_relaxed);
        if (index >= worker->task_count || worker->overflow) break;
        const Task *task = &worker->tasks[index];
        uint64_t visited[VISITED_WORDS];
        memcpy(visited, task->visited, sizeof(visited));
        const U128 value = memoized_count(
            worker, visited, task->vertex, task->depth,
            task->last_direction, task->current_length,
            task->previous_length);
        if (worker->overflow || !add_u128(&worker->count, value)) {
            worker->overflow = true;
            break;
        }
    }
    return NULL;
}

static size_t floor_power_of_two(size_t value)
{
    if (value == 0U) return 0U;
    size_t result = 1U;
    while (result <= value / 2U) result *= 2U;
    return result;
}

static size_t allocate_caches(Worker *workers, unsigned thread_count,
                              unsigned requested_mib)
{
    if (requested_mib == 0U) return 0U;
    const size_t total_bytes = (size_t)requested_mib * 1024U * 1024U;
    const size_t per_worker = total_bytes / thread_count;
    size_t capacity = floor_power_of_two(per_worker / sizeof(CacheEntry));

    while (capacity >= 1024U) {
        bool success = true;
        for (unsigned i = 0U; i < thread_count; ++i) {
            workers[i].cache.entries = calloc(capacity, sizeof(CacheEntry));
            if (workers[i].cache.entries == NULL) {
                success = false;
                for (unsigned j = 0U; j <= i; ++j) {
                    free(workers[j].cache.entries);
                    workers[j].cache.entries = NULL;
                }
                break;
            }
        }
        if (success) {
            for (unsigned i = 0U; i < thread_count; ++i) {
                workers[i].cache.capacity = capacity;
                workers[i].cache.mask = capacity - 1U;
            }
            return capacity;
        }
        capacity /= 2U;
    }
    return 0U;
}

static U128 count_memoized(unsigned n, unsigned requested_threads,
                           unsigned split_depth,
                           unsigned connectivity_interval,
                           unsigned cache_mib, bool progress)
{
    if (n == 0U) return 1U;
    Grid grid;
    initialize_grid(&grid, n, connectivity_interval);
    uint64_t visited[VISITED_WORDS] = {0U};
    const unsigned start = vertex_of(&grid, 0U, 0U);
    const unsigned first = vertex_of(&grid, 1U, 0U);
    set_bit(visited, start);
    set_bit(visited, first);

    const unsigned maximum_depth = grid.vertex_count - 1U;
    if (split_depth > maximum_depth) split_depth = maximum_depth;
    TaskList tasks = {0};
    generate_tasks(&grid, &tasks, visited, first, 1U, EAST, 1U, 0U,
                   split_depth);
    if (tasks.overflow) {
        free(tasks.items);
        die("unsigned 128-bit count overflow while generating tasks");
    }
    if (tasks.count == 0U) {
        U128 result = tasks.early_count;
        free(tasks.items);
        if (!double_u128(&result)) die("unsigned 128-bit count overflow");
        return result;
    }

    unsigned thread_count = requested_threads;
    if (thread_count > tasks.count) thread_count = (unsigned)tasks.count;
    if (thread_count == 0U) thread_count = 1U;
    Worker *workers = calloc(thread_count, sizeof(*workers));
    pthread_t *threads = calloc(thread_count, sizeof(*threads));
    if (workers == NULL || threads == NULL) {
        free(workers);
        free(threads);
        free(tasks.items);
        die("out of memory allocating workers");
    }
    const size_t cache_capacity =
        allocate_caches(workers, thread_count, cache_mib);
    const size_t actual_cache_bytes =
        cache_capacity * sizeof(CacheEntry) * thread_count;

    if (progress) {
        fprintf(stderr,
                "n=%u: %zu prefix tasks at depth %u, %u thread%s, "
                "%.1f MiB cache\n",
                n, tasks.count, split_depth, thread_count,
                thread_count == 1U ? "" : "s",
                (double)actual_cache_bytes / (1024.0 * 1024.0));
        fflush(stderr);
    }

    atomic_size_t next_task;
    atomic_init(&next_task, 0U);
    for (unsigned i = 0U; i < thread_count; ++i) {
        workers[i].grid = &grid;
        workers[i].tasks = tasks.items;
        workers[i].task_count = tasks.count;
        workers[i].next_task = &next_task;
        if (pthread_create(&threads[i], NULL, worker_main, &workers[i]) != 0)
            die("pthread_create failed");
    }
    for (unsigned i = 0U; i < thread_count; ++i)
        if (pthread_join(threads[i], NULL) != 0) die("pthread_join failed");

    U128 half = tasks.early_count;
    U128 lookups = 0U;
    U128 hits = 0U;
    U128 stores = 0U;
    for (unsigned i = 0U; i < thread_count; ++i) {
        if (workers[i].overflow || !add_u128(&half, workers[i].count) ||
            !add_u128(&lookups, workers[i].cache.lookups) ||
            !add_u128(&hits, workers[i].cache.hits) ||
            !add_u128(&stores, workers[i].cache.stores)) {
            die("unsigned 128-bit count or statistic overflow");
        }
    }

    if (progress && cache_capacity != 0U) {
        fputs("cache: ", stderr);
        print_u128(stderr, hits);
        fputc('/', stderr);
        print_u128(stderr, lookups);
        fputs(" hits, ", stderr);
        print_u128(stderr, stores);
        fputs(" stores\n", stderr);
    }

    for (unsigned i = 0U; i < thread_count; ++i)
        free(workers[i].cache.entries);
    free(workers);
    free(threads);
    free(tasks.items);
    if (!double_u128(&half)) die("unsigned 128-bit count overflow");
    return half;
}

/* Independent oracle: enumerate all simple paths and inspect the complete
 * direction word only at the goal. */
static bool complete_word_is_valid(const uint8_t *directions, unsigned length)
{
    if (length == 0U) return true;
    unsigned previous = 0U;
    unsigned current = 1U;
    for (unsigned i = 1U; i < length; ++i) {
        if (directions[i] == directions[i - 1U]) {
            ++current;
        } else {
            if (previous == current) return false;
            previous = current;
            current = 1U;
        }
    }
    return previous != current;
}

static void brute_paths(const Grid *grid,
                        uint64_t visited[VISITED_WORDS],
                        uint8_t directions[MAX_VERTICES],
                        unsigned vertex, unsigned depth,
                        U128 *total, U128 *valid)
{
    if (vertex == grid->goal) {
        if (!increment_u128(total)) die("self-test total overflow");
        if (complete_word_is_valid(directions, depth) &&
            !increment_u128(valid)) die("self-test count overflow");
        return;
    }
    for (unsigned direction = 0U; direction < DIRECTION_COUNT; ++direction) {
        const int next = grid->neighbor[vertex][direction];
        if (next < 0 || bit_is_set(visited, (unsigned)next)) continue;
        const unsigned candidate = (unsigned)next;
        directions[depth] = (uint8_t)direction;
        set_bit(visited, candidate);
        brute_paths(grid, visited, directions, candidate, depth + 1U,
                    total, valid);
        clear_bit(visited, candidate);
    }
}

static U128 count_bruteforce(unsigned n, U128 *total)
{
    Grid grid;
    initialize_grid(&grid, n, 0U);
    uint64_t visited[VISITED_WORDS] = {0U};
    uint8_t directions[MAX_VERTICES];
    const unsigned start = vertex_of(&grid, 0U, 0U);
    set_bit(visited, start);
    *total = 0U;
    U128 valid = 0U;
    brute_paths(&grid, visited, directions, start, 0U, total, &valid);
    return valid;
}

static void run_self_test(void)
{
    for (unsigned n = 0U; n <= SELF_TEST_MAX_N; ++n) {
        U128 total;
        const U128 direct = count_bruteforce(n, &total);
        const U128 memoized = count_memoized(n, 1U, 8U, 1U, 32U, false);
        const U128 uncached = count_memoized(n, 1U, 8U, 1U, 0U, false);
        if (direct != memoized || direct != uncached) {
            fprintf(stderr, "self-test n=%u mismatch\n", n);
            exit(EXIT_FAILURE);
        }
        if (n < sizeof(known_prefix) / sizeof(known_prefix[0]) &&
            direct != (U128)known_prefix[n]) {
            fprintf(stderr, "self-test n=%u known-value mismatch\n", n);
            exit(EXIT_FAILURE);
        }
        fprintf(stderr, "self-test n=%u: ", n);
        print_u128(stderr, total);
        fputs(" simple paths, ", stderr);
        print_u128(stderr, direct);
        fputs(" valid\n", stderr);
    }
}

static void usage(FILE *stream, const char *program)
{
    fprintf(stream,
            "Usage: %s [OPTIONS] MAX_N\n"
            "       %s --self-test\n\n"
            "Options:\n"
            "  --start N                  first index (default: 0)\n"
            "  --threads N                worker threads (default: online CPUs)\n"
            "  --cache-mib N              total cache request; 0 disables\n"
            "                              (default: %u MiB)\n"
            "  --split-depth N            prefix depth 1..%u (default: %u)\n"
            "  --connectivity-interval N  flood-fill every N steps; 0 disables\n"
            "                              (default: %u)\n"
            "  --quiet                    suppress progress on stderr\n"
            "  --self-test                exhaustive test through n=%u\n"
            "  -h, --help                 show this help\n",
            program, program, DEFAULT_CACHE_MIB, MAX_SPLIT_DEPTH,
            DEFAULT_SPLIT_DEPTH, DEFAULT_CONNECTIVITY_INTERVAL,
            SELF_TEST_MAX_N);
}

static Options parse_options(int argc, char **argv)
{
    Options options = {
        .start = 0U,
        .maximum = 0U,
        .threads = default_thread_count(),
        .split_depth = DEFAULT_SPLIT_DEPTH,
        .connectivity_interval = DEFAULT_CONNECTIVITY_INTERVAL,
        .cache_mib = DEFAULT_CACHE_MIB,
        .quiet = false,
        .self_test = false,
        .have_maximum = false
    };
    for (int i = 1; i < argc; ++i) {
        const char *argument = argv[i];
        if (strcmp(argument, "-h") == 0 ||
            strcmp(argument, "--help") == 0) {
            usage(stdout, argv[0]);
            exit(EXIT_SUCCESS);
        }
        if (strcmp(argument, "--quiet") == 0) {
            options.quiet = true;
            continue;
        }
        if (strcmp(argument, "--self-test") == 0) {
            options.self_test = true;
            continue;
        }
        if (strcmp(argument, "--start") == 0 ||
            strcmp(argument, "--threads") == 0 ||
            strcmp(argument, "--cache-mib") == 0 ||
            strcmp(argument, "--split-depth") == 0 ||
            strcmp(argument, "--connectivity-interval") == 0) {
            if (++i >= argc) {
                fprintf(stderr, "error: %s needs an argument\n", argument);
                exit(EXIT_FAILURE);
            }
            if (strcmp(argument, "--start") == 0) {
                options.start = parse_unsigned(argv[i], MAX_N, "start");
            } else if (strcmp(argument, "--threads") == 0) {
                options.threads =
                    parse_unsigned(argv[i], MAX_THREADS, "thread count");
                if (options.threads == 0U) die("thread count must be positive");
            } else if (strcmp(argument, "--cache-mib") == 0) {
                options.cache_mib =
                    parse_unsigned(argv[i], MAX_CACHE_MIB, "cache MiB");
            } else if (strcmp(argument, "--split-depth") == 0) {
                options.split_depth = parse_unsigned(
                    argv[i], MAX_SPLIT_DEPTH, "split depth");
                if (options.split_depth == 0U)
                    die("split depth must be positive");
            } else {
                options.connectivity_interval = parse_unsigned(
                    argv[i], MAX_VERTICES - 1U, "connectivity interval");
            }
            continue;
        }
        if (argument[0] == '-') {
            fprintf(stderr, "error: unknown option: %s\n", argument);
            exit(EXIT_FAILURE);
        }
        if (options.have_maximum) die("only one MAX_N may be specified");
        options.maximum = parse_unsigned(argument, MAX_N, "MAX_N");
        options.have_maximum = true;
    }
    return options;
}

int main(int argc, char **argv)
{
    const Options options = parse_options(argc, argv);
    if (options.self_test) {
        if (options.have_maximum) die("--self-test does not take MAX_N");
        run_self_test();
        return EXIT_SUCCESS;
    }
    if (!options.have_maximum) {
        usage(stderr, argv[0]);
        return EXIT_FAILURE;
    }
    if (options.start > options.maximum)
        die("--start must not exceed MAX_N");

    for (unsigned n = options.start; n <= options.maximum; ++n) {
        const double started = monotonic_seconds();
        const U128 value = count_memoized(
            n, options.threads, options.split_depth,
            options.connectivity_interval, options.cache_mib, !options.quiet);
        if (printf("%u ", n) < 0 || print_u128(stdout, value) != 0 ||
            fputc('\n', stdout) == EOF || fflush(stdout) != 0)
            die("writing stdout failed");
        if (!options.quiet) {
            fprintf(stderr, "n=%u: completed in %.3f s\n",
                    n, monotonic_seconds() - started);
            fflush(stderr);
        }
    }
    return EXIT_SUCCESS;
}
