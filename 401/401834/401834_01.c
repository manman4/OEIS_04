/* A401834 / Erdos Problem 796, g_3(n).
   Usage: 401834_01 n, with 1 <= n <= 200.
   Print only proved terms, separated by commas, flushing each term.

   Three distinct equal-product pairs have six distinct endpoints: if two
   pairs shared a positive factor, cancellation would make the pairs equal.
   A valid subset therefore omits a vertex from each forbidden six-set.
   This program solves that minimum hitting-set problem exactly.

   On adjoining n, the minimum number of omissions either stays unchanged
   or increases by one. Test the old optimum budget by exhaustive branching;
   if infeasible, adjoining n to the old deletion set proves the new optimum.
   Branch dominance uses inclusion of covered constraints. A packing of
   vertex-disjoint constraints gives a lower bound. The bounded cache stores
   only exhaustive infeasibility results, checked by full state equality.

   All arithmetic is bounded by MAX_N=200 and EDGE_LIMIT=200000. At most
   19900 pairs are stored, products are <=40000, bit shifts are 0..63, and
   edge counts and coverage counts are <=200000. Allocation sizes are checked.
   Only completed results reach stdout. No result or checkpoint files are used.
*/
#include <errno.h>
#include <limits.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { MAX_N = 200, VWORDS = (MAX_N + 63) / 64,
       MAX_PAIRS = MAX_N * (MAX_N - 1) / 2,
       MAX_PRODUCT = MAX_N * MAX_N, EDGE_LIMIT = 200000 };

static volatile sig_atomic_t interrupted;
static int printed;

typedef struct { uint64_t word[VWORDS]; } Deleted;
typedef struct { int a, b, next; } Pair;
typedef struct { unsigned short vertex[6]; } Edge;
typedef struct {
    Pair pair[MAX_PAIRS];
    int head[MAX_PRODUCT + 1], pair_count;
    Edge *edge;
    size_t edge_count, capacity;
} Model;
typedef struct { uint64_t hash; int budget, used; } CacheEntry;
typedef struct {
    const Model *model;
    size_t words, slots;
    uint64_t *incident, *states, *packing, *keys;
    CacheEntry *cache;
    Deleted answer;
} Solver;
typedef struct { int vertex, coverage; } Choice;

static void on_interrupt(int signal_number)
{
    (void)signal_number;
    interrupted = 1;
}

static void stop(const char *message, int status)
{
    if (printed) {
        (void)putchar('\n');
        (void)fflush(stdout);
    }
    fprintf(stderr, "%s\n", message);
    exit(status);
}

static void check_interrupt(void)
{
    if (interrupted)
        stop("Interrupted; only completed terms were printed.", 130);
}

static void *allocate(size_t count, size_t size)
{
    if (!size || count > SIZE_MAX / size)
        stop("Allocation size exceeds supported range.", 1);
    void *result = calloc(count, size);
    if (!result)
        stop("Not enough memory.", 1);
    return result;
}

static int member(Deleted set, int vertex)
{
    return (set.word[vertex / 64] & (UINT64_C(1) << (vertex % 64))) != 0;
}

static void mark(Deleted *set, int vertex, int present)
{
    uint64_t bit = UINT64_C(1) << (vertex % 64);
    if (present) set->word[vertex / 64] |= bit;
    else set->word[vertex / 64] &= ~bit;
}

static int deletion_count(Deleted set)
{
    int count = 0;
    for (int w = 0; w < VWORDS; ++w)
        count += __builtin_popcountll(set.word[w]);
    return count;
}

static void append_edge(Model *model, int a, int b, Pair first, Pair second)
{
    if (model->edge_count == EDGE_LIMIT)
        stop("Constraint resource limit reached; current term is incomplete.", 1);
    if (model->edge_count == model->capacity) {
        size_t capacity = model->capacity ? 2 * model->capacity : 256;
        if (capacity > EDGE_LIMIT) capacity = EDGE_LIMIT;
        if (capacity > SIZE_MAX / sizeof *model->edge)
            stop("Constraint allocation is too large.", 1);
        Edge *next = realloc(model->edge, capacity * sizeof *next);
        if (!next) stop("Not enough memory for constraints.", 1);
        model->edge = next;
        model->capacity = capacity;
    }
    int vertices[6] = {a, b, first.a, first.b, second.a, second.b};
    for (int i = 1; i < 6; ++i) {
        int value = vertices[i], j = i;
        while (j > 0 && vertices[j - 1] > value) {
            vertices[j] = vertices[j - 1];
            --j;
        }
        vertices[j] = value;
    }
    Edge *edge = &model->edge[model->edge_count++];
    for (int i = 0; i < 6; ++i) {
        if (vertices[i] < 0 || vertices[i] >= MAX_N ||
            (i && vertices[i] == vertices[i - 1]))
            stop("Invalid equal-product constraint.", 1);
        edge->vertex[i] = (unsigned short)vertices[i];
    }
}

static void extend_model(Model *model, int n)
{
    for (int a = 1; a < n; ++a) {
        check_interrupt();
        int product = a * n;
        for (int i = model->head[product]; i >= 0; i = model->pair[i].next)
            for (int j = model->pair[i].next; j >= 0; j = model->pair[j].next)
                append_edge(model, a - 1, n - 1, model->pair[i], model->pair[j]);
        if (model->pair_count >= MAX_PAIRS)
            stop("Pair resource limit exceeded.", 1);
        int index = model->pair_count++;
        model->pair[index] = (Pair){a - 1, n - 1, model->head[product]};
        model->head[product] = index;
    }
}

static int hits_all(const Model *model, Deleted set)
{
    for (size_t i = 0; i < model->edge_count; ++i) {
        int hit = 0;
        for (int j = 0; j < 6; ++j)
            hit |= member(set, model->edge[i].vertex[j]);
        if (!hit) return 0;
    }
    return 1;
}

/* XOR and masked rotation avoid overflowing arithmetic in the hash.
   A hash match alone is never treated as a cache hit. */
static uint64_t state_hash(const uint64_t *active, size_t words, int budget)
{
    uint64_t hash = UINT64_C(0x9e3779b97f4a7c15) ^ (uint64_t)budget;
    for (size_t w = 0; w < words; ++w) {
        hash ^= active[w];
        hash = ((hash & (UINT64_MAX >> 7)) << 7) | (hash >> 57);
        hash ^= hash >> 29;
    }
    return hash;
}

static int covered_by(const Solver *solver, const uint64_t *active, int vertex)
{
    int count = 0;
    const uint64_t *incident = solver->incident + (size_t)vertex * solver->words;
    for (size_t w = 0; w < solver->words; ++w)
        count += __builtin_popcountll(active[w] & incident[w]);
    return count;
}

static int dominated(const Solver *solver, const uint64_t *active, int a, int b)
{
    const uint64_t *first = solver->incident + (size_t)a * solver->words;
    const uint64_t *second = solver->incident + (size_t)b * solver->words;
    for (size_t w = 0; w < solver->words; ++w)
        if (active[w] & first[w] & ~second[w]) return 0;
    return 1;
}

static size_t first_edge(const uint64_t *active, size_t words)
{
    for (size_t w = 0; w < words; ++w)
        if (active[w]) return 64 * w + (size_t)__builtin_ctzll(active[w]);
    return SIZE_MAX;
}

static int cover(Solver *solver, const uint64_t *active, int budget, int depth)
{
    check_interrupt();
    size_t first = first_edge(active, solver->words);
    if (first == SIZE_MAX) return 1;
    if (!budget) return 0;
    uint64_t hash = state_hash(active, solver->words, budget);
    size_t slot = (size_t)(hash & (uint64_t)(solver->slots - 1));
    CacheEntry *entry = &solver->cache[slot];
    uint64_t *key = solver->keys + slot * solver->words;
    if (entry->used && entry->budget == budget && entry->hash == hash &&
        memcmp(key, active, solver->words * sizeof *active) == 0)
        return 0;

    int total = 0;
    for (size_t w = 0; w < solver->words; ++w)
        total += __builtin_popcountll(active[w]);
    Choice choices[6], kept[6];
    int kept_count = 0;
    for (int i = 0; i < 6; ++i) {
        int vertex = solver->model->edge[first].vertex[i];
        choices[i] = (Choice){vertex, covered_by(solver, active, vertex)};
    }
    for (int i = 1; i < 6; ++i) {
        Choice value = choices[i];
        int j = i;
        while (j > 0 && (choices[j - 1].coverage < value.coverage ||
               (choices[j - 1].coverage == value.coverage && choices[j - 1].vertex > value.vertex))) {
            choices[j] = choices[j - 1];
            --j;
        }
        choices[j] = value;
    }
    for (int i = 0; i < 6; ++i) {
        if (choices[i].coverage == total) {
            mark(&solver->answer, choices[i].vertex, 1);
            return 1;
        }
        int redundant = 0;
        for (int j = 0; j < kept_count; ++j)
            if (dominated(solver, active, choices[i].vertex, kept[j].vertex)) {
                redundant = 1;
                break;
            }
        if (!redundant) kept[kept_count++] = choices[i];
    }
    if (budget > 1) {
        uint64_t *packing = solver->packing + (size_t)depth * solver->words;
        memcpy(packing, active, solver->words * sizeof *packing);
        int packed = 0;
        for (;;) {
            size_t index = first_edge(packing, solver->words);
            if (index == SIZE_MAX) break;
            if (++packed > budget) goto infeasible;
            const Edge *edge = &solver->model->edge[index];
            for (size_t w = 0; w < solver->words; ++w) {
                uint64_t touching = 0;
                for (int i = 0; i < 6; ++i)
                    touching |= solver->incident[(size_t)edge->vertex[i] * solver->words + w];
                packing[w] &= ~touching;
            }
        }
        uint64_t *next = solver->states + (size_t)(depth + 1) * solver->words;
        for (int i = 0; i < kept_count; ++i) {
            int vertex = kept[i].vertex;
            const uint64_t *incident = solver->incident + (size_t)vertex * solver->words;
            for (size_t w = 0; w < solver->words; ++w)
                next[w] = active[w] & ~incident[w];
            mark(&solver->answer, vertex, 1);
            if (cover(solver, next, budget - 1, depth + 1)) return 1;
            mark(&solver->answer, vertex, 0);
        }
    }

infeasible:
    entry->hash = hash;
    entry->budget = budget;
    entry->used = 1;
    memcpy(key, active, solver->words * sizeof *active);
    return 0;
}

static Deleted optimum(const Model *model, int n, Deleted previous)
{
    if (hits_all(model, previous)) return previous;
    Solver solver = {.model = model, .words = (model->edge_count + 63) / 64};
    solver.incident = allocate((size_t)n * solver.words, sizeof *solver.incident);
    solver.states = allocate((size_t)(n + 1) * solver.words, sizeof *solver.states);
    solver.packing = allocate((size_t)(n + 1) * solver.words, sizeof *solver.packing);
    size_t entry_bytes = sizeof(CacheEntry) + solver.words * sizeof(uint64_t);
    size_t maximum = ((size_t)16 * 1024 * 1024) / entry_bytes;
    solver.slots = 1;
    while (solver.slots < 32768 && solver.slots <= maximum / 2)
        solver.slots *= 2;
    solver.cache = allocate(solver.slots, sizeof *solver.cache);
    solver.keys = allocate(solver.slots * solver.words, sizeof *solver.keys);
    for (size_t i = 0; i < model->edge_count; ++i)
        for (int j = 0; j < 6; ++j) {
            int vertex = model->edge[i].vertex[j];
            solver.incident[(size_t)vertex * solver.words + i / 64] |= UINT64_C(1) << (i % 64);
        }
    for (size_t w = 0; w < solver.words; ++w) solver.states[w] = UINT64_MAX;
    if (model->edge_count % 64)
        solver.states[solver.words - 1] = UINT64_MAX >> (64 - model->edge_count % 64);
    int old_count = deletion_count(previous);
    int found = cover(&solver, solver.states, old_count, 0);
    Deleted result = solver.answer;
    if (!found) {
        result = previous;
        mark(&result, n - 1, 1);
    }
    free(solver.keys);
    free(solver.cache);
    free(solver.packing);
    free(solver.states);
    free(solver.incident);
    if ((deletion_count(result) != old_count && deletion_count(result) != old_count + 1) ||
        !hits_all(model, result))
        stop("Invalid minimum-deletion witness.", 1);
    return result;
}

static int verify(int n, Deleted deleted)
{
    unsigned char counts[MAX_PRODUCT + 1] = {0};
    int selected = 0;
    for (int a = 1; a <= n; ++a) {
        if (member(deleted, a - 1)) continue;
        ++selected;
        for (int b = a + 1; b <= n; ++b)
            if (!member(deleted, b - 1) && ++counts[a * b] > 2)
                stop("Invalid product multiplicity in the witness.", 1);
    }
    return selected;
}

int main(int argc, char **argv)
{
    if (argc != 2 || argv[1][0] < '0' || argv[1][0] > '9')
        stop("Usage: 401834_01 n (1 <= n <= 200)", 1);
    errno = 0;
    char *end;
    long limit = strtol(argv[1], &end, 10);
    if (errno || *end || limit < 1 || limit > MAX_N)
        stop("n must be an integer from 1 to 200.", 1);
    if (signal(SIGINT, on_interrupt) == SIG_ERR)
        stop("Could not install the interrupt handler.", 1);
    Model *model = allocate(1, sizeof *model);
    for (int i = 0; i <= MAX_PRODUCT; ++i) model->head[i] = -1;
    Deleted previous = {{0}};
    for (int n = 1; n <= limit; ++n) {
        extend_model(model, n);
        previous = optimum(model, n, previous);
        int value = verify(n, previous);
        check_interrupt();
        if ((printed && printf(", ") < 0) || printf("%d", value) < 0 || fflush(stdout) != 0)
            stop("Could not write standard output.", 1);
        printed = 1;
    }
    free(model->edge);
    free(model);
    if (putchar('\n') == EOF || fflush(stdout) != 0)
        stop("Could not finish standard output.", 1);
    return 0;
}
