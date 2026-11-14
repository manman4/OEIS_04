/*
 * A401117: Count tilings of an n x n square by isosceles right triangles
 * with lattice vertices and sides parallel to board sides or diagonals.
 *
 * Build in the source directory (GMP and POSIX file APIs required):
 *   /usr/bin/clang -O3 -std=c17 -Wall -Wextra -Wpedantic 401117_01.c \
 *     $(pkg-config --cflags --libs gmp) -o 401117_01
 *   ./401117_01 9
 *   ./401117_01 --no-bfile 9
 *
 * A tile has either axis-parallel legs of positive integer length or an
 * axis-parallel hypotenuse. In the latter case the apex is an offset of
 * half the hypotenuse length in both coordinates from an endpoint, so the
 * length must be even. These rules generate each tile placement once.
 * Every side follows the edges of the four atoms per unit square drawn
 * by its diagonals. A diagonal through a square is a whole diagonal
 * segment there. Two different diagonals cannot be tile boundaries in
 * the same square: they would cross at the center, which is not a lattice
 * vertex. Thus a square is covered by one whole tile or two half tiles.
 *
 * Visit squares in row order. The state records covered but unprocessed
 * atoms. To finish a square, place its remaining tile(s), starting with
 * the one covering the first available atom. A tile can only be placed
 * at its first square, so this order is unique for each tiling.
 * Equal coverage states give identical future choices and are summed.
 *
 * The layered algorithm runs through n=9 with a bounded state table and
 * checked 256-bit counts. The bounded-cache depth-first algorithm
 * uses GMP for its counters. Eviction only causes exact recomputation.
 * The b-file stores the contiguous completed prefix. Save one full term
 * at a time under flock using a synced temporary file and atomic rename.
 */
#define _POSIX_C_SOURCE 200809L
#define _DARWIN_C_SOURCE

#include <errno.h>
#include <fcntl.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>
#include <gmp.h>

enum {
    MAX_N = 12,
    LAYER_MAX_N = 9,
    LAYER_WORDS = (4 * LAYER_MAX_N * LAYER_MAX_N + 63) / 64,
    CHUNK_BITS = 15,
    CHUNK_SIZE = 1 << CHUNK_BITS,
    MAX_CHUNKS = 2048,
    MAX_ATOMS = 4 * MAX_N * MAX_N,
    WORDS = (MAX_ATOMS + 63) / 64,
    COUNT_WORDS = 4,
    /* At most 8*(n+1)^2*n placements before rejecting outside vertices. */
    MAX_TILES = 8 * (MAX_N + 1) * (MAX_N + 1) * MAX_N,
};
static const size_t memory_limit = (size_t)4608 << 20;
static size_t allocated;
static const char bfile_path[] = "b401117.txt";
static const char lock_path[] = "b401117.txt.lock";

_Static_assert(SIZE_MAX >= UINT64_MAX, "64-bit target required");

_Noreturn static void fail(const char *message)
{
    fprintf(stderr, "401117_01: %s\n", message);
    exit(EXIT_FAILURE);
}

_Noreturn static void fail_io(const char *operation)
{
    perror(operation);
    exit(EXIT_FAILURE);
}

static void *allocate(size_t count, size_t size)
{
    if (count > (memory_limit - allocated) / size)
        fail("state tables exceeded the 4608 MiB memory limit");
    const size_t bytes = count * size;
    void *buffer = malloc(bytes);
    if (buffer == NULL) fail("could not allocate a state table");
    allocated += bytes;
    return buffer;
}

static void release(void *buffer, size_t count, size_t size)
{
    free(buffer);
    allocated -= count * size;
}

typedef struct { uint64_t word[WORDS]; } Mask;
typedef struct { uint64_t word[COUNT_WORDS]; } Count;
typedef struct { uint64_t mask[LAYER_WORDS]; Count count; } Entry;

typedef struct {
    Entry *chunks[MAX_CHUNKS];
    uint32_t *index;
    size_t size, chunks_used, index_capacity;
} Layer;

static uint64_t hash_mask(const uint64_t *mask, int words)
{
    uint64_t hash = UINT64_C(0x9e3779b97f4a7c15);
    for (int i = 0; i < words; ++i) {
        uint64_t next;
        /* The hash uses multiplication and addition modulo 2^64. */
        (void)__builtin_mul_overflow(hash, UINT64_C(0x9e3779b185ebca87), &next);
        (void)__builtin_add_overflow(next, mask[i], &hash);
        hash ^= hash >> 31;
    }
    (void)__builtin_mul_overflow(hash ^ (hash >> 30),
                                 UINT64_C(0xbf58476d1ce4e5b9), &hash);
    return hash ^ (hash >> 27);
}

static bool equal_masks(const uint64_t *a, const uint64_t *b, int words)
{
    for (int i = 0; i < words; ++i)
        if (a[i] != b[i]) return false;
    return true;
}

static Entry *layer_entry(const Layer *layer, size_t i)
{
    return &layer->chunks[i >> CHUNK_BITS][i & (CHUNK_SIZE - 1)];
}

static size_t find_slot(const Layer *layer, const uint64_t *mask, int words)
{
    const size_t wrap = layer->index_capacity - 1;
    size_t slot = (size_t)hash_mask(mask, words) & wrap;
    while (layer->index[slot] != 0 &&
           !equal_masks(layer_entry(layer, layer->index[slot] - 1)->mask,
                        mask, words))
        slot = (slot + 1) & wrap;
    return slot;
}

static void grow_index(Layer *layer, int words)
{
    const size_t capacity = layer->index_capacity == 0 ? 16 : 2 * layer->index_capacity;
    /* The old index is rebuilt from the entries and can be freed first. */
    release(layer->index, layer->index_capacity, sizeof(*layer->index));
    layer->index = allocate(capacity, sizeof(*layer->index));
    layer->index_capacity = capacity;
    memset(layer->index, 0, capacity * sizeof(*layer->index));
    for (size_t i = 0; i < layer->size; ++i)
        layer->index[find_slot(layer, layer_entry(layer, i)->mask, words)] =
            (uint32_t)(i + 1);
}

static void add_count(Count *count, const Count *value)
{
    bool carry = false;
    for (int i = 0; i < COUNT_WORDS; ++i) {
        uint64_t sum;
        const bool first = __builtin_add_overflow(count->word[i], value->word[i], &sum);
        const bool second = __builtin_add_overflow(sum, (uint64_t)carry, &count->word[i]);
        carry = first || second;
    }
    if (carry) fail("256-bit count capacity exceeded");
}

static void add_state(Layer *layer, const Mask *mask, const Count *count, int words)
{
    if (layer->index_capacity == 0) grow_index(layer, words);
    size_t slot = find_slot(layer, mask->word, words);
    if (layer->index[slot] != 0) {
        add_count(&layer_entry(layer, layer->index[slot] - 1)->count, count);
        return;
    }
    if (layer->size >= layer->index_capacity - layer->index_capacity / 4) {
        grow_index(layer, words);
        slot = find_slot(layer, mask->word, words);
    }
    /* The memory budget bounds the entry count well below UINT32_MAX. */
    if (layer->size / CHUNK_SIZE == layer->chunks_used) {
        if (layer->chunks_used == MAX_CHUNKS) fail("too many states in one layer");
        layer->chunks[layer->chunks_used++] = allocate(CHUNK_SIZE, sizeof(Entry));
    }
    Entry *entry = layer_entry(layer, layer->size++);
    memcpy(entry->mask, mask->word, (size_t)words * sizeof(*entry->mask));
    entry->count = *count;
    layer->index[slot] = (uint32_t)layer->size;
}

static void clear_layer(Layer *layer)
{
    layer->size = 0;
    if (layer->index != NULL)
        memset(layer->index, 0, layer->index_capacity * sizeof(*layer->index));
}

static void free_layer(Layer *layer)
{
    for (size_t i = 0; i < layer->chunks_used; ++i)
        release(layer->chunks[i], CHUNK_SIZE, sizeof(Entry));
    release(layer->index, layer->index_capacity, sizeof(*layer->index));
}

typedef struct { int x, y; } Point;
typedef struct {
    Mask mask;
    int next;
} Tile;
typedef struct {
    Point centroid[MAX_ATOMS];
    Tile tiles[MAX_TILES];
    int first[MAX_ATOMS];
    int length, used, side;
} Board;

static int cross(Point a, Point b, Point p)
{
    return (b.x - a.x) * (p.y - a.y) - (b.y - a.y) * (p.x - a.x);
}

static bool in_board(Point p, int side)
{
    return p.x >= 0 && p.x <= side && p.y >= 0 && p.y <= side;
}

static void add_tile(Board *board, Point a, Point b, Point c)
{
    if (!in_board(a, board->side) || !in_board(b, board->side)
        || !in_board(c, board->side)) return;
    int area = cross(a, b, c);
    if (area < 0) {
        const Point swap = b;
        b = c;
        c = swap;
        area = -area;
    }
    if (area == 0 || area % 2 != 0) fail("invalid tile area");
    /* Coordinates for the centroid tests have scale six. */
    a = (Point){3 * a.x, 3 * a.y};
    b = (Point){3 * b.x, 3 * b.y};
    c = (Point){3 * c.x, 3 * c.y};
    Mask mask = {0};
    int first = -1, count = 0;
    for (int i = 0; i < board->length; ++i) {
        const Point p = board->centroid[i];
        if (cross(a, b, p) > 0 && cross(b, c, p) > 0 && cross(c, a, p) > 0) {
            if (first < 0) first = i;
            mask.word[i / 64] |= UINT64_C(1) << (i % 64);
            ++count;
        }
    }
    if (count != area / 2 || first < 0 || board->used >= MAX_TILES)
        fail("tile does not cover the expected elementary triangles");
    board->tiles[board->used] = (Tile){mask, board->first[first]};
    board->first[first] = board->used++;
}

static void make_board(Board *board, int n)
{
    board->side = 2 * n;
    const Point offsets[] = {{3, 1}, {1, 3}, {5, 3}, {3, 5}};
    for (int y = 0; y < n; ++y)
        for (int x = 0; x < n; ++x)
            for (int i = 0; i < 4; ++i) {
                board->first[board->length] = -1;
                board->centroid[board->length++] =
                    (Point){6 * x + offsets[i].x, 6 * y + offsets[i].y};
            }
    for (int y = 0; y <= board->side; y += 2) {
        for (int x = 0; x <= board->side; x += 2) {
            const Point p = {x, y};
            for (int k = 2; k <= board->side; k += 2) {
                for (int dx = -1; dx <= 1; dx += 2)
                    for (int dy = -1; dy <= 1; dy += 2)
                        add_tile(board, p, (Point){x + dx * k, y}, (Point){x, y + dy * k});
                if (k % 4 != 0) continue;
                for (int d = -1; d <= 1; d += 2) {
                    add_tile(board, p, (Point){x + k, y}, (Point){x + k/2, y + d*k/2});
                    add_tile(board, p, (Point){x, y + k}, (Point){x + d*k/2, y + k/2});
                }
            }
        }
    }
}

static bool place_tile(Mask *result, const uint64_t *state, const Mask *tile, int words)
{
    for (int i = 0; i < words; ++i)
        if ((state[i] & tile->word[i]) != 0) return false;
    for (int i = 0; i < words; ++i)
        result->word[i] = state[i] | tile->word[i];
    return true;
}

/* Every tiling is determined by its subset of internal elementary edges.
 * There are 6n^2-2n such edges (count the 3 sides of each of 4n^2 atoms
 * and subtract the 4n boundary unit edges before dividing by two).
 * The b-file check uses this bound for either counting mode. */
static void count_bound(mpz_t bound, int n)
{
    const unsigned edges = (unsigned)(6 * n * n - 2 * n);
    mpz_set_ui(bound, 0);
    mpz_setbit(bound, edges);
}

static void compute_layered(mpz_t value, const Board *board, int n)
{
    const int words = (board->length + 63) / 64;
    const Mask empty = {0};
    const Count one = {{1}};
    Layer layers[2] = {{0}};
    Layer *current = &layers[0], *next = &layers[1];
    add_state(current, &empty, &one, words);
    size_t peak = 1;
    for (int i = 0; i < board->length; i += 4) {
        clear_layer(next);
        const int word = i / 64;
        const int shift = i % 64;
        const uint64_t square = UINT64_C(15) << shift;
        for (size_t j = 0; j < current->size; ++j) {
            const Entry *entry = layer_entry(current, j);
            const uint64_t bits = entry->mask[word] & square;
            if (bits == square) {
                Mask target;
                memcpy(target.word, entry->mask, (size_t)words * sizeof(*target.word));
                target.word[word] ^= square;
                add_state(next, &target, &entry->count, words);
                continue;
            }
            const int first = i + __builtin_ctzll((square ^ bits) >> shift);
            for (int tile = board->first[first]; tile >= 0; tile = board->tiles[tile].next) {
                Mask target = {0};
                if (!place_tile(&target, entry->mask, &board->tiles[tile].mask, words)) continue;
                const uint64_t missing = square & ~target.word[word];
                if (missing == 0) {
                    target.word[word] ^= square;
                    add_state(next, &target, &entry->count, words);
                    continue;
                }
                const int second = i + __builtin_ctzll(missing >> shift);
                for (int other = board->first[second]; other >= 0;
                     other = board->tiles[other].next) {
                    if ((board->tiles[other].mask.word[word] & square) != missing) continue;
                    Mask done = {0};
                    if (!place_tile(&done, target.word, &board->tiles[other].mask, words)) continue;
                    done.word[word] ^= square;
                    add_state(next, &done, &entry->count, words);
                }
            }
        }
        Layer *swap = current;
        current = next;
        next = swap;
        if (current->size > peak) peak = current->size;
        if (n >= 9 && (i + 4) % (4 * n) == 0)
            fprintf(stderr, "n=%d: row %d/%d, %zu states\n",
                    n, (i + 4) / (4 * n), n, current->size);
    }
    if (current->size != 1 || !equal_masks(empty.word, layer_entry(current, 0)->mask, words))
        fail("inconsistent final state");
    mpz_import(value, COUNT_WORDS, -1, sizeof(uint64_t), 0, 0,
               layer_entry(current, 0)->count.word);
    fprintf(stderr, "n=%d: %d tiles, peak %zu states\n", n, board->used, peak);
    free_layer(current);
    free_layer(next);
}

enum { CACHE_SLOTS = 1 << 22 };

typedef struct {
    Mask mask;
    Count count;
    bool valid;
} CacheEntry;

static void count_suffix(mpz_t result, const Board *board, CacheEntry *cache,
                         const Mask *covered, int first, int words)
{
    while (first < board->length &&
           (covered->word[first / 64] & (UINT64_C(1) << (first % 64))) != 0)
        ++first;
    if (first == board->length) {
        mpz_set_ui(result, 1);
        return;
    }

    const size_t slot = (size_t)hash_mask(covered->word, words) & (CACHE_SLOTS - 1);
    CacheEntry *entry = &cache[slot];
    if (entry->valid && equal_masks(entry->mask.word, covered->word, words)) {
        mpz_import(result, COUNT_WORDS, -1, sizeof(uint64_t), 0, 0, entry->count.word);
        return;
    }

    mpz_t subtotal;
    mpz_init(subtotal);
    mpz_set_ui(result, 0);
    for (int t = board->first[first]; t >= 0; t = board->tiles[t].next) {
        Mask target = {0};
        if (place_tile(&target, covered->word, &board->tiles[t].mask, words)) {
            count_suffix(subtotal, board, cache, &target, first + 1, words);
            mpz_add(result, result, subtotal);
        }
    }
    mpz_clear(subtotal);
    if (mpz_sizeinbase(result, 2) <= 64 * COUNT_WORDS) {
        entry->mask = *covered;
        entry->count = (Count){0};
        mpz_export(entry->count.word, NULL, -1, sizeof(uint64_t), 0, 0, result);
        entry->valid = true;
    }
}

static void compute_term(mpz_t value, int n, bool low_memory)
{
    Board *board = calloc(1, sizeof(*board));
    if (board == NULL) fail("could not allocate board");
    make_board(board, n);
    if (!low_memory && n <= LAYER_MAX_N) {
        compute_layered(value, board, n);
    } else {
        CacheEntry *cache = calloc(CACHE_SLOTS, sizeof(*cache));
        if (cache == NULL) fail("could not allocate the bounded cache");
        fprintf(stderr, "n=%d: depth-first search with a cache of %.0f MiB\n", n,
                (double)(CACHE_SLOTS * sizeof(*cache)) / 1048576.0);
        const Mask empty = {0};
        count_suffix(value, board, cache, &empty, 0, (board->length + 63) / 64);
        free(cache);
    }
    free(board);
}

static int lock_output(void)
{
    const int fd = open(lock_path, O_RDWR | O_CREAT | O_NOFOLLOW | O_NONBLOCK | O_CLOEXEC, 0644);
    if (fd < 0) fail_io(lock_path);
    struct stat info;
    if (fstat(fd, &info) != 0) fail_io("stat b-file lock");
    if (!S_ISREG(info.st_mode) || info.st_nlink != 1)
        fail("b-file lock must be a regular file with one name");
    if (flock(fd, LOCK_EX | LOCK_NB) != 0) {
        if (errno == EWOULDBLOCK) fail("another process holds the b-file lock");
        fail_io("lock b-file");
    }
    return fd;
}

static FILE *open_saved(struct stat *snapshot)
{
    const int fd = open(bfile_path, O_RDONLY | O_NOFOLLOW | O_NONBLOCK | O_CLOEXEC);
    if (fd < 0) {
        if (errno == ENOENT) return NULL;
        fail_io(bfile_path);
    }
    if (fstat(fd, snapshot) != 0) fail_io("stat b-file");
    if (!S_ISREG(snapshot->st_mode) || snapshot->st_nlink != 1)
        fail("b-file must be a regular file with one name");
    FILE *input = fdopen(fd, "r");
    if (input == NULL) fail_io("open b-file stream");
    return input;
}

/* The existing prefix must contain contiguous indices starting at 1.
 * Preserve comments and whitespace by copying the original bytes on save. */
static int validate_saved(FILE *input)
{
    if (input == NULL) return 0;

    int n = 0;
    mpz_t value, bound;
    mpz_inits(value, bound, NULL);
    char line[1024];
    const char blanks[] = " \t\r\n";
    const char digits[] = "0123456789";
    while (fgets(line, sizeof(line), input) != NULL) {
        if (strchr(line, '\n') == NULL)
            fail("b-file contains an incomplete or oversized line");
        char *index = line + strspn(line, blanks);
        if (*index == '\0' || *index == '#') continue;
        char *sep = index + strspn(index, digits);
        if (sep == index || (*sep != ' ' && *sep != '\t'))
            fail("b-file contains a malformed index");
        *sep++ = '\0';
        char *end;
        errno = 0;
        const long saved_n = strtol(index, &end, 10);
        if (errno != 0 || *end != '\0' || saved_n != n + 1 || saved_n > MAX_N)
            fail("b-file indices are out of range or are not contiguous");
        char *number = sep + strspn(sep, blanks);
        end = number + strspn(number, digits);
        if (end == number || end[strspn(end, blanks)] != '\0')
            fail("b-file contains a malformed value");
        *end = '\0';
        if (mpz_set_str(value, number, 10) != 0 || mpz_sgn(value) <= 0)
            fail("b-file values must be positive integers");
        count_bound(bound, (int)saved_n);
        if (mpz_cmp(value, bound) > 0)
            fail("b-file value exceeds the proved count bound");
        n = (int)saved_n;
    }
    if (ferror(input)) fail_io("read b-file");
    mpz_clears(value, bound, NULL);
    return n;
}

static bool copy_saved(FILE *output, FILE *input)
{
    if (input == NULL) return true;
    if (fseek(input, 0, SEEK_SET) != 0) return false;
    char data[4096];
    size_t count;
    while ((count = fread(data, 1, sizeof(data), input)) != 0)
        if (fwrite(data, 1, count, output) != count) return false;
    return !ferror(input);
}

static bool saved_is_current(FILE *input, const struct stat *snapshot)
{
    struct stat current;
    if (lstat(bfile_path, &current) != 0)
        return input == NULL && errno == ENOENT;
    return input != NULL && S_ISREG(current.st_mode) && current.st_nlink == 1
           && current.st_mode == snapshot->st_mode
           && current.st_dev == snapshot->st_dev
           && current.st_ino == snapshot->st_ino
           && current.st_size == snapshot->st_size
           && current.st_mtime == snapshot->st_mtime
           && current.st_ctime == snapshot->st_ctime
#ifdef __APPLE__
           && current.st_mtimespec.tv_nsec == snapshot->st_mtimespec.tv_nsec
           && current.st_ctimespec.tv_nsec == snapshot->st_ctimespec.tv_nsec
#else
           && current.st_mtim.tv_nsec == snapshot->st_mtim.tv_nsec
           && current.st_ctim.tv_nsec == snapshot->st_ctim.tv_nsec
#endif
           ;
}

static FILE *save_term(FILE *input, struct stat *snapshot, int directory, int n,
                       const mpz_t value)
{
    if (!saved_is_current(input, snapshot))
        fail("b-file changed during computation");
    char temporary[] = "b401117.txt.tmp.XXXXXX";
    const int fd = mkstemp(temporary);
    if (fd < 0) fail_io("create b-file temporary");
    FILE *output = fdopen(fd, "w+");
    if (output == NULL) {
        const int error = errno;
        close(fd);
        unlink(temporary);
        errno = error;
        fail_io("open b-file temporary");
    }
    if ((input != NULL && fchmod(fd, snapshot->st_mode & 0777) != 0)
        || !copy_saved(output, input) || gmp_fprintf(output, "%d %Zd\n", n, value) < 0
        || fflush(output) != 0 || fsync(fd) != 0) {
        const int error = errno;
        fclose(output);
        unlink(temporary);
        errno = error;
        fail_io("save b-file");
    }
    if (!saved_is_current(input, snapshot)) {
        fclose(output);
        unlink(temporary);
        fail("b-file changed before saving");
    }
    if (rename(temporary, bfile_path) != 0) {
        const int error = errno;
        fclose(output);
        unlink(temporary);
        errno = error;
        fail_io("replace b-file");
    }
    if (fsync(directory) != 0) fail_io("sync b-file directory");
    if (fstat(fd, snapshot) != 0) fail_io("stat updated b-file");
    if (input != NULL && fclose(input) != 0) fail_io("close previous b-file");
    return output;
}

static void usage(FILE *stream, const char *program)
{
    fprintf(stream, "Usage: %s [--low-memory] [--no-bfile] N\n"
            "  1 <= N <= %d\n"
            "  N: extend ./b401117.txt through N and print newly computed terms.\n"
            "  --no-bfile N: compute and print only a(N), without opening the b-file.\n"
            "  --low-memory: use bounded-cache depth-first search (automatic for n >= 10).\n",
            program, MAX_N);
}

static int parse_n(const char *argument)
{
    errno = 0;
    char *end;
    const long n = strtol(argument, &end, 10);
    if (errno != 0 || end == argument || *end != '\0' || n < 1 || n > MAX_N)
        return 0;
    return (int)n;
}

int main(int argc, char **argv)
{
    if (argc == 2 && strcmp(argv[1], "--help") == 0) {
        usage(stdout, argv[0]);
        return EXIT_SUCCESS;
    }
    bool single = false, low_memory = false;
    int arg = 1;
    while (arg < argc - 1) {
        if (!single && strcmp(argv[arg], "--no-bfile") == 0) single = true;
        else if (!low_memory && strcmp(argv[arg], "--low-memory") == 0) low_memory = true;
        else break;
        ++arg;
    }
    const int n = arg == argc - 1 ? parse_n(argv[arg]) : 0;
    if (n == 0) {
        usage(stderr, argv[0]);
        return EXIT_FAILURE;
    }

    FILE *saved = NULL;
    struct stat snapshot;
    int lock = -1;
    int directory = -1;
    int first = n;
    if (!single) {
        lock = lock_output();
        saved = open_saved(&snapshot);
        first = validate_saved(saved) + 1;
        if (first > n)
            fprintf(stderr, "%s already contains terms through n=%d\n",
                    bfile_path, first - 1);
        else if ((directory = open(".", O_RDONLY)) < 0)
            fail_io("open b-file directory");
    }

    mpz_t value;
    mpz_init(value);
    for (int k = first; k <= n; ++k) {
        fprintf(stderr, "n=%d: computing\n", k);
        compute_term(value, k, low_memory);
        if (!single) saved = save_term(saved, &snapshot, directory, k, value);
        if (gmp_printf("%d %Zd\n", k, value) < 0 || fflush(stdout) != 0)
            fail_io("write result");
    }
    mpz_clear(value);
    if (saved != NULL && fclose(saved) != 0) fail_io("close b-file");
    if (directory >= 0 && close(directory) != 0) fail_io("close b-file directory");
    if (lock >= 0 && close(lock) != 0) fail_io("close b-file lock");
    return EXIT_SUCCESS;
}
