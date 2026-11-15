/*
 * A402198: Count tilings of the triangle (0,0), (n,0), (0,n) by
 * lattice-vertex isosceles right triangles with axis-parallel legs.
 * Placements that differ by reflection are counted separately.
 *
 * Build (GMP required):
 *   cc -O3 -std=c17 -Wall -Wextra -Wpedantic 402198_01.c \
 *      $(pkg-config --cflags --libs gmp) -o 402198_01
 *   ./402198_01 13
 *   ./402198_01 --low-memory --no-bfile 10
 *
 * The board has four elementary triangles in each interior unit square
 * and two in each boundary half-square. Enumerate tiles by right-angle
 * vertex, leg length, and the signs of the two axial legs. Tile edges lie
 * on the elementary grid, so classifying the centroids is exact.
 *
 * Sweep unit squares from the shortest row to the longest. Select a tile
 * when its first elementary triangle is reached. In a given tiling,
 * the first uncovered triangle determines the next tile. Identical masks have the
 * same continuations, so the layered dynamic program adds their counts.
 * Keys omit whole words occupied only by already processed squares.
 * The sweep starts with at most 128-bit counts and retries with the
 * proved bound if checked addition detects that more limbs are needed.
 * The memory-limited alternative is an exact depth-first search. Cache
 * collisions only cause recomputation. The depth is at most n*n.
 *
 * b402198.txt is the saved contiguous prefix. Resume checks its syntax
 * and count bounds and starts with the first missing term. Each term is
 * saved as a synced replacement under the stable b402198.txt.lock flock.
 * Any other cooperating writer must use that same lock.
 */
#define _POSIX_C_SOURCE 200809L
#define _DARWIN_C_SOURCE
#define _GNU_SOURCE

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
#if defined(__APPLE__)
#include <sys/acl.h>
#elif defined(__linux__)
#include <linux/fs.h>
#include <sys/syscall.h>
#include <sys/xattr.h>
#endif

enum {
    MAX_N = 16,
    CHUNK_BITS = 15,
    CHUNK_SIZE = 1 << CHUNK_BITS,
    MAX_CHUNKS = 2048,
    MAX_ATOMS = 2 * MAX_N * (MAX_N + 1),
    WORDS = (MAX_ATOMS + 63) / 64,
    COUNT_WORDS = ((9 * MAX_N * (MAX_N - 1) + 4) / 5 + 64) / 64,
    /* Per orientation and length k there are at most C(n-k+2,2)
     * translations. Summing over k gives C(n+2,3) per orientation. */
    MAX_TILES = 4 * MAX_N * (MAX_N + 1) * (MAX_N + 2) / 6,
    MAX_SAVED_BYTES = 1 << 20,
};
static size_t memory_limit = (size_t)1024 << 20;
static size_t allocated;
static const char bfile_path[] = "b402198.txt";
static const char lock_path[] = "b402198.txt.lock";

_Static_assert(SIZE_MAX >= UINT64_MAX, "64-bit target required");

_Noreturn static void fail(const char *message)
{
    fprintf(stderr, "402198_01: %s\n", message);
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
        fail("state tables exceeded the memory limit; try --memory-mib or --low-memory");
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

typedef struct {
    uint64_t *chunks[MAX_CHUNKS];
    uint32_t *index;
    size_t size, chunks_used, index_capacity;
    int words, count_words;
    bool overflow;
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

static uint64_t *layer_entry(const Layer *layer, size_t i)
{
    const size_t stride = (size_t)(layer->words + layer->count_words);
    return layer->chunks[i >> CHUNK_BITS] + (i & (CHUNK_SIZE - 1)) * stride;
}

static size_t find_slot(const Layer *layer, const uint64_t *mask)
{
    const size_t wrap = layer->index_capacity - 1;
    size_t slot = (size_t)hash_mask(mask, layer->words) & wrap;
    while (layer->index[slot] != 0 &&
           !equal_masks(layer_entry(layer, layer->index[slot] - 1),
                        mask, layer->words))
        slot = (slot + 1) & wrap;
    return slot;
}

static void grow_index(Layer *layer)
{
    const size_t capacity = layer->index_capacity == 0 ? 16 : 2 * layer->index_capacity;
    /* The old index is rebuilt from the entries and can be freed first. */
    release(layer->index, layer->index_capacity, sizeof(*layer->index));
    layer->index = allocate(capacity, sizeof(*layer->index));
    layer->index_capacity = capacity;
    memset(layer->index, 0, capacity * sizeof(*layer->index));
    for (size_t i = 0; i < layer->size; ++i)
        layer->index[find_slot(layer, layer_entry(layer, i))] =
            (uint32_t)(i + 1);
}

static bool add_count(uint64_t *count, const uint64_t *value, int count_words)
{
    bool carry = false;
    for (int i = 0; i < count_words; ++i) {
        uint64_t sum;
        const bool first = __builtin_add_overflow(count[i], value[i], &sum);
        const bool second = __builtin_add_overflow(sum, (uint64_t)carry, &count[i]);
        carry = first || second;
    }
    return !carry;
}

static void add_state(Layer *layer, const uint64_t *mask, const uint64_t *count)
{
    if (layer->index_capacity == 0) grow_index(layer);
    size_t slot = find_slot(layer, mask);
    if (layer->index[slot] != 0) {
        if (!add_count(layer_entry(layer, layer->index[slot] - 1) + layer->words,
                       count, layer->count_words))
            layer->overflow = true;
        return;
    }
    if (layer->size >= layer->index_capacity - layer->index_capacity / 4) {
        grow_index(layer);
        slot = find_slot(layer, mask);
    }
    /* At one word per entry or more, 8192 MiB holds at most 2^30 entries. */
    if (layer->size / CHUNK_SIZE == layer->chunks_used) {
        if (layer->chunks_used == MAX_CHUNKS) fail("too many states in one layer");
        layer->chunks[layer->chunks_used++] = allocate(CHUNK_SIZE, (size_t)(layer->words + layer->count_words) * sizeof(uint64_t));
    }
    uint64_t *entry = layer_entry(layer, layer->size++);
    memcpy(entry, mask, (size_t)layer->words * sizeof(*entry));
    memcpy(entry + layer->words, count, (size_t)layer->count_words * sizeof(*entry));
    layer->index[slot] = (uint32_t)layer->size;
}

static void free_layer(Layer *layer)
{
    const size_t stride = (size_t)(layer->words + layer->count_words);
    for (size_t i = 0; i < layer->chunks_used; ++i)
        release(layer->chunks[i], CHUNK_SIZE, stride * sizeof(uint64_t));
    release(layer->index, layer->index_capacity, sizeof(*layer->index));
}

static void clear_layer(Layer *layer, int words)
{
    layer->size = 0;
    layer->overflow = false;
    if (layer->words != words) {
        free_layer(layer);
        layer->words = words;
        layer->chunks_used = 0;
        layer->index = NULL;
        layer->index_capacity = 0;
    } else if (layer->index != NULL) {
        memset(layer->index, 0, layer->index_capacity * sizeof(*layer->index));
    }
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
    return p.x >= 0 && p.y >= 0 && p.x + p.y <= side;
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
        if (p.x >= 0 && cross(a, b, p) > 0 && cross(b, c, p) > 0 && cross(c, a, p) > 0) {
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
    for (int y = n - 1; y >= 0; --y)
        for (int x = 0; x < n - y; ++x)
            for (int i = 0; i < 4; ++i) {
                /* The last square in a row has only the first two atoms.
                 * Pad its group to four bits and skip the two absent atoms. */
                board->first[board->length] = -1;
                board->centroid[board->length++] =
                    (x + y == n - 1 && i >= 2)
                    ? (Point){-1, -1}
                    : (Point){6 * x + offsets[i].x, 6 * y + offsets[i].y};
            }
    for (int y = 0; y <= board->side; y += 2) {
        for (int x = 0; x <= board->side; x += 2) {
            const Point p = {x, y};
            for (int k = 2; k <= board->side; k += 2) {
                for (int dx = -1; dx <= 1; dx += 2)
                    for (int dy = -1; dy <= 1; dy += 2)
                        add_tile(board, p, (Point){x + dx * k, y}, (Point){x, y + dy * k});
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

/* The board contains I=n(n-1)/2 full unit squares and n boundary halves.
 * For a fixed covered set, record in each full unit square whether covered
 * pieces share a tile or are divided along either diagonal (at most 3
 * choices). The covered set already specifies which pieces are present.
 * Also record whether each of the 2I internal unit edges joins tiles.
 * Connected pieces recover the tiles. The same bound applies to partial
 * tilings of either a fixed covered set or its fixed complement.
 * Since 3^5 < 2^8, 3^I * 2^(2I) <= 2^bound_bits(n). */
static int bound_bits(int n)
{
    const int squares = n * (n - 1) / 2;
    return (18 * squares + 4) / 5;
}

static bool compute_layered(mpz_t value, const Board *board, int n, int count_words)
{
    const int words = (board->length + 63) / 64;
    const Mask empty = {0};
    const Count one = {{1}};
    Layer layers[2] = {{.words = words, .count_words = count_words},
                       {.words = words, .count_words = count_words}};
    Layer *current = &layers[0], *next = &layers[1];
    add_state(current, empty.word, one.word);
    size_t peak = 1;
    for (int i = 0; i < board->length; i += 4) {
        const int word = i / 64;
        const int next_word = (i + 4) / 64;
        clear_layer(next, words - next_word);
        const int shift = i % 64;
        const uint64_t square = (board->centroid[i + 3].x < 0 ? UINT64_C(3) : UINT64_C(15)) << shift;
        for (size_t j = 0; j < current->size && !next->overflow; ++j) {
            const uint64_t *entry = layer_entry(current, j);
            const uint64_t *count = entry + current->words;
            Mask covered = {0};
            memcpy(covered.word + word, entry, (size_t)current->words * sizeof(*entry));
            const uint64_t bits = covered.word[word] & square;
            if (bits == square) {
                covered.word[word] ^= square;
                add_state(next, covered.word + next_word, count);
                continue;
            }
            const int first = i + __builtin_ctzll((square ^ bits) >> shift);
            for (int tile = board->first[first]; tile >= 0; tile = board->tiles[tile].next) {
                Mask target = {0};
                if (!place_tile(&target, covered.word, &board->tiles[tile].mask, words)) continue;
                const uint64_t missing = square & ~target.word[word];
                if (missing == 0) {
                    target.word[word] ^= square;
                    add_state(next, target.word + next_word, count);
                    continue;
                }
                const int second = i + __builtin_ctzll(missing >> shift);
                for (int other = board->first[second]; other >= 0;
                     other = board->tiles[other].next) {
                    if ((board->tiles[other].mask.word[word] & square) != missing) continue;
                    Mask done = {0};
                    if (!place_tile(&done, target.word, &board->tiles[other].mask, words)) continue;
                    done.word[word] ^= square;
                    add_state(next, done.word + next_word, count);
                }
            }
        }
        if (next->overflow) {
            free_layer(current);
            free_layer(next);
            return false;
        }
        Layer *swap = current;
        current = next;
        next = swap;
        if (current->size > peak) peak = current->size;
        if (n >= 9 && board->centroid[i + 3].x < 0)
            fprintf(stderr, "n=%d: row %d/%d, %zu states\n",
                    n, n - board->centroid[i].y / 6, n, current->size);
    }
    if (current->size != 1 || !equal_masks(empty.word, layer_entry(current, 0), current->words))
        fail("inconsistent final state");
    mpz_import(value, (size_t)count_words, -1, sizeof(uint64_t), 0, 0,
               layer_entry(current, 0) + current->words);
    fprintf(stderr, "n=%d: %d tiles, peak %zu states\n", n, board->used, peak);
    free_layer(current);
    free_layer(next);
    return true;
}

enum { CACHE_SLOTS = 1 << 20 };

typedef struct {
    const Board *board;
    uint64_t *entries;
    int words, count_words;
} Search;

static void count_suffix(Count *result, const Search *search, const Mask *covered, int first)
{
    const Board *board = search->board;
    while (first < board->length &&
           (board->centroid[first].x < 0 ||
            (covered->word[first / 64] & (UINT64_C(1) << (first % 64))) != 0))
        ++first;
    *result = (Count){0};
    if (first == board->length) {
        result->word[0] = 1;
        return;
    }

    const int words = search->words, count_words = search->count_words;
    const uint64_t tag = (uint64_t)first + 1;
    const size_t slot = (size_t)hash_mask(covered->word, words) & (CACHE_SLOTS - 1);
    uint64_t *entry = search->entries + slot * (size_t)(1 + words + count_words);
    if (entry[0] == tag && equal_masks(entry + 1, covered->word, words)) {
        memcpy(result->word, entry + 1 + words, (size_t)count_words * sizeof(*entry));
        return;
    }

    for (int t = board->first[first]; t >= 0; t = board->tiles[t].next) {
        Mask target = {0};
        if (place_tile(&target, covered->word, &board->tiles[t].mask, words)) {
            Count subtotal;
            count_suffix(&subtotal, search, &target, first + 1);
            if (!add_count(result->word, subtotal.word, count_words))
                fail("count exceeds the proved bound");
        }
    }
    entry[0] = tag;
    memcpy(entry + 1, covered->word, (size_t)words * sizeof(*entry));
    memcpy(entry + 1 + words, result->word, (size_t)count_words * sizeof(*entry));
}

static void compute_term(mpz_t value, int n, bool low_memory)
{
    Board *board = calloc(1, sizeof(*board));
    if (board == NULL) fail("could not allocate board");
    make_board(board, n);
    if (!low_memory) {
        const int bound_words = bound_bits(n) / 64 + 1;
        const int initial_words = bound_words < 2 ? bound_words : 2;
        if (!compute_layered(value, board, n, initial_words)) {
            fprintf(stderr, "n=%d: retrying with %d count limbs\n", n, bound_words);
            if (!compute_layered(value, board, n, bound_words))
                fail("count exceeds the proved bound");
        }
    } else {
        Search search = {.board = board, .words = (board->length + 63) / 64,
                         .count_words = bound_bits(n) / 64 + 1};
        const size_t stride = (size_t)(1 + search.words + search.count_words);
        search.entries = calloc(CACHE_SLOTS, stride * sizeof(*search.entries));
        if (search.entries == NULL) fail("could not allocate the bounded cache");
        fprintf(stderr, "n=%d: depth-first search with a %zu MiB cache\n",
                n, CACHE_SLOTS * stride * sizeof(*search.entries) >> 20);
        const Mask empty = {0};
        Count count;
        count_suffix(&count, &search, &empty, 0);
        mpz_import(value, (size_t)search.count_words, -1, sizeof(uint64_t), 0, 0, count.word);
        free(search.entries);
    }
    free(board);
}

static int lock_output(void)
{
    const int fd = open(lock_path, O_RDWR | O_CREAT | O_NOFOLLOW | O_NONBLOCK | O_CLOEXEC, 0600);
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
    if (snapshot->st_size < 0 || snapshot->st_size > MAX_SAVED_BYTES)
        fail("b-file exceeds 1 MiB");
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
    size_t bytes = 0;
    const char blanks[] = " \t\r\n";
    const char digits[] = "0123456789";
    while (fgets(line, sizeof(line), input) != NULL) {
        if (strchr(line, '\n') == NULL)
            fail("b-file contains an incomplete or oversized line");
        bytes += strlen(line);
        if (bytes > MAX_SAVED_BYTES) fail("b-file exceeds 1 MiB");
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
        mpz_set_ui(bound, 0);
        mpz_setbit(bound, (mp_bitcnt_t)bound_bits((int)saved_n));
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
    size_t count, total = 0;
    while ((count = fread(data, 1, sizeof(data), input)) != 0) {
        total += count;
        if (total > MAX_SAVED_BYTES) {
            errno = EFBIG;
            return false;
        }
        if (fwrite(data, 1, count, output) != count) return false;
    }
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
           && current.st_uid == snapshot->st_uid && current.st_gid == snapshot->st_gid
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

#if defined(__APPLE__)
static int copy_access_acl(int src, int dst) {
    acl_t acl = src < 0 ? acl_init(0) : acl_get_fd(src);
    if (!acl && src >= 0 && errno == ENOENT) acl = acl_init(0);
    if (!acl) return -1;
    int rc = acl_set_fd(dst, acl);
    int err = errno;
    acl_free(acl);
    errno = err;
    return rc;
}
#elif defined(__linux__)
static int copy_access_acl(int src, int dst) {
    const char *name = "system.posix_acl_access";
    if (src >= 0) {
        unsigned char acl[65536];  // Linux's maximum extended attribute size
        ssize_t len = fgetxattr(src, name, acl, sizeof acl);
        if (len >= 0) return fsetxattr(dst, name, acl, (size_t)len, 0);
        if (errno != ENODATA && errno != ENOTSUP) return -1;
    }
    if (fremovexattr(dst, name) == 0 || errno == ENODATA || errno == ENOTSUP) return 0;
    return -1;
}
#endif

static int publish_new(const char *temporary)
{
#if defined(__APPLE__)
    return renamex_np(temporary, bfile_path, RENAME_EXCL);
#elif defined(__linux__)
    return (int)syscall(SYS_renameat2, AT_FDCWD, temporary, AT_FDCWD, bfile_path,
                        RENAME_NOREPLACE);
#else
    errno = ENOTSUP;
    return -1;
#endif
}

static void remove_temporary(const char *temporary, const char *folder, int error)
{
    unlink(temporary);
    rmdir(folder);
    errno = error;
}

static FILE *save_term(FILE *input, struct stat *snapshot, int directory, int n,
                       const mpz_t value)
{
    if (!saved_is_current(input, snapshot))
        fail("b-file changed during computation");
    char folder[] = ".b402198.tmp.XXXXXX";
    if (mkdtemp(folder) == NULL) fail_io("create private save directory");
    char temporary[sizeof(folder) + sizeof("/term")];
    snprintf(temporary, sizeof(temporary), "%s/term", folder);
    int fd = -1;
    FILE *output = NULL;
    const int folder_fd = open(folder, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    if (folder_fd < 0) goto failed;
#if defined(__APPLE__) || defined(__linux__)
    const int acl_status = copy_access_acl(-1, folder_fd);
    const int acl_error = errno;
    if (acl_status != 0) {
        close(folder_fd);
        errno = acl_error;
        goto failed;
    }
#endif
    if (close(folder_fd) != 0) goto failed;
    fd = open(temporary, O_CREAT | O_EXCL | O_RDWR | O_NOFOLLOW | O_CLOEXEC, 0600);
    if (fd < 0) goto failed;
    output = fdopen(fd, "w+");
    if (output == NULL) goto failed;
    if (!copy_saved(output, input) || gmp_fprintf(output, "%d %Zd\n", n, value) < 0
        || fflush(output) != 0)
        goto failed;
    struct stat mode;
    if (fstat(fd, &mode) != 0) goto failed;
    if (input != NULL && (mode.st_uid != snapshot->st_uid || mode.st_gid != snapshot->st_gid)
        && fchown(fd, snapshot->st_uid, snapshot->st_gid) != 0)
        goto failed;
    if (fchmod(fd, input == NULL ? 0600 : snapshot->st_mode & 0777) != 0)
        goto failed;
#if defined(__APPLE__) || defined(__linux__)
    if (input != NULL && copy_access_acl(fileno(input), fd) != 0) goto failed;
#endif
    if (fsync(fd) != 0) goto failed;
    if (!saved_is_current(input, snapshot)) {
        fclose(output);
        remove_temporary(temporary, folder, ESTALE);
        fail("b-file changed before saving");
    }
    /* The final metadata check and replacement are protected by flock
     * for cooperating writers. POSIX rename has no compare-and-replace. */
    if ((input == NULL ? publish_new(temporary) : rename(temporary, bfile_path)) != 0)
        goto failed;
    if (rmdir(folder) != 0) fail_io("remove empty save directory");
    if (fsync(directory) != 0) fail_io("sync b-file directory");
    if (fstat(fd, snapshot) != 0) fail_io("stat updated b-file");
    if (input != NULL && fclose(input) != 0) fail_io("close previous b-file");
    return output;

failed:;
    const int error = errno;
    if (output != NULL) fclose(output);
    else if (fd >= 0) close(fd);
    remove_temporary(temporary, folder, error);
    fail_io("save b-file");
}

static void usage(FILE *stream, const char *program)
{
    fprintf(stream, "Usage: %s [--memory-mib M | --low-memory] [--no-bfile] N\n"
            "  1 <= N <= %d\n"
            "  N: extend ./b402198.txt through N and print newly computed terms.\n"
            "  --no-bfile N: compute and print only a(N), without opening the b-file.\n"
            "  --memory-mib M: sweep table limit from 16 to 8192 MiB (default 1024).\n"
            "  --low-memory: use bounded-cache depth-first search.\n",
            program, MAX_N);
}

static int parse_integer(const char *argument, int min, int max)
{
    if (*argument == '\0' || argument[strspn(argument, "0123456789")] != '\0') return 0;
    errno = 0;
    char *end;
    const long n = strtol(argument, &end, 10);
    if (errno != 0 || end == argument || *end != '\0' || n < min || n > max)
        return 0;
    return (int)n;
}

int main(int argc, char **argv)
{
    if (argc == 2 && strcmp(argv[1], "--help") == 0) {
        usage(stdout, argv[0]);
        return EXIT_SUCCESS;
    }
    bool single = false, low_memory = false, memory_set = false;
    int arg = 1;
    while (arg < argc - 1) {
        if (!single && strcmp(argv[arg], "--no-bfile") == 0) single = true;
        else if (!memory_set && arg + 1 < argc - 1 &&
                 strcmp(argv[arg], "--memory-mib") == 0) {
            const int limit = parse_integer(argv[++arg], 16, 8192);
            if (limit == 0) break;
            memory_limit = (size_t)limit << 20;
            memory_set = true;
        } else if (!low_memory && strcmp(argv[arg], "--low-memory") == 0) low_memory = true;
        else break;
        ++arg;
    }
    const int n = arg == argc - 1 ? parse_integer(argv[arg], 1, MAX_N) : 0;
    if (n == 0 || (low_memory && memory_set)) {
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
        else if ((directory = open(".", O_RDONLY | O_DIRECTORY | O_CLOEXEC)) < 0)
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
