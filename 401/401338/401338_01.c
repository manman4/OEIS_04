/*
 * A401338. Tilings of the staircase with row lengths n,n-1,...,1
 * by squares of integer side lengths, for n >= 1.
 * Independently implemented row-profile DP; hash/CRT and file saving are
 * adapted from this repository's independently implemented 402560_01.c.
 *
 * Build: cc -O3 -std=c11 -Wall -Wextra -Wpedantic 401338_01.c \
 *           $(pkg-config --cflags --libs gmp) -o 401338_01
 * Run: ./401338_01 --memory-mib 4096 10
 * Each completed term is saved to b401338.txt in the working directory.
 *
 * Geometry: the cells are (x,y) with x,y >= 0 and x+y < n. Squares have
 * their sides parallel to the boundary: positive-length tile adjacencies
 * propagate the two directions from the frame throughout a finite tiling.
 * Along any maximal straight chain of tile edges the full edges on either
 * side partition the chain into integer lengths. All its vertices are
 * therefore integer distances from its endpoint. Connectedness of tile
 * perimeters then puts all tile vertices on the frame's unit lattice.
 *
 * A row profile gives the remaining occupied depth in each column.
 * If an active square has side k, its depth d satisfies 1 <= d < k,
 * and its k columns have the same depth. Hence a maximal positive plateau
 * of width w and depth d always satisfies w >= d+1. Encode that plateau
 * by w two-bit tokens: 01, then d-1 copies of 11, then w-d copies of 10.
 * A zero column is 00. Maximal plateaus make the encoding canonical.
 * This stores 32 columns in one 64-bit key. The last staircase column
 * can only contain a unit square, so its two bits are always zero, and
 * UINT64_MAX cannot be a real key.
 *
 * Decode a row and decrement occupied depths for the next row. At its
 * first free cell (column,y), choose a square side k. The k columns must
 * be free, and column+y+2*k-2 < n. Fill those columns in the next profile
 * to depth k-1, merging equal neighboring plateaus. Each tiling makes a
 * unique sequence of these choices. The row recursion has at most 32
 * placements plus the terminating call (33 simultaneous calls).
 *
 * Counts use LANES 32-bit primes in one pass (default 2), followed by
 * exact CRT reconstruction with GMP. Trial division proves each modulus.
 * A count bound is floor((n+1)/2)^(n*(n+1)/2), by bounding choices at each
 * cell. A second bound follows by recording each tile's unit grid edges.
 * At an interior vertex (n-1)*(n-2)/2 of them, given the incoming west and
 * south edges, at most three outgoing east/north pairs can occur: the
 * gaps between tile-boundary rays must be 90 or 180 degrees. At the
 * 2*(n-1) straight boundary vertices there are at most two choices.
 * At staircase corners, the outgoing edges are forced by the frame.
 * Thus 3^((n-1)*(n-2)/2) * 2^(2*n-2) also bounds the count. Use the smaller
 * bound, and stop only when the product of distinct primes exceeds it.
 *
 * Input range 1..32. Square sides are at most 16, depths at most 15.
 * A positive plateau ends before column 31, so encoding never shifts by
 * 64. Decoding shifts by at most 62, and working-depth shifts by at most
 * 60. Modular sums fit in 33 bits and CRT scalar products in 64 bits.
 * State-table allocation bounds include both maps and rehashing copies.
 * Define LANES=1..8 at compile time to trade memory for fewer CRT passes.
 * At the default LANES=2 each hash slot needs 8 + 2*4 = 16 bytes.
 *
 * The b-file is authoritative. Updates preserve saved rows, require any
 * recomputed row to agree, and use a separate stable advisory lock.
 * Data and (on macOS) ACLs are copied to a temporary file, synced, then
 * renamed atomically. Results are printed only after successful saving.
 */
#define _POSIX_C_SOURCE 200809L
#ifdef __APPLE__
#define _DARWIN_C_SOURCE
#endif
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#ifdef __APPLE__
#include <copyfile.h>
#endif

#include <gmp.h>

enum {
    MAX_N = 32,
    MIN_CAPACITY = 128,
    DEFAULT_MIB = 1024
};

#define MIB ((size_t)1048576)
#define EMPTY_KEY UINT64_MAX
#define BFILE "b401338.txt"

#ifndef LANES
#define LANES 2
#endif
_Static_assert(LANES >= 1 && LANES <= 8, "LANES must be in 1..8");

typedef uint64_t Key;
typedef struct {
    uint64_t low;
    uint64_t high;
} Profile;

typedef struct {
    Key *keys;
    uint32_t *values;
    size_t capacity;
    size_t size;
} Table;

typedef struct {
    size_t limit;
    size_t allocated;
} Budget;

static bool key_empty(Key key)
{
    return key == EMPTY_KEY;
}

static bool key_equal(Key a, Key b)
{
    return a == b;
}

static unsigned profile_get(Profile key, unsigned column)
{
    uint64_t word = column < 16 ? key.low : key.high;
    return (unsigned)((word >> (4 * (column % 16))) & 15u);
}

static Profile profile_set(Profile key, unsigned column, unsigned depth)
{
    unsigned shift = 4 * (column % 16);
    uint64_t mask = UINT64_C(15) << shift;
    uint64_t bits = (uint64_t)depth << shift;
    if (column < 16)
        key.low = (key.low & ~mask) | bits;
    else
        key.high = (key.high & ~mask) | bits;
    return key;
}

static void table_free(Table *table, Budget *budget)
{
    free(table->keys);
    free(table->values);
    budget->allocated -= table->capacity * (sizeof(Key) + LANES * sizeof(uint32_t));
    *table = (Table){0};
}

/* This finalizer intentionally multiplies modulo 2^64.
   The implementation below masks each half product before combining it,
   keeping intentional wrap out of the integer sanitizer. */
static uint64_t multiply_low(uint64_t x, uint64_t y)
{
    uint64_t low = (x & UINT32_MAX) * (y & UINT32_MAX);
    uint64_t high = ((x >> 32) * (y & UINT32_MAX)) & UINT32_MAX;
    high += ((y >> 32) * (x & UINT32_MAX)) & UINT32_MAX;
    high += low >> 32;
    return (low & UINT32_MAX) | ((high & UINT32_MAX) << 32);
}

static size_t slot_for(const Table *table, Key key)
{
    uint64_t hash = key ^ (key >> 30);
    hash = multiply_low(hash, UINT64_C(0xbf58476d1ce4e5b9));
    hash ^= hash >> 27;
    hash = multiply_low(hash, UINT64_C(0x94d049bb133111eb));
    hash ^= hash >> 31;
    size_t mask = table->capacity - 1;
    size_t slot = (size_t)(hash & mask);
    while (!key_empty(table->keys[slot]) && !key_equal(table->keys[slot], key))
        slot = (slot + 1) & mask;
    return slot;
}

static bool table_grow(Table *table, Budget *budget)
{
    const size_t bytes_per_slot = sizeof(Key) + LANES * sizeof(uint32_t);
    /* Include old and new copies in the budget while rehashing. */
    size_t remaining = (budget->limit - budget->allocated) / bytes_per_slot;
    if (table->capacity > remaining / 2)
        return false;
    size_t capacity = table->capacity ? table->capacity * 2 : MIN_CAPACITY;
    if (capacity > remaining)
        return false;

    Table expanded = {0};
    expanded.keys = malloc(capacity * sizeof *expanded.keys);
    expanded.values = calloc(capacity, LANES * sizeof *expanded.values);
    if (!expanded.keys || !expanded.values) {
        free(expanded.keys);
        free(expanded.values);
        return false;
    }
    expanded.capacity = capacity;
    expanded.size = table->size;
    budget->allocated += capacity * bytes_per_slot;
    memset(expanded.keys, 0xff, capacity * sizeof *expanded.keys);
    for (size_t i = 0; i < table->capacity; ++i) {
        if (!key_empty(table->keys[i])) {
            size_t slot = slot_for(&expanded, table->keys[i]);
            expanded.keys[slot] = table->keys[i];
            memcpy(expanded.values + slot * LANES, table->values + i * LANES,
                   LANES * sizeof *expanded.values);
        }
    }
    table_free(table, budget);
    *table = expanded;
    return true;
}

static bool add_state(Table *table, Budget *budget, Key key,
                      const uint32_t values[LANES], const uint32_t primes[LANES])
{
    if (table->capacity == 0 && !table_grow(table, budget))
        return false;
    size_t slot = slot_for(table, key);
    if (key_equal(table->keys[slot], key)) {
        uint32_t *dest = table->values + slot * LANES;
        for (unsigned lane = 0; lane < LANES; ++lane) {
            uint64_t sum = (uint64_t)dest[lane] + values[lane];
            dest[lane] = (uint32_t)(sum >= primes[lane] ? sum - primes[lane] : sum);
        }
    } else {
        if (table->size >= table->capacity - table->capacity / 4) {
            if (!table_grow(table, budget))
                return false;
            slot = slot_for(table, key);
        }
        table->keys[slot] = key;
        memcpy(table->values + slot * LANES, values, LANES * sizeof *values);
        ++table->size;
    }
    return true;
}

/* A positive plateau of width w and depth d has w >= d+1, because
   every square crossing this row has side k > d and covers k columns.
   Encode the plateau using w two-bit tokens: 01, (d-1) copies of 11,
   then (w-d) copies of 10. A zero column is 00. Equal adjacent depths
   are merged into maximal plateaus, giving a canonical 2*n-bit key. */
static bool set_plateau(Key *key, unsigned start, unsigned end, unsigned depth)
{
    if (start >= end || end >= 32 || depth == 0 || depth >= 16 ||
        end - start <= depth) {
        fputs("401338_01: invalid active-square plateau\n", stderr);
        return false;
    }
    unsigned length = end - start;
    uint64_t mask = (UINT64_C(1) << (2 * length)) - 1;
    uint64_t low = UINT64_C(0x5555555555555555) &
                   ((UINT64_C(1) << (2 * depth)) - 1);
    uint64_t high = UINT64_C(0xAAAAAAAAAAAAAAAA) & mask & ~UINT64_C(2);
    *key = (*key & ~(mask << (2 * start))) | ((low | high) << (2 * start));
    return true;
}

static bool encode_profile(Profile profile, unsigned width, Key *key)
{
    *key = 0;
    for (unsigned column = 0; column < width;) {
        unsigned depth = profile_get(profile, column);
        if (depth == 0) {
            ++column;
            continue;
        }
        unsigned end = column + 1;
        while (end < width && profile_get(profile, end) == depth)
            ++end;
        if (!set_plateau(key, column, end, depth))
            return false;
        column = end;
    }
    return true;
}

static bool place_square(Profile *profile, Key *key, unsigned column,
                         unsigned side, unsigned width)
{
    if (side == 1)
        return true;
    unsigned depth = side - 1;
    for (unsigned j = column; j < column + side; ++j)
        *profile = profile_set(*profile, j, depth);
    unsigned start = column;
    unsigned end = column + side;
    while (start > 0 && profile_get(*profile, start - 1) == depth)
        --start;
    while (end < width && profile_get(*profile, end) == depth)
        ++end;
    return set_plateau(key, start, end, depth);
}

static bool decode_profile(Key key, unsigned width, unsigned char profile[MAX_N],
                           Profile *following)
{
    *following = (Profile){0};
    for (unsigned column = 0; column < width;) {
        unsigned token = (unsigned)((key >> (2 * column)) & 3u);
        if (token == 0) {
            profile[column++] = 0;
            continue;
        }
        if (token != 1)
            return false;
        unsigned split = column + 1;
        while (split < width && ((key >> (2 * split)) & 3u) == 3u)
            ++split;
        unsigned end = split;
        while (end < width && ((key >> (2 * end)) & 3u) == 2u)
            ++end;
        unsigned depth = split - column;
        if (end == split || depth >= 16)
            return false;
        for (unsigned j = column; j < end; ++j) {
            profile[j] = (unsigned char)depth;
            *following = profile_set(*following, j, depth - 1);
        }
        column = end;
    }
    return true;
}

typedef struct {
    unsigned width;
    const unsigned char *profile;
    Table *dest;
    Budget *budget;
    const uint32_t *values;
    const uint32_t *primes;
} RowFill;

static bool fill_row(const RowFill *fill, unsigned column, Profile next, Key encoded)
{
    while (column < fill->width && fill->profile[column] != 0)
        ++column;
    if (column == fill->width)
        return add_state(fill->dest, fill->budget, encoded, fill->values, fill->primes);

    /* The farthest cell of a square of side k, starting at (column,y),
       has x+y = column+y+2*k-2 and must be smaller than n. */
    unsigned largest = (fill->width - column + 1) / 2;
    for (unsigned side = 1; side <= largest; ++side) {
        if (fill->profile[column + side - 1] != 0)
            break;
        Profile placed = next;
        Key placed_key = encoded;
        if (!place_square(&placed, &placed_key, column, side, fill->width) ||
            !fill_row(fill, column + side, placed, placed_key))
            return false;
    }
    return true;
}

static bool count_mod(int n, const uint32_t primes[LANES], size_t limit,
                      uint32_t residues[LANES], size_t *peak)
{
    Budget budget = {.limit = limit};
    Table current = {0}, next = {0};
    const Key zero = {0};
    uint32_t one[LANES];
    for (unsigned lane = 0; lane < LANES; ++lane)
        one[lane] = 1;
    bool ok = add_state(&current, &budget, zero, one, primes);
    *peak = current.size;
    for (unsigned width = (unsigned)n; ok && width != 0; --width) {
        if (next.capacity > MIN_CAPACITY && next.capacity / 8 > current.size)
            table_free(&next, &budget);
        if (next.capacity != 0)
            memset(next.keys, 0xff, next.capacity * sizeof *next.keys);
        next.size = 0;
        for (size_t i = 0; ok && i < current.capacity; ++i) {
            Key key = current.keys[i];
            if (key_empty(key))
                continue;
            unsigned char profile[MAX_N] = {0};
            Profile following;
            if (!decode_profile(key, width, profile, &following)) {
                fputs("401338_01: invalid encoded profile\n", stderr);
                ok = false;
                break;
            }
            if (profile_get(following, width - 1) != 0) {
                fputs("401338_01: a square extends outside the staircase\n", stderr);
                ok = false;
                break;
            }
            RowFill fill = {
                .width = width, .profile = profile, .dest = &next,
                .budget = &budget, .values = current.values + i * LANES, .primes = primes
            };
            /* Zero residues are retained so all CRT passes use identical
               states and have the same allocation requirements. */
            Key encoded;
            ok = encode_profile(following, width, &encoded) &&
                 fill_row(&fill, 0, following, encoded);
        }
        if (next.size > *peak)
            *peak = next.size;
        Table previous = current;
        current = next;
        next = previous;
    }
    if (ok) {
        if (current.size != 1 ||
            !key_equal(current.keys[slot_for(&current, zero)], zero)) {
            fputs("401338_01: inconsistent final profile\n", stderr);
            ok = false;
        } else {
            size_t slot = slot_for(&current, zero);
            memcpy(residues, current.values + slot * LANES, LANES * sizeof *residues);
        }
    } else {
        fprintf(stderr, "401338_01: state table allocation failed or invalid profile "
                        "(limit %zu MiB, peak %zu states reached)\n",
                limit / MIB, *peak);
    }
    table_free(&current, &budget);
    table_free(&next, &budget);
    return ok;
}

static uint32_t previous_prime(uint32_t candidate)
{
    /* Only called with an odd starting value. Trial division proves primality. */
    for (; candidate > INT32_MAX; candidate -= 2) {
        uint32_t divisor = 3;
        while (divisor <= candidate / divisor && candidate % divisor != 0)
            divisor += 2;
        if (divisor > candidate / divisor)
            return candidate;
    }
    return 0;
}

static bool count_exact(int n, size_t limit, mpz_t result)
{
    mpz_t bound, product, inverse;
    mpz_inits(bound, product, inverse, NULL);
    /* At each of n*(n+1)/2 cells, there are at most (n+1)/2 possible
       side lengths for a square anchored at the first unfilled cell. */
    unsigned long cells = (unsigned long)n * (unsigned long)(n + 1) / 2;
    mpz_ui_pow_ui(bound, (unsigned long)(n + 1) / 2, cells);
    /* A square tiling injects into its grid-edge boundary pattern.
       Each interior vertex has at most 3 choices for its outgoing edges,
       given the incoming edges. There are (n-1)*(n-2)/2 such vertices.
       The 2*(n-1) straight boundary vertices have at most 2 choices each;
       the staircase corners contribute no outgoing choices. */
    unsigned long interior = (unsigned long)((n - 1) * (n - 2) / 2);
    mpz_ui_pow_ui(inverse, 3, interior);
    mpz_mul_2exp(inverse, inverse, (mp_bitcnt_t)(2 * (n - 1)));
    if (mpz_cmp(inverse, bound) < 0)
        mpz_set(bound, inverse);
    bool ok = true;

    mpz_set_ui(result, 0);
    mpz_set_ui(product, 1);
    uint32_t candidate = UINT32_MAX;
    unsigned passes = 0;
    fprintf(stderr, "n=%d: computing\n", n);
    while (ok && mpz_cmp(product, bound) <= 0) {
        uint32_t primes[LANES], residues[LANES];
        for (unsigned lane = 0; lane < LANES; ++lane) {
            primes[lane] = previous_prime(candidate);
            if (primes[lane] == 0) {
                fputs("401338_01: exhausted CRT moduli\n", stderr);
                ok = false;
                break;
            }
            candidate = primes[lane] - 2;
        }
        size_t peak = 0;
        if (ok)
            ok = count_mod(n, primes, limit, residues, &peak);
        if (!ok)
            break;
        for (unsigned lane = 0; lane < LANES; ++lane) {
            uint32_t prime = primes[lane];
            uint64_t x_mod = mpz_fdiv_ui(result, prime);
            uint64_t delta = ((uint64_t)residues[lane] + prime - x_mod) % prime;
            mpz_set_ui(inverse, prime);
            if (mpz_invert(inverse, product, inverse) == 0) {
                fputs("401338_01: CRT moduli are not coprime\n", stderr);
                ok = false;
                break;
            }
            unsigned long k = (unsigned long)((delta * mpz_get_ui(inverse)) % prime);
            mpz_addmul_ui(result, product, k);
            mpz_mul_ui(product, product, prime);
        }
        fprintf(stderr, "n=%d: CRT pass %u (%u primes/pass), peak %zu states\n",
                n, ++passes, (unsigned)LANES, peak);
    }
    if (ok && (mpz_sgn(result) <= 0 || mpz_cmp(result, bound) > 0)) {
        fputs("401338_01: result violates the count bounds\n", stderr);
        ok = false;
    }

    mpz_clears(bound, product, inverse, NULL);
    return ok;
}

static bool write_term(FILE *stream, size_t n, mpz_srcptr result)
{
    return gmp_fprintf(stream, "%zu %Zd\n", n, result) >= 0;
}

/* The copy preserves existing lines, including comments and whitespace.
   A missing index can be inserted anywhere in the increasing sequence. */
static bool copy_bfile(FILE *source, FILE *dest, size_t n, mpz_srcptr result,
                       bool *changed)
{
    char line[4096];
    uintmax_t last = 0;
    bool handled = false;
    int ch;
    while (source != NULL && (ch = fgetc(source)) != EOF) {
        size_t len = 0;
        while (ch != '\n') {
            if (ch == EOF || ch == '\0' || len == sizeof line - 2)
                goto invalid;
            line[len++] = (char)ch;
            ch = fgetc(source);
        }
        line[len++] = '\n';
        line[len] = '\0';

        char *p = line + strspn(line, " \t\r");
        if (*p != '#' && *p != '\n') {
            if (*p < '0' || *p > '9')
                goto invalid;
            char *number_end;
            errno = 0;
            uintmax_t index = strtoumax(p, &number_end, 10);
            if (errno != 0 || index <= last ||
                (*number_end != ' ' && *number_end != '\t'))
                goto invalid;
            last = index;

            char *value = number_end + strspn(number_end, " \t");
            size_t digits = strspn(value, "0123456789");
            char *value_end = value + digits;
            if (digits == strspn(value, "0") ||
                value_end[strspn(value_end, " \t\r")] != '\n')
                goto invalid;
            if (!handled && index >= n) {
                handled = true;
                if (index == n) {
                    char saved = *value_end;
                    *value_end = '\0';
                    mpz_t old;
                    mpz_init(old);
                    bool equal = mpz_set_str(old, value, 10) == 0 &&
                                 mpz_cmp(old, result) == 0;
                    mpz_clear(old);
                    *value_end = saved;
                    if (!equal) {
                        fprintf(stderr, "%s already has a different value at n=%zu\n",
                                BFILE, n);
                        return false;
                    }
                } else {
                    *changed = true;
                    if (!write_term(dest, n, result))
                        goto io_error;
                }
            }
        }
        if (fputs(line, dest) == EOF)
            goto io_error;
    }
    if (source != NULL && ferror(source))
        goto io_error;
    if (!handled) {
        *changed = true;
        if (!write_term(dest, n, result))
            goto io_error;
    }
    return true;

invalid:
    if (source != NULL && ferror(source))
        goto io_error;
    fprintf(stderr, "%s contains an invalid, incomplete, or unsorted line\n", BFILE);
    return false;

io_error:
    perror("401338_01: copying " BFILE);
    return false;
}

typedef struct {
    struct stat output;
    struct stat error;
    bool have_output;
    bool have_error;
} OutputFiles;

static bool same_file(const struct stat *a, const struct stat *b)
{
    return a->st_dev == b->st_dev && a->st_ino == b->st_ino;
}

static bool bfile_output_conflict(const struct stat *data, const OutputFiles *streams)
{
    bool output_alias = streams->have_output && same_file(data, &streams->output);
    bool error_alias = streams->have_error && same_file(data, &streams->error);
    if (!output_alias && !error_alias)
        return false;

    /* A diagnostic must also avoid any stream redirected to the b-file. */
    if (!error_alias)
        fputs("401338_01: stdout is redirected to " BFILE "\n", stderr);
    else if (!output_alias)
        fputs("401338_01: stderr is redirected to " BFILE "\n", stdout);
    return true;
}

static bool replace_bfile(size_t n, mpz_srcptr result, const struct stat *lock_stat,
                          const OutputFiles *streams)
{
    struct stat old_stat = {0};
    FILE *source = NULL;
    int original_fd = open(BFILE, O_RDONLY | O_CLOEXEC | O_NOFOLLOW | O_NONBLOCK);
    if (original_fd >= 0) {
        if (fstat(original_fd, &old_stat) != 0 || !S_ISREG(old_stat.st_mode)) {
            fputs("401338_01: cannot read a regular " BFILE " file\n", stderr);
        } else if (bfile_output_conflict(&old_stat, streams)) {
            close(original_fd);
            return false;
        } else if (same_file(&old_stat, lock_stat)) {
            fputs("401338_01: " BFILE " and its lock refer to the same file\n", stderr);
        } else {
            source = fdopen(original_fd, "r");
            if (source == NULL)
                perror("401338_01: opening the b-file stream");
        }
        if (source == NULL) {
            close(original_fd);
            return false;
        }
    } else if (errno != ENOENT) {
        perror("401338_01: opening " BFILE);
        return false;
    }

    char name[] = BFILE ".tmp.XXXXXX";
    int temp_fd = mkstemp(name);
    FILE *dest = temp_fd >= 0 ? fdopen(temp_fd, "w") : NULL;
    if (dest == NULL) {
        perror("401338_01: creating temporary b-file");
        if (temp_fd >= 0) {
            close(temp_fd);
            unlink(name);
        }
        if (source != NULL)
            fclose(source);
        return false;
    }

    bool changed = false;
    bool ok = copy_bfile(source, dest, n, result, &changed);
    if (ok && changed && fflush(dest) == EOF) {
        perror("401338_01: flushing temporary b-file");
        ok = false;
    }
    if (ok && changed && original_fd >= 0) {
        if (fchmod(temp_fd, old_stat.st_mode & 0777) != 0) {
            perror("401338_01: preserving b-file permissions");
            ok = false;
        }
#ifdef __APPLE__
        if (ok && fcopyfile(original_fd, temp_fd, NULL, COPYFILE_ACL) != 0) {
            perror("401338_01: preserving b-file ACL");
            ok = false;
        }
#endif
    }
    if (ok && changed && fsync(temp_fd) != 0) {
        perror("401338_01: syncing temporary b-file");
        ok = false;
    }
    if (source != NULL && fclose(source) == EOF) {
        perror("401338_01: closing " BFILE);
        ok = false;
    }
    if (fclose(dest) == EOF && ok) {
        perror("401338_01: closing temporary b-file");
        ok = false;
    }
    if (ok && changed) {
        if (rename(name, BFILE) == 0) {
            int dir = open(".", O_RDONLY | O_CLOEXEC);
            ok = dir >= 0 && fsync(dir) == 0;
            if (!ok)
                perror("401338_01: syncing the directory after replacing " BFILE);
            if (dir >= 0)
                close(dir);
            return ok;
        }
        perror("401338_01: replacing " BFILE);
        ok = false;
    }
    unlink(name);
    return ok;
}

static bool save_bfile(size_t n, mpz_srcptr result, const OutputFiles *streams)
{
    /* Lock a separate, stable inode since rename replaces the data inode. */
    int fd = open(BFILE ".lock", O_RDWR | O_CREAT | O_CLOEXEC | O_NOFOLLOW |
                  O_NONBLOCK, 0666);
    if (fd < 0) {
        perror("401338_01: opening the b-file lock");
        return false;
    }
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode)) {
        fputs("401338_01: b-file lock must be a regular file\n", stderr);
        close(fd);
        return false;
    }
    struct flock lock = {.l_type = F_WRLCK, .l_whence = SEEK_SET};
    int locked;
    do {
        locked = fcntl(fd, F_SETLKW, &lock);
    } while (locked < 0 && errno == EINTR);
    if (locked < 0)
        perror("401338_01: locking the b-file");
    bool ok = locked == 0 && replace_bfile(n, result, &st, streams);
    close(fd);
    return ok;
}

static bool parse_number(const char *text, size_t max, size_t *result)
{
    if (text[0] < '0' || text[0] > '9')
        return false;
    errno = 0;
    char *end;
    uintmax_t value = strtoumax(text, &end, 10);
    if (errno != 0 || *end != '\0' || value == 0 || value > max)
        return false;
    *result = (size_t)value;
    return true;
}

static void usage(FILE *stream, const char *program)
{
    fprintf(stream, "Usage: %s [--start N] [--memory-mib MIB] N\n"
                    "Compute through N (1..%d). Save each completed n a(n) line in " BFILE ".\n"
                    "--start N       first index (default 1)\n"
                    "--memory-mib M  state table limit (default %d MiB)\n",
            program, MAX_N, DEFAULT_MIB);
}

int main(int argc, char **argv)
{
    /* Check before progress or usage output, and again under the file lock. */
    OutputFiles streams = {0};
    streams.have_output = fstat(STDOUT_FILENO, &streams.output) == 0;
    streams.have_error = fstat(STDERR_FILENO, &streams.error) == 0;
    struct stat data;
    if (stat(BFILE, &data) == 0 && bfile_output_conflict(&data, &streams))
        return EXIT_FAILURE;

    if (argc == 2 && strcmp(argv[1], "--help") == 0) {
        usage(stdout, argv[0]);
        return EXIT_SUCCESS;
    }
    size_t start = 1, end = 0, mib = DEFAULT_MIB;
    for (int i = 1; i < argc; ++i) {
        if (strcmp(argv[i], "--memory-mib") == 0) {
            if (++i == argc || !parse_number(argv[i], SIZE_MAX / MIB, &mib))
                goto invalid;
        } else if (strcmp(argv[i], "--start") == 0) {
            if (++i == argc || !parse_number(argv[i], MAX_N, &start))
                goto invalid;
        } else if (end != 0 || !parse_number(argv[i], MAX_N, &end)) {
            goto invalid;
        }
    }
    if (start > end)
        goto invalid;

    mpz_t result;
    mpz_init(result);
    int status = EXIT_SUCCESS;
    for (size_t n = start; n <= end; ++n) {
        if (!count_exact((int)n, mib * MIB, result) || !save_bfile(n, result, &streams)) {
            status = EXIT_FAILURE;
            break;
        }
        if (!write_term(stdout, n, result) || fflush(stdout) == EOF) {
            fputs("401338_01: cannot write the result\n", stderr);
            status = EXIT_FAILURE;
            break;
        }
    }
    mpz_clear(result);
    return status;

invalid:
    usage(stderr, argv[0]);
    return EXIT_FAILURE;
}
