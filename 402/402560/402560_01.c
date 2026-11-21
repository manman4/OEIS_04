/*
 * A402560. Integer-sided equilateral triangles tiling a fixed 60/120 degree rhombus.
 * Adapted from the independently implemented boundary-edge DP in A402226.
 * Build: cc -O3 -std=c11 -Wall -Wextra -Wpedantic 402560_01.c \
 *           $(pkg-config --cflags --libs gmp) -o 402560_01
 *
 * A path through tile interiors, crossing positive-length edge contacts and
 * avoiding vertices, propagates the three edge directions from the boundary.
 * On each maximal straight segment of tile edges, the full tile edges on
 * either side partition that segment (the frame uses just the inside).
 * Thus all vertices on it are at integer distances from its endpoint.
 * Connectedness of the tile perimeters puts all vertices on the unit lattice
 * of the frame. Record the unit edges belonging to tile boundaries.
 *
 * At every vertex an interior face sector has angle 60 or 180 degrees.
 * Include the frame edges and treat each outside ray as present, so the
 * same rule applies on the frame. The allowed masks are empty, two opposite
 * rays, four consecutive rays, or all six. Conversely any occupied component
 * disjoint from the frame would have an extreme vertex (in a generic
 * direction) with all incident edges in an open half-plane, giving a gap
 * greater than 180 degrees. Thus the edge graph, omitting unused vertices,
 * is connected. Each bounded face has a boundary walk with the face on the
 * left. A small inward rounding within its sectors separates repeated visits
 * and gives a simple contour with total turn 360 degrees. The turns of the
 * walk are 0 or 120 degrees, so the walk has three corners and traces an
 * equilateral lattice triangle. This gives a bijection with the tilings.
 *
 * Use lattice basis vectors of length 1 at 60 degrees. The rhombus is
 * 0 <= x,y <= n, containing 2*n^2 elementary triangles.
 *
 * Sweep vertices in (y,x) order. Past choices interact with the future
 * only through the occupied edges joining processed and unprocessed vertices.
 * Recycle bit positions once an edge is read. Count modulo 32-bit primes
 * to store a single 32-bit count per state. CRT is exact once the product
 * of primes exceeds the product of local maximum numbers of continuations.
 * This latter bound follows by multiplying branching bounds in sweep order
 * and depends only on the vertex rules and the frame.
 *
 * Input range 1..30: at most 961 vertices, at most 63 live edge slots
 * (bit 63 is reserved for the empty hash key). Local choices are at most 8,
 * so the count is bounded by 8^961. Counts are reconstructed with GMP.
 * Each modular addition is below 2^33 and each CRT scalar product below
 * 2^64. Hash-table allocations include both maps and a growing replacement.
 * The --memory-mib limit covers state tables. Steps need less than 1 MiB.
 * The b-file is authoritative, protected by a stable advisory lock, and
 * replaced atomically only after fflush/fsync. Previously saved rows are
 * retained, and a computed row must agree with any existing value.
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
    MAX_N = 30,
    WIDTH = MAX_N + 1,
    MAX_POINTS = (MAX_N + 1) * (MAX_N + 1),
    MIN_CAPACITY = 128,
    DEFAULT_MIB = 1024
};

#define MIB ((size_t)1048576)
#define EMPTY_KEY UINT64_MAX
#define BFILE "b402560.txt"

typedef struct {
    uint64_t incoming[3];
    uint64_t incoming_all;
    uint64_t outgoing[8][8];
    unsigned char count[8];
} Step;

typedef struct {
    uint64_t *keys;
    uint32_t *values;
    size_t capacity;
    size_t size;
} Table;

typedef struct {
    size_t limit;
    size_t allocated;
} Budget;

static const int dx[6] = {1, 0, -1, -1, 0, 1};
static const int dy[6] = {0, 1, 1, 0, -1, -1};

static bool inside(int x, int y, int n)
{
    return x >= 0 && x <= n && y >= 0 && y <= n;
}

static bool frame_edge(int x, int y, int u, int v, int n)
{
    return (x == u && (x == 0 || x == n)) ||
           (y == v && (y == 0 || y == n));
}

static bool local_mask(unsigned mask)
{
    if (mask == 0)
        return true;
    unsigned gap = 0;
    /* Two turns include the gap crossing ray 5 to ray 0. */
    for (unsigned i = 0; i < 12; ++i) {
        ++gap;
        if (mask & (1u << (i % 6))) {
            if (i >= 6 && gap != 1 && gap != 3)
                return false;
            gap = 0;
        }
    }
    return true;
}

static size_t make_steps(int n, Step steps[MAX_POINTS], mpz_t bound)
{
    /* Slots of free edges arriving along rays 3, 4 and 5.
       The sweep writes every such entry before reading it. */
    unsigned char pending[WIDTH][WIDTH][3] = {0};
    uint64_t live = 0;
    size_t length = 0;
    mpz_set_ui(bound, 1);
    for (int y = 0; y <= n; ++y) {
        for (int x = 0; x <= n; ++x) {
            if (!inside(x, y, n))
                continue;

            Step *step = &steps[length++];
            memset(step, 0, sizeof *step);
            uint64_t outgoing[3] = {0};
            unsigned forced = 0;
            for (unsigned ray = 0; ray < 6; ++ray) {
                int u = x + dx[ray], v = y + dy[ray];
                if (!inside(u, v, n) || frame_edge(x, y, u, v, n)) {
                    forced |= 1u << ray;
                } else if (ray >= 3) {
                    unsigned slot = pending[y][x][ray - 3];
                    uint64_t bit = UINT64_C(1) << slot;
                    if ((live & bit) == 0)
                        return 0;
                    step->incoming[ray - 3] = bit;
                    step->incoming_all |= bit;
                    live ^= bit;
                }
            }
            for (unsigned ray = 0; ray < 3; ++ray) {
                if ((forced & (1u << ray)) != 0)
                    continue;
                int u = x + dx[ray], v = y + dy[ray];
                /* Keep bit 63 clear so EMPTY_KEY is outside the key range.
                   At each cut at most two crossing edges per vertex of
                   the current row, plus one horizontal edge, can be live.
                   There are n+1 vertices per row, so 2*n+3 <= 63. */
                uint64_t free_bits = ~live & (UINT64_MAX >> 1);
                if (free_bits == 0)
                    return 0;
                unsigned slot = 0;
                while ((free_bits & (UINT64_C(1) << slot)) == 0)
                    ++slot;
                uint64_t bit = UINT64_C(1) << slot;
                live |= bit;
                outgoing[ray] = bit;
                pending[v][u][ray] = (unsigned char)slot;
            }

            unsigned largest = 0;
            for (unsigned mask = 0; mask < 64; ++mask) {
                if ((mask & forced) != forced || !local_mask(mask))
                    continue;
                unsigned in = ((mask & ~forced) >> 3) & 7u;
                uint64_t out = 0;
                for (unsigned ray = 0; ray < 3; ++ray)
                    if (mask & (1u << ray))
                        out |= outgoing[ray];
                unsigned count = step->count[in]++;
                /* At most eight assignments to three outgoing rays. */
                step->outgoing[in][count] = out;
                if (count + 1 > largest)
                    largest = count + 1;
            }
            mpz_mul_ui(bound, bound, largest);
        }
    }
    return live == 0 ? length : 0;
}

static void table_free(Table *table, Budget *budget)
{
    free(table->keys);
    free(table->values);
    budget->allocated -= table->capacity * (sizeof(uint64_t) + sizeof(uint32_t));
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

static size_t slot_for(const Table *table, uint64_t key)
{
    uint64_t hash = key ^ (key >> 30);
    hash = multiply_low(hash, UINT64_C(0xbf58476d1ce4e5b9));
    hash ^= hash >> 27;
    hash = multiply_low(hash, UINT64_C(0x94d049bb133111eb));
    hash ^= hash >> 31;
    size_t mask = table->capacity - 1;
    size_t slot = (size_t)(hash & mask);
    while (table->keys[slot] != EMPTY_KEY && table->keys[slot] != key)
        slot = (slot + 1) & mask;
    return slot;
}

static bool table_grow(Table *table, Budget *budget)
{
    const size_t bytes_per_slot = sizeof(uint64_t) + sizeof(uint32_t);
    /* Include old and new copies in the budget while rehashing. */
    size_t remaining = (budget->limit - budget->allocated) / bytes_per_slot;
    if (table->capacity > remaining / 2)
        return false;
    size_t capacity = table->capacity ? table->capacity * 2 : MIN_CAPACITY;
    if (capacity > remaining)
        return false;

    Table expanded = {0};
    expanded.keys = malloc(capacity * sizeof *expanded.keys);
    expanded.values = calloc(capacity, sizeof *expanded.values);
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
        if (table->keys[i] != EMPTY_KEY) {
            size_t slot = slot_for(&expanded, table->keys[i]);
            expanded.keys[slot] = table->keys[i];
            expanded.values[slot] = table->values[i];
        }
    }
    table_free(table, budget);
    *table = expanded;
    return true;
}

static bool add_state(Table *table, Budget *budget, uint64_t key,
                      uint32_t value, uint32_t prime)
{
    if (table->capacity == 0 && !table_grow(table, budget))
        return false;
    size_t slot = slot_for(table, key);
    if (table->keys[slot] == key) {
        uint64_t sum = (uint64_t)table->values[slot] + value;
        table->values[slot] = (uint32_t)(sum >= prime ? sum - prime : sum);
    } else {
        if (table->size >= table->capacity - table->capacity / 4) {
            if (!table_grow(table, budget))
                return false;
            slot = slot_for(table, key);
        }
        table->keys[slot] = key;
        table->values[slot] = value;
        ++table->size;
    }
    return true;
}

static bool count_mod(const Step *steps, size_t length, uint32_t prime,
                      size_t limit, uint32_t *residue, size_t *peak)
{
    Budget budget = {.limit = limit};
    Table current = {0}, next = {0};
    bool ok = add_state(&current, &budget, 0, 1, prime);
    *peak = current.size;
    for (size_t j = 0; ok && j < length; ++j) {
        const Step *step = &steps[j];
        if (next.capacity > MIN_CAPACITY && next.capacity / 8 > current.size)
            table_free(&next, &budget);
        if (next.capacity != 0)
            memset(next.keys, 0xff, next.capacity * sizeof *next.keys);
        next.size = 0;
        for (size_t i = 0; ok && i < current.capacity; ++i) {
            uint64_t key = current.keys[i];
            if (key == EMPTY_KEY)
                continue;
            unsigned in = (key & step->incoming[0] ? 1u : 0u) |
                          (key & step->incoming[1] ? 2u : 0u) |
                          (key & step->incoming[2] ? 4u : 0u);
            uint64_t retained = key & ~step->incoming_all;
            /* Keep zero residues too. All CRT passes then visit identical
               frontiers, so the first pass also tests the later memory needs. */
            for (unsigned k = 0; k < step->count[in]; ++k) {
                if (!add_state(&next, &budget, retained | step->outgoing[in][k],
                               current.values[i], prime)) {
                    ok = false;
                    break;
                }
            }
        }
        if (next.size > *peak)
            *peak = next.size;
        Table previous = current;
        current = next;
        next = previous;
    }
    if (ok) {
        if (current.size != 1 || current.keys[slot_for(&current, 0)] != 0) {
            fputs("402560_01: inconsistent final frontier\n", stderr);
            ok = false;
        } else {
            *residue = current.values[slot_for(&current, 0)];
        }
    } else {
        fprintf(stderr, "402560_01: state table allocation failed "
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
    Step *steps = malloc(MAX_POINTS * sizeof *steps);
    if (!steps) {
        fputs("402560_01: cannot allocate lattice steps\n", stderr);
        return false;
    }

    mpz_t bound, product, inverse;
    mpz_inits(bound, product, inverse, NULL);
    size_t length = make_steps(n, steps, bound);
    bool ok = length == (size_t)((n + 1) * (n + 1));
    if (!ok)
        fputs("402560_01: inconsistent lattice frontier\n", stderr);

    mpz_set_ui(result, 0);
    mpz_set_ui(product, 1);
    uint32_t candidate = UINT32_MAX;
    unsigned passes = 0;
    fprintf(stderr, "n=%d: computing\n", n);
    while (ok && mpz_cmp(product, bound) <= 0) {
        uint32_t prime = previous_prime(candidate);
        if (prime == 0) {
            fputs("402560_01: exhausted CRT moduli\n", stderr);
            ok = false;
            break;
        }
        candidate = prime - 2;
        uint32_t residue;
        size_t peak;
        ok = count_mod(steps, length, prime, limit, &residue, &peak);
        if (!ok)
            break;

        uint64_t x_mod = mpz_fdiv_ui(result, prime);
        uint64_t delta = ((uint64_t)residue + prime - x_mod) % prime;
        mpz_set_ui(inverse, prime);
        if (mpz_invert(inverse, product, inverse) == 0) {
            fputs("402560_01: CRT moduli are not coprime\n", stderr);
            ok = false;
            break;
        }
        /* delta and the inverse are below 2^32, so the product fits. */
        unsigned long k = (unsigned long)((delta * mpz_get_ui(inverse)) % prime);
        mpz_addmul_ui(result, product, k);
        mpz_mul_ui(product, product, prime);
        fprintf(stderr, "n=%d: CRT pass %u, peak %zu states\n", n, ++passes, peak);
    }
    if (ok && (mpz_sgn(result) <= 0 || mpz_cmp(result, bound) > 0)) {
        fputs("402560_01: result violates the count bounds\n", stderr);
        ok = false;
    }

    mpz_clears(bound, product, inverse, NULL);
    free(steps);
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
    perror("402560_01: copying " BFILE);
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
        fputs("402560_01: stdout is redirected to " BFILE "\n", stderr);
    else if (!output_alias)
        fputs("402560_01: stderr is redirected to " BFILE "\n", stdout);
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
            fputs("402560_01: cannot read a regular " BFILE " file\n", stderr);
        } else if (bfile_output_conflict(&old_stat, streams)) {
            close(original_fd);
            return false;
        } else if (same_file(&old_stat, lock_stat)) {
            fputs("402560_01: " BFILE " and its lock refer to the same file\n", stderr);
        } else {
            source = fdopen(original_fd, "r");
            if (source == NULL)
                perror("402560_01: opening the b-file stream");
        }
        if (source == NULL) {
            close(original_fd);
            return false;
        }
    } else if (errno != ENOENT) {
        perror("402560_01: opening " BFILE);
        return false;
    }

    char name[] = BFILE ".tmp.XXXXXX";
    int temp_fd = mkstemp(name);
    FILE *dest = temp_fd >= 0 ? fdopen(temp_fd, "w") : NULL;
    if (dest == NULL) {
        perror("402560_01: creating temporary b-file");
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
        perror("402560_01: flushing temporary b-file");
        ok = false;
    }
    if (ok && changed && original_fd >= 0) {
        if (fchmod(temp_fd, old_stat.st_mode & 0777) != 0) {
            perror("402560_01: preserving b-file permissions");
            ok = false;
        }
#ifdef __APPLE__
        if (ok && fcopyfile(original_fd, temp_fd, NULL, COPYFILE_ACL) != 0) {
            perror("402560_01: preserving b-file ACL");
            ok = false;
        }
#endif
    }
    if (ok && changed && fsync(temp_fd) != 0) {
        perror("402560_01: syncing temporary b-file");
        ok = false;
    }
    if (source != NULL && fclose(source) == EOF) {
        perror("402560_01: closing " BFILE);
        ok = false;
    }
    if (fclose(dest) == EOF && ok) {
        perror("402560_01: closing temporary b-file");
        ok = false;
    }
    if (ok && changed) {
        if (rename(name, BFILE) == 0) {
            int dir = open(".", O_RDONLY | O_CLOEXEC);
            ok = dir >= 0 && fsync(dir) == 0;
            if (!ok)
                perror("402560_01: syncing the directory after replacing " BFILE);
            if (dir >= 0)
                close(dir);
            return ok;
        }
        perror("402560_01: replacing " BFILE);
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
        perror("402560_01: opening the b-file lock");
        return false;
    }
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode)) {
        fputs("402560_01: b-file lock must be a regular file\n", stderr);
        close(fd);
        return false;
    }
    struct flock lock = {.l_type = F_WRLCK, .l_whence = SEEK_SET};
    int locked;
    do {
        locked = fcntl(fd, F_SETLKW, &lock);
    } while (locked < 0 && errno == EINTR);
    if (locked < 0)
        perror("402560_01: locking the b-file");
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
            fputs("402560_01: cannot write the result\n", stderr);
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
