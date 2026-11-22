/*
 * A402657: Number of ways to tile an n X n square with rectangles of integer
 * side lengths so that both widths and heights weakly decrease to the right
 * in every row and upward in every column. Width is horizontal; height is
 * vertical. T-junctions are allowed. No symmetry identifications are made.
 * Initial terms (n=1..7): 1, 6, 30, 294, 2263, 31579, 333719.
 *
 * Build (GMP required):
 *   cc -O3 -std=c11 -Wall -Wextra -Wpedantic 402657_01.c \
 *      $(pkg-config --cflags --libs gmp) -o 402657_01
 * Usage: ./402657_01 [--start N] [--memory-mib MIB] N
 * Each completed term is saved atomically to b402657.txt before printing.
 * Existing requested terms are recomputed and compared; other terms remain.
 * --start chooses the first index; unfinished DP layers are not checkpointed.
 * Malformed files, including an unterminated final line, are rejected.
 *
 * Sweep unit rows from bottom to top, filling each from left to right.
 * A profile stores three byte arrays for the n columns: remaining height of
 * the old rectangle, its width, and its full height. For a zero remaining
 * height, the dimensions belong to the rectangle in the preceding row.
 * Initial dimension bounds are n, which places no restriction on the board.
 *
 * A new w X h rectangle covers w unoccupied columns, fits inside the board,
 * and has both dimensions no larger than the left neighbor's or any lower
 * neighbor's corresponding dimension. Continuing rectangles are compared
 * with their left neighbors as well. These tests are precisely the adjacent
 * cell inequalities; their transitivity gives the condition on every row
 * and column, including partially shared edges. The previous row's width and
 * height labels are each weakly decreasing, so the rightmost column of a
 * new rectangle gives the tightest bound from below for each dimension.
 *
 * Every tiling has a unique sequence of placements: the rectangle containing
 * the first uncovered cell has that cell as its bottom-left corner. Future
 * placements depend only on the profile and current row. Adding GMP counts
 * of equal profiles therefore counts all tilings without duplication.
 * Finite rectangle tilings of this board have axis-parallel edges, since the
 * positive-edge adjacency graph is connected and sharing an edge forces a
 * common orientation. Scanning from a boundary with integral tile dimensions
 * then puts the vertices on the integer grid.
 *
 * Proven bound: a(n) <= 2^(2*n*(n-1)), since a tiling is determined by the set
 * of internal unit grid edges on tile boundaries. Checked on answers and
 * saved terms. For 1 <= n <= 128: dimensions <= 128, remaining height <= 127,
 * cells <= 16384, exponent <= 32512, recursion depth <= 129, and the profile
 * uses at most 384 bytes. Indices stay inside these fixed arrays. Allocation
 * products are checked before multiplication; table capacities double only
 * after a size check, and their load stays at most 3/4. Full key comparison
 * resolves hash collisions. Counts themselves use arbitrary precision.
 *
 * State arrays and GMP allocations share the memory budget, including old
 * and new rehash arrays and a conservative reservation for realloc. Allocator
 * metadata, stdio and stack are extra. A budget failure saves no unfinished
 * term. Permissions and macOS ACLs are retained during atomic replacement;
 * a stable flock prevents other cooperating instances from writing at once.
 *
 * Independently derived rectangle transitions. Common table, allocation and
 * file helpers are adapted from the independently written 402607_01.c.
 */
#define _POSIX_C_SOURCE 200809L
#define _DARWIN_C_SOURCE

#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>
#ifdef __APPLE__
#include <copyfile.h>
#endif
#include <gmp.h>

enum { MAX_N = 128, DEFAULT_MIB = 1024, MAX_LINE = 12000 };
#define MIB ((size_t)1048576)
#define BFILE "b402657.txt"
_Static_assert(SIZE_MAX >= UINT64_MAX, "64-bit target required");
_Static_assert(MAX_N < UINT8_MAX, "profile values must fit in a byte");

static size_t memory_limit, allocated, peak_allocated;

_Noreturn static void fail(const char *message)
{
    fprintf(stderr, "402657_01: %s\n", message);
    exit(EXIT_FAILURE);
}

static void budget_check(size_t extra)
{
    if (extra > memory_limit - allocated)
        fail("heap budget exceeded; increase --memory-mib or use a smaller N");
}

static void *heap_alloc(size_t bytes)
{
    if (bytes == 0) bytes = 1;
    budget_check(bytes);
    void *p = malloc(bytes);
    if (p == NULL) fail("out of memory");
    allocated += bytes;
    if (allocated > peak_allocated) peak_allocated = allocated;
    return p;
}

static void *heap_resize(void *p, size_t old_bytes, size_t new_bytes)
{
    if (new_bytes == 0) new_bytes = 1;
    /* realloc may hold both blocks briefly, so reserve conservatively. */
    budget_check(new_bytes);
    if (allocated + new_bytes > peak_allocated) peak_allocated = allocated + new_bytes;
    void *q = realloc(p, new_bytes);
    if (q == NULL) fail("out of memory");
    allocated -= old_bytes;
    allocated += new_bytes;
    if (allocated > peak_allocated) peak_allocated = allocated;
    return q;
}

static void heap_free(void *p, size_t bytes)
{
    if (p != NULL) { free(p); allocated -= bytes == 0 ? 1 : bytes; }
}

static void *array_alloc(size_t count, size_t width)
{
    if (width == 0 || count > SIZE_MAX / width) fail("allocation size overflow");
    return heap_alloc(count * width);
}

typedef struct {
    size_t capacity, size, width;
    uint64_t *hashes;
    uint8_t *keys;
    mpz_t *values;
} Table;

static uint64_t hash_key(const uint8_t *key, size_t width)
{
    uint64_t h = UINT64_C(14695981039346656037);
    for (size_t j = 0; j < width; ++j) {
        h ^= key[j];
        /* Deliberate multiplication modulo 2^64, including under sanitizers. */
        (void)__builtin_mul_overflow(h, UINT64_C(1099511628211), &h);
    }
    return h | UINT64_C(1);
}

static void table_init(Table *t, size_t capacity, size_t width)
{
    t->capacity = capacity; t->size = 0; t->width = width;
    t->hashes = array_alloc(capacity, sizeof *t->hashes);
    memset(t->hashes, 0, capacity * sizeof *t->hashes);
    t->keys = array_alloc(capacity, width);
    t->values = array_alloc(capacity, sizeof *t->values);
}

static size_t table_slot(const Table *t, const uint8_t *key, uint64_t hash)
{
    size_t slot = (size_t)hash & (t->capacity - 1);
    while (t->hashes[slot] != 0 &&
           (t->hashes[slot] != hash ||
            memcmp(t->keys + slot * t->width, key, t->width) != 0))
        slot = (slot + 1) & (t->capacity - 1);
    return slot;
}

static void table_clear(Table *t)
{
    if (t->capacity == 0) return;
    for (size_t i = 0; i < t->capacity; ++i)
        if (t->hashes[i] != 0) mpz_clear(t->values[i]);
    heap_free(t->hashes, t->capacity * sizeof *t->hashes);
    heap_free(t->keys, t->capacity * t->width);
    heap_free(t->values, t->capacity * sizeof *t->values);
    *t = (Table){0};
}

static void table_grow(Table *t)
{
    if (t->capacity > SIZE_MAX / 2) fail("table capacity overflow");
    Table larger;
    table_init(&larger, 2 * t->capacity, t->width);
    for (size_t i = 0; i < t->capacity; ++i) if (t->hashes[i] != 0) {
        const uint8_t *key = t->keys + i * t->width;
        size_t j = table_slot(&larger, key, t->hashes[i]);
        memcpy(larger.keys + j * larger.width, key, larger.width);
        larger.hashes[j] = t->hashes[i];
        mpz_init(larger.values[j]);
        mpz_swap(larger.values[j], t->values[i]);
        ++larger.size;
    }
    table_clear(t);
    *t = larger;
}

static void table_add(Table *t, const uint8_t *key, mpz_srcptr ways)
{
    uint64_t hash = hash_key(key, t->width);
    size_t j = table_slot(t, key, hash);
    if (t->hashes[j] != 0) {
        mpz_add(t->values[j], t->values[j], ways);
        return;
    }
    if (t->size >= t->capacity - t->capacity / 4) {
        table_grow(t);
        j = table_slot(t, key, hash);
    }
    t->hashes[j] = hash;
    memcpy(t->keys + j * t->width, key, t->width);
    mpz_init_set(t->values[j], ways);
    ++t->size;
}

typedef struct {
    int n, row;
    const uint8_t *old;
    uint8_t next[3 * MAX_N];
    mpz_srcptr ways;
    Table *dest;
} Filling;

static void fill_row(Filling *f, int x, int left_width, int left_height)
{
    const int n = f->n;
    const uint8_t *remaining = f->old;
    const uint8_t *widths = f->old + n, *heights = f->old + 2 * n;
    while (x < n && remaining[x] != 0) {
        if ((int)widths[x] > left_width || (int)heights[x] > left_height)
            return;
        left_width = widths[x];
        left_height = heights[x++];
    }
    if (x == n) { table_add(f->dest, f->next, f->ways); return; }
    int maximum_width = n - x;
    if (left_width < maximum_width) maximum_width = left_width;
    for (int w = 1; w <= maximum_width; ++w) {
        const int last = x + w - 1;
        /* Prior iterations already established emptiness of the prefix.
         * Width bounds decrease to the right, so either failure excludes
         * all larger widths as well. */
        if (remaining[last] != 0 || w > widths[last]) break;
        int maximum_height = n - f->row;
        if (left_height < maximum_height) maximum_height = left_height;
        if ((int)heights[last] < maximum_height) maximum_height = heights[last];
        for (int h = 1; h <= maximum_height; ++h) {
            for (int c = x; c <= last; ++c) {
                f->next[c] = (uint8_t)(h - 1);
                f->next[n + c] = (uint8_t)w;
                f->next[2 * n + c] = (uint8_t)h;
            }
            fill_row(f, x + w, w, h);
            for (int c = x; c <= last; ++c) {
                f->next[c] = 0;
                f->next[n + c] = widths[c];
                f->next[2 * n + c] = heights[c];
            }
        }
    }
}

static void count_exact(int n, mpz_ptr result)
{
    const size_t width = 3 * (size_t)n;
    Table current, next;
    table_init(&current, 64, width);
    uint8_t initial[3 * MAX_N] = {0};
    memset(initial + n, n, 2 * (size_t)n);
    mpz_set_ui(result, 1);
    table_add(&current, initial, result);
    peak_allocated = allocated;
    for (int row = 0; row < n; ++row) {
        table_init(&next, 64, width);
        for (size_t i = 0; i < current.capacity; ++i) if (current.hashes[i] != 0) {
            Filling f = {.n = n, .row = row,
                         .old = current.keys + i * width,
                         .ways = current.values[i], .dest = &next};
            memcpy(f.next + n, f.old + n, 2 * (size_t)n);
            for (int c = 0; c < n; ++c)
                f.next[c] = f.old[c] == 0 ? 0 : (uint8_t)(f.old[c] - 1);
            fill_row(&f, 0, n, n);
        }
        table_clear(&current);
        current = next;
        fprintf(stderr, "n=%d: row %d/%d, %zu states, peak %.1f MiB\n",
                n, row + 1, n, current.size, (double)peak_allocated / (double)MIB);
    }
    mpz_set_ui(result, 0);
    for (size_t i = 0; i < current.capacity; ++i) if (current.hashes[i] != 0) {
        const uint8_t *key = current.keys + i * width;
        for (int c = 0; c < n; ++c)
            if (key[c] != 0) fail("internal error: unfinished rectangle at top boundary");
        mpz_add(result, result, current.values[i]);
    }
    table_clear(&current);
    mpz_t bound;
    mpz_init_set_ui(bound, 1);
    mpz_mul_2exp(bound, bound, (mp_bitcnt_t)(2 * n * (n - 1)));
    if (mpz_sgn(result) <= 0 || mpz_cmp(result, bound) > 0)
        fail("answer violates proven count bounds");
    mpz_clear(bound);
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
    char line[MAX_LINE];
    uintmax_t last = 0;
    bool handled = n == 0;
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
            if (errno != 0 || index <= last || index > MAX_N ||
                (*number_end != ' ' && *number_end != '\t'))
                goto invalid;
            last = index;

            char *value = number_end + strspn(number_end, " \t");
            size_t digits = strspn(value, "0123456789");
            char *value_end = value + digits;
            if (digits == strspn(value, "0") ||
                value_end[strspn(value_end, " \t\r")] != '\n')
                goto invalid;
            /* A saved value may not exceed the elementary edge-set bound. */
            char end_char = *value_end;
            *value_end = '\0';
            mpz_t saved_value, bound;
            mpz_inits(saved_value, bound, NULL);
            bool valid = mpz_set_str(saved_value, value, 10) == 0;
            mpz_set_ui(bound, 1);
            mpz_mul_2exp(bound, bound, (mp_bitcnt_t)(2 * index * (index - 1)));
            valid = valid && mpz_cmp(saved_value, bound) <= 0;
            mpz_clears(saved_value, bound, NULL);
            *value_end = end_char;
            if (!valid) goto invalid;
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
        if (dest != NULL && fputs(line, dest) == EOF)
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
    perror("402657_01: copying " BFILE);
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
        fputs("402657_01: stdout is redirected to " BFILE "\n", stderr);
    else if (!output_alias)
        fputs("402657_01: stderr is redirected to " BFILE "\n", stdout);
    return true;
}

static bool replace_bfile(size_t n, mpz_srcptr result, const struct stat *lock_stat,
                          const OutputFiles *streams)
{
    struct stat old_stat = {0};
    FILE *source = NULL;
    int original_fd = open(BFILE, O_RDONLY | O_CLOEXEC | O_NOFOLLOW | O_NONBLOCK);
    if (original_fd >= 0) {
        if (fstat(original_fd, &old_stat) != 0 || !S_ISREG(old_stat.st_mode) ||
            old_stat.st_nlink != 1 || old_stat.st_size > 2 * 1024 * 1024) {
            fputs("402657_01: cannot read a regular " BFILE " file\n", stderr);
        } else if (bfile_output_conflict(&old_stat, streams)) {
            close(original_fd);
            return false;
        } else if (same_file(&old_stat, lock_stat)) {
            fputs("402657_01: " BFILE " and its lock refer to the same file\n", stderr);
        } else {
            source = fdopen(original_fd, "r");
            if (source == NULL)
                perror("402657_01: opening the b-file stream");
        }
        if (source == NULL) {
            close(original_fd);
            return false;
        }
    } else if (errno != ENOENT) {
        perror("402657_01: opening " BFILE);
        return false;
    }

    char name[] = BFILE ".tmp.XXXXXX";
    int temp_fd = mkstemp(name);
    FILE *dest = temp_fd >= 0 ? fdopen(temp_fd, "w") : NULL;
    if (dest == NULL) {
        perror("402657_01: creating temporary b-file");
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
    if (ok && changed) {
        off_t length = ftello(dest);
        if (length < 0 || length > 2 * 1024 * 1024) {
            fputs("402657_01: replacement b-file exceeds 2 MiB or cannot be sized\n", stderr);
            ok = false;
        }
    }
    if (ok && changed && fflush(dest) == EOF) {
        perror("402657_01: flushing temporary b-file");
        ok = false;
    }
    if (ok && changed && original_fd >= 0) {
        if (fchmod(temp_fd, old_stat.st_mode & 0777) != 0) {
            perror("402657_01: preserving b-file permissions");
            ok = false;
        }
#ifdef __APPLE__
        if (ok && fcopyfile(original_fd, temp_fd, NULL, COPYFILE_ACL) != 0) {
            perror("402657_01: preserving b-file ACL");
            ok = false;
        }
#endif
    }
    if (ok && changed && fsync(temp_fd) != 0) {
        perror("402657_01: syncing temporary b-file");
        ok = false;
    }
    if (source != NULL && fclose(source) == EOF) {
        perror("402657_01: closing " BFILE);
        ok = false;
    }
    if (fclose(dest) == EOF && ok) {
        perror("402657_01: closing temporary b-file");
        ok = false;
    }
    if (ok && changed) {
        if (rename(name, BFILE) == 0) {
            int dir = open(".", O_RDONLY | O_CLOEXEC);
            ok = dir >= 0 && fsync(dir) == 0;
            if (!ok)
                perror("402657_01: syncing the directory after replacing " BFILE);
            if (dir >= 0 && close(dir) != 0) {
                perror("402657_01: closing b-file directory");
                ok = false;
            }
            return ok;
        }
        perror("402657_01: replacing " BFILE);
        ok = false;
    }
    unlink(name);
    return ok;
}

/* Held for the entire run. The stable lock inode must not be deleted. */
static int acquire_lock(struct stat *lock_stat)
{
    int fd = open(BFILE ".lock", O_RDWR | O_CREAT | O_CLOEXEC | O_NOFOLLOW |
                  O_NONBLOCK, 0600);
    if (fd < 0) { perror("402657_01: opening b-file lock"); return -1; }
    if (fstat(fd, lock_stat) != 0 || !S_ISREG(lock_stat->st_mode) ||
        lock_stat->st_nlink != 1) {
        fputs("402657_01: lock must be a plain regular file\n", stderr);
        close(fd); return -1;
    }
    if (flock(fd, LOCK_EX | LOCK_NB) != 0) {
        perror("402657_01: b-file is locked by another instance");
        close(fd); return -1;
    }
    return fd;
}

static bool validate_existing(const struct stat *lock_stat, const OutputFiles *streams)
{
    int fd = open(BFILE, O_RDONLY | O_CLOEXEC | O_NOFOLLOW | O_NONBLOCK);
    if (fd < 0) {
        if (errno == ENOENT) return true;
        perror("402657_01: opening " BFILE); return false;
    }
    struct stat st;
    bool ok = fstat(fd, &st) == 0;
    if (ok && bfile_output_conflict(&st, streams)) { close(fd); return false; }
    ok = ok && S_ISREG(st.st_mode) && st.st_nlink == 1 &&
         st.st_size <= 2 * 1024 * 1024 && !same_file(&st, lock_stat);
    if (!ok) {
        fputs("402657_01: b-file must be a plain regular file of at most 2 MiB\n", stderr);
        close(fd); return false;
    }
    FILE *input = fdopen(fd, "r");
    if (input == NULL) { close(fd); perror("402657_01: fdopen"); return false; }
    bool changed = false;
    ok = copy_bfile(input, NULL, 0, NULL, &changed);
    if (fclose(input) != 0) { perror("402657_01: closing b-file"); ok = false; }
    return ok;
}

static bool parse_number(const char *text, size_t max, size_t *result)
{
    if (*text == '\0') return false;
    for (const char *s = text; *s != '\0'; ++s)
        if (*s < '0' || *s > '9') return false;
    errno = 0;
    char *end;
    uintmax_t v = strtoumax(text, &end, 10);
    if (errno != 0 || *end != '\0' || v == 0 || v > max) return false;
    *result = (size_t)v;
    return true;
}

static void usage(FILE *f, const char *program)
{
    fprintf(f,
        "Usage: %s [--start N] [--memory-mib MIB] N\n"
        "Count rectangle tilings with both dimensions weakly decreasing right/up, 1 <= N <= %d.\n"
        "  --start N       first index to compute (default 1)\n"
        "  --memory-mib M  table/GMP heap budget (default %d MiB)\n"
        "Each finished term is saved to " BFILE "; no output redirection needed.\n"
        "Existing requested terms are checked; other saved terms are kept.\n"
        "The input limit is an encoding limit, not a runtime guarantee.\n",
        program, MAX_N, DEFAULT_MIB);
}

int main(int argc, char **argv)
{
    OutputFiles streams = {0};
    streams.have_output = fstat(STDOUT_FILENO, &streams.output) == 0;
    streams.have_error = fstat(STDERR_FILENO, &streams.error) == 0;
    struct stat data;
    if (stat(BFILE, &data) == 0 && bfile_output_conflict(&data, &streams))
        return EXIT_FAILURE;
    if (argc == 2 && strcmp(argv[1], "--help") == 0) {
        usage(stdout, argv[0]); return EXIT_SUCCESS;
    }
    size_t start = 1, end = 0, mib = DEFAULT_MIB;
    bool have_start = false, have_memory = false;
    for (int i = 1; i < argc; ++i) {
        if (strcmp(argv[i], "--start") == 0) {
            if (have_start || ++i == argc || !parse_number(argv[i], MAX_N, &start))
                goto invalid;
            have_start = true;
        } else if (strcmp(argv[i], "--memory-mib") == 0) {
            if (have_memory || ++i == argc || !parse_number(argv[i], SIZE_MAX / MIB, &mib))
                goto invalid;
            have_memory = true;
        } else if (end != 0 || !parse_number(argv[i], MAX_N, &end)) {
            goto invalid;
        }
    }
    if (start > end) goto invalid;
    memory_limit = mib * MIB;
    mp_set_memory_functions(heap_alloc, heap_resize, heap_free);
    struct stat lock_stat;
    int lock = acquire_lock(&lock_stat);
    if (lock < 0) return EXIT_FAILURE;
    int status = EXIT_SUCCESS;
    if (!validate_existing(&lock_stat, &streams)) {
        close(lock); return EXIT_FAILURE;
    }
    mpz_t answer;
    mpz_init(answer);
    for (size_t n = start; n <= end; ++n) {
        count_exact((int)n, answer);
        if (!replace_bfile(n, answer, &lock_stat, &streams)) {
            status = EXIT_FAILURE; break;
        }
        if (!write_term(stdout, n, answer) || fflush(stdout) != 0) {
            fputs("402657_01: cannot print result\n", stderr);
            status = EXIT_FAILURE; break;
        }
    }
    mpz_clear(answer);
    if (close(lock) != 0) { perror("402657_01: close lock"); status = EXIT_FAILURE; }
    return status;
invalid:
    usage(stderr, argv[0]);
    return EXIT_FAILURE;
}
