/*
 * C version of the supplied Python search for A400781.
 *
 * Build: xcrun clang -O3 -std=c17 -Wall -Wextra -Wshadow 400781_01.c -o 400781_01_c
 * Run without arguments: n = 1,...,4 with M = 100, as in the Python program.
 * Run one search: ./400781_01_c n M [width]
 * Example for n = 5: ./400781_01_c 5 244
 *
 * Enumerate increasing tuples, group equal sums, and select the first n
 * representations whose bases are pairwise disjoint. Extra representations
 * are permitted. This program does not compute the maximum packing size.
 *
 * Sums are processed in ascending, inclusive intervals to limit memory use.
 * The full range of sums using bases 1,...,M is searched, as in Python.
 * "minimum_proved" also checks whether bases beyond M could affect the result.
 * stdout matches Python's value/representation format; diagnostics use stderr.
 * Integer powers and all prefix sums must fit in uint64_t.
 */

#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_N 6
#define MAX_M 10000
#define DEFAULT_WIDTH (UINT64_C(1) << 32)

typedef uint64_t U;

typedef struct {
    U sum;
    uint16_t bases[3];
} Small;

typedef struct {
    uint16_t bases[MAX_N];
} Representation;

typedef struct {
    Small *data;
    size_t size, capacity;
} SmallVector;

typedef struct {
    int n, m;
    U low, high;
    U *powers, *prefix;
    uint32_t *offsets, *scratch;
    size_t count, capacity, scratch_capacity;
    size_t *positions;
    SmallVector left, right;
    bool tables_ready;
    Representation *representations;
    size_t representation_count, representation_capacity;
    bool *used;
    size_t chosen[MAX_N];
} Search;

static bool fail(const char *message) {
    fprintf(stderr, "%s\n", message);
    return false;
}

static void *reserve(void *data, size_t *capacity, size_t needed, size_t unit) {
    const size_t maximum = SIZE_MAX / unit;
    if (needed > maximum) {
        fail("allocation size overflow");
        return NULL;
    }
    size_t next = *capacity ? *capacity : 1024;
    if (next > maximum) next = maximum;
    while (next < needed) {
        if (next > maximum / 2) {
            next = needed;
            break;
        }
        next *= 2;
    }
    void *result = realloc(data, next * unit);
    if (!result) {
        fail("out of memory");
        return NULL;
    }
    *capacity = next;
    return result;
}

static bool integer_power(unsigned base, int exponent, U *answer) {
    U value = 1;
    for (int i = 0; i < exponent; ++i) {
        if (base && value > UINT64_MAX / base) return false;
        value *= base;
    }
    *answer = value;
    return true;
}

static void destroy_search(Search *s) {
    free(s->powers);
    free(s->prefix);
    free(s->offsets);
    free(s->scratch);
    free(s->positions);
    free(s->left.data);
    free(s->right.data);
    free(s->representations);
    free(s->used);
}

static bool initialize_search(Search *s, int n, int m) {
    memset(s, 0, sizeof(*s));
    if (n < 1 || n > MAX_N || m < 0 || m > MAX_M)
        return fail("require 1<=n<=6 and 0<=M<=10000");
    s->n = n;
    s->m = m;
    const size_t size = (size_t)m + 1;
    s->powers = calloc(size, sizeof(*s->powers));
    s->prefix = calloc(size, sizeof(*s->prefix));
    s->used = calloc(size, sizeof(*s->used));
    if (!s->powers || !s->prefix || !s->used) return fail("out of memory");
    for (int x = 1; x <= m; ++x) {
        U value;
        if (!integer_power((unsigned)x, n, &value)) return fail("power overflow");
        if (s->prefix[x - 1] > UINT64_MAX - value) return fail("prefix overflow");
        s->powers[x] = value;
        s->prefix[x] = s->prefix[x - 1] + value;
    }
    return true;
}

static int lower_power(const Search *s, int first, int end, U value) {
    while (first < end) {
        const int middle = first + (end - first) / 2;
        if (s->powers[middle] < value) first = middle + 1;
        else end = middle;
    }
    return first;
}

static int upper_power(const Search *s, int first, int end, U value) {
    while (first < end) {
        const int middle = first + (end - first) / 2;
        if (s->powers[middle] <= value) first = middle + 1;
        else end = middle;
    }
    return first;
}

static bool append_offset(Search *s, U value) {
    if (value < s->low || value > s->high || value - s->low > UINT32_MAX)
        return fail("internal sum interval mismatch");
    if (s->count == SIZE_MAX) return fail("record count overflow");
    if (s->count == s->capacity) {
        void *data = reserve(s->offsets, &s->capacity, s->count + 1,
                             sizeof(*s->offsets));
        if (!data) return false;
        s->offsets = data;
    }
    s->offsets[s->count++] = (uint32_t)(value - s->low);
    return true;
}

static bool enumerate(Search *s, int start, int remaining, U partial) {
    if (start + remaining - 1 > s->m) return true;
    /* Even the largest remaining bases cannot reach the interval. */
    if (partial + (s->prefix[s->m] - s->prefix[s->m - remaining]) < s->low)
        return true;
    if (remaining == 1) {
        const int end = upper_power(s, start, s->m + 1, s->high - partial);
        const U need = s->low > partial ? s->low - partial : 0;
        const int first = lower_power(s, start, end, need);
        for (int x = first; x < end; ++x)
            if (!append_offset(s, partial + s->powers[x])) return false;
        return true;
    }
    const U tail = s->prefix[s->m] - s->prefix[s->m - remaining + 1];
    const U need = s->low > partial + tail ? s->low - partial - tail : 0;
    start = lower_power(s, start, s->m + 1, need);
    for (int x = start; x + remaining - 1 <= s->m; ++x) {
        /* Every completion uses at least x,...,x+remaining-1. */
        if (s->prefix[x + remaining - 1] - s->prefix[x - 1] > s->high - partial)
            break;
        if (!enumerate(s, x + 1, remaining - 1, partial + s->powers[x]))
            return false;
    }
    return true;
}

static bool sort_offsets(Search *s) {
    if (s->count < 2) return true;
    if (s->scratch_capacity < s->count) {
        void *data = reserve(s->scratch, &s->scratch_capacity, s->count,
                             sizeof(*s->scratch));
        if (!data) return false;
        s->scratch = data;
    }
    if (!s->positions) {
        s->positions = calloc(65536, sizeof(*s->positions));
        if (!s->positions) return fail("out of memory");
    }
    uint32_t *input = s->offsets, *output = s->scratch;
    for (unsigned shift = 0; shift <= 16; shift += 16) {
        memset(s->positions, 0, 65536 * sizeof(*s->positions));
        for (size_t i = 0; i < s->count; ++i)
            ++s->positions[(input[i] >> shift) & 65535U];
        size_t offset = 0;
        for (size_t i = 0; i < 65536; ++i) {
            const size_t next = offset + s->positions[i];
            s->positions[i] = offset;
            offset = next;
        }
        for (size_t i = 0; i < s->count; ++i)
            output[s->positions[(input[i] >> shift) & 65535U]++] = input[i];
        uint32_t *temporary = input;
        input = output;
        output = temporary;
    }
    return true;
}

static bool small_tuples(Search *s, int start, int remaining, U partial,
                         uint16_t bases[3], int depth, SmallVector *out) {
    if (!remaining) {
        if (out->size == SIZE_MAX) return fail("tuple count overflow");
        if (out->size == out->capacity) {
            void *data = reserve(out->data, &out->capacity, out->size + 1,
                                 sizeof(*out->data));
            if (!data) return false;
            out->data = data;
        }
        Small row = {0};
        row.sum = partial;
        memcpy(row.bases, bases, (size_t)depth * sizeof(*bases));
        out->data[out->size++] = row;
        return true;
    }
    for (int x = start; x + remaining - 1 <= s->m; ++x) {
        bases[depth] = (uint16_t)x;
        if (!small_tuples(s, x + 1, remaining - 1, partial + s->powers[x],
                          bases, depth + 1, out)) return false;
    }
    return true;
}

static int compare_small(const void *a, const void *b) {
    const U x = ((const Small *)a)->sum, y = ((const Small *)b)->sum;
    return (x > y) - (x < y);
}

static int compare_representation(const void *a, const void *b) {
    const Representation *x = a, *y = b;
    for (int i = 0; i < MAX_N; ++i) {
        if (x->bases[i] != y->bases[i])
            return (x->bases[i] > y->bases[i]) - (x->bases[i] < y->bases[i]);
    }
    return 0;
}

static bool build_tables(Search *s) {
    uint16_t bases[3] = {0};
    const int a = s->n / 2, b = s->n - a;
    if (!small_tuples(s, 1, a, 0, bases, 0, &s->left) ||
        !small_tuples(s, 1, b, 0, bases, 0, &s->right)) return false;
    if (s->left.size > 1)
        qsort(s->left.data, s->left.size, sizeof(*s->left.data), compare_small);
    if (s->right.size > 1)
        qsort(s->right.data, s->right.size, sizeof(*s->right.data), compare_small);
    s->tables_ready = true;
    return true;
}

static bool choose_disjoint(Search *s, size_t first, int depth) {
    if (depth == s->n) return true;
    if (s->representation_count - first < (size_t)(s->n - depth)) return false;
    for (size_t j = first; j < s->representation_count; ++j) {
        const Representation *row = &s->representations[j];
        bool disjoint = true;
        for (int k = 0; k < s->n; ++k)
            if (s->used[row->bases[k]]) { disjoint = false; break; }
        if (!disjoint) continue;
        for (int k = 0; k < s->n; ++k) s->used[row->bases[k]] = true;
        s->chosen[depth] = j;
        if (choose_disjoint(s, j + 1, depth + 1)) return true;
        for (int k = 0; k < s->n; ++k) s->used[row->bases[k]] = false;
    }
    return false;
}

static bool check_sum(Search *s, U target, size_t expected, bool *found) {
    *found = false;
    if (!s->tables_ready && !build_tables(s)) return false;
    s->representation_count = 0;
    memset(s->used, 0, ((size_t)s->m + 1) * sizeof(*s->used));
    const int a = s->n / 2, b = s->n - a;
    for (size_t i = 0; i < s->left.size; ++i) {
        const Small *left = &s->left.data[i];
        if (left->sum >= target) break;
        const U need = target - left->sum;
        size_t first = 0, end = s->right.size;
        while (first < end) {
            const size_t middle = first + (end - first) / 2;
            if (s->right.data[middle].sum < need) first = middle + 1;
            else end = middle;
        }
        for (size_t j = first; j < s->right.size && s->right.data[j].sum == need; ++j) {
            const Small *right = &s->right.data[j];
            /* Every increasing tuple has exactly one split at position a. */
            if (a && left->bases[a - 1] >= right->bases[0]) continue;
            if (s->representation_count == SIZE_MAX) return fail("representation count overflow");
            if (s->representation_count == s->representation_capacity) {
                void *data = reserve(s->representations, &s->representation_capacity,
                                     s->representation_count + 1,
                                     sizeof(*s->representations));
                if (!data) return false;
                s->representations = data;
            }
            Representation row = {0};
            memcpy(row.bases, left->bases, (size_t)a * sizeof(*row.bases));
            memcpy(row.bases + a, right->bases, (size_t)b * sizeof(*row.bases));
            s->representations[s->representation_count++] = row;
        }
    }
    if (s->representation_count != expected) return fail("representation count mismatch");
    /* Match itertools.combinations order before choosing the first witness. */
    if (s->representation_count > 1)
        qsort(s->representations, s->representation_count,
              sizeof(*s->representations), compare_representation);
    *found = choose_disjoint(s, 0, 0);
    return true;
}

static bool minimum_proved(const Search *s, U value) {
    U outside;
    if (!integer_power((unsigned)s->m + 1, s->n, &outside)) return true;
    const U other_terms = s->prefix[s->n - 1];
    if (outside > UINT64_MAX - other_terms) return true;
    /* Any representation using a base beyond M has at least this sum. */
    return value < outside + other_terms;
}

static bool emit_result(const Search *s, U value) {
    if (printf("%" PRIu64 "\n", value) < 0) return fail("error writing standard output");
    for (int i = 0; i < s->n; ++i) {
        const Representation *row = &s->representations[s->chosen[i]];
        for (int k = 0; k < s->n; ++k) {
            if (printf("%s%u^%d", k ? " + " : "", (unsigned)row->bases[k], s->n) < 0)
                return fail("error writing standard output");
        }
        if (printf(" = %" PRIu64 "\n", value) < 0) return fail("error writing standard output");
    }
    if (fflush(stdout) != 0) return fail("error writing standard output");
    if (fprintf(stderr, "result n=%d N=%" PRIu64
                " representations=%zu (bases 1..%d) selected=%d minimum_proved=%d\n",
                s->n, value, s->representation_count, s->m, s->n,
                (int)minimum_proved(s, value)) < 0 || fflush(stderr) != 0)
        return false;
    return true;
}

static bool find(Search *s, U width) {
    if (!width || width > DEFAULT_WIDTH) return fail("require 1<=width<=2^32");
    if (s->m < s->n) {
        return fprintf(stderr, "no solution with bases 1..%d for n=%d\n", s->m, s->n) >= 0;
    }
    const U maximum = s->prefix[s->m] - s->prefix[s->m - s->n];
    if (fprintf(stderr, "n=%d M=%d sum_range=[0,%" PRIu64 "]\n", s->n, s->m, maximum) < 0)
        return false;
    U total = 0;
    for (s->low = 0;;) {
        s->high = maximum - s->low >= width - 1 ? s->low + width - 1 : maximum;
        s->count = 0;
        if (!enumerate(s, 1, s->n, 0) || !sort_offsets(s)) return false;
        if ((U)s->count > UINT64_MAX - total) return fail("record count overflow");
        total += (U)s->count;
        for (size_t i = 0; i < s->count;) {
            size_t j = i + 1;
            while (j < s->count && s->offsets[i] == s->offsets[j]) ++j;
            if (j - i >= (size_t)s->n) {
                bool found;
                const U value = s->low + s->offsets[i];
                if (!check_sum(s, value, j - i, &found)) return false;
                if (found) return emit_result(s, value);
            }
            i = j;
        }
        if (fprintf(stderr, "completed [%" PRIu64 ",%" PRIu64
                    "] records=%zu total=%" PRIu64 "\n",
                    s->low, s->high, s->count, total) < 0) return false;
        if (s->high == maximum) break;
        s->low = s->high + 1;
    }
    return fprintf(stderr, "no solution with bases 1..%d for n=%d\n", s->m, s->n) >= 0;
}

static bool parse_unsigned(const char *text, U *answer) {
    if (*text < '0' || *text > '9') return false;
    errno = 0;
    char *end;
    const uintmax_t value = strtoumax(text, &end, 10);
    if (errno == ERANGE || *end || value > UINT64_MAX) return false;
    *answer = (U)value;
    return true;
}

static bool run_one(int n, int m, U width) {
    Search search;
    const bool initialized = initialize_search(&search, n, m);
    const bool ok = initialized && find(&search, width);
    destroy_search(&search);
    return ok;
}

int main(int argc, char **argv) {
    bool ok = true;
    if (argc == 1) {
        for (int n = 1; n < 5 && ok; ++n) ok = run_one(n, 100, DEFAULT_WIDTH);
    } else if (argc == 3 || argc == 4) {
        U n, m, width = DEFAULT_WIDTH;
        if (!parse_unsigned(argv[1], &n) || !parse_unsigned(argv[2], &m) ||
            (argc == 4 && !parse_unsigned(argv[3], &width)) || n > INT_MAX || m > INT_MAX) {
            fail("invalid unsigned integer argument");
            return EXIT_FAILURE;
        }
        ok = run_one((int)n, (int)m, width);
    } else {
        fail("usage: 400781_01_c [n M [width]]");
        return EXIT_FAILURE;
    }
    if (fflush(stdout) != 0 || ferror(stdout)) ok = false;
    if (fflush(stderr) != 0 || ferror(stderr)) ok = false;
    return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}
