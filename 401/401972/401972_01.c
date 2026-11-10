/* Read triangle-free graph6 graphs from stdin. Exact sequence values
   require a complete stream of biconnected graphs through EDGE_LIMIT. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#ifndef EDGE_LIMIT
#define EDGE_LIMIT 20
#endif

_Static_assert(EDGE_LIMIT >= 4 && EDGE_LIMIT <= 31,
               "EDGE_LIMIT must be between 4 and 31");
enum {
    LIMIT = EDGE_LIMIT,
    MAX_LINE = (LIMIT * (LIMIT - 1) / 2 + 5) / 6 + 3
};

static int count_bits(uint32_t value) {
    return __builtin_popcount(value);
}

static void order_vertices(int n, const uint32_t neighbors[LIMIT],
                           uint32_t previous[LIMIT]) {
    int order[LIMIT] = {0};
    uint32_t placed = 0;
    for (int i = 0; i < n; ++i) {
        int selected = -1;
        int best_score = -1;
        for (int v = 0; v < n; ++v) {
            if (placed & (UINT32_C(1) << v)) continue;
            int score = LIMIT * count_bits(neighbors[v] & placed) +
                        count_bits(neighbors[v]);
            if (score > best_score) {
                best_score = score;
                selected = v;
            }
        }
        order[i] = selected;
        placed |= UINT32_C(1) << selected;
        for (int j = 0; j < i; ++j) {
            if (neighbors[selected] & (UINT32_C(1) << order[j]))
                previous[i] |= UINT32_C(1) << j;
        }
    }
}

/* Each monochromatic edge is charged when its second endpoint is placed. */
static int cut_exists(int n, const uint32_t previous[LIMIT], int i,
                      uint32_t side, int budget) {
    if (i == n) return 1;
    const int loss_zero = count_bits(previous[i] & ~side);
    const int loss_one = count_bits(previous[i] & side);
    const uint32_t bit = UINT32_C(1) << i;
    if (loss_one < loss_zero) {
        if (loss_one <= budget &&
            cut_exists(n, previous, i + 1, side | bit, budget - loss_one))
            return 1;
        return loss_zero <= budget &&
               cut_exists(n, previous, i + 1, side, budget - loss_zero);
    }
    if (loss_zero <= budget &&
        cut_exists(n, previous, i + 1, side, budget - loss_zero))
        return 1;
    return loss_one <= budget &&
           cut_exists(n, previous, i + 1, side | bit, budget - loss_one);
}

static int read_core(const char *line, int *n, uint32_t neighbors[LIMIT]) {
    *n = line[0] - '?';
    if (*n < 4 || *n > LIMIT) return -1;
    const int symbols = (*n * (*n - 1) / 2 + 5) / 6;
    if (strlen(line) != (size_t)symbols + 2 || line[symbols + 1] != '\n')
        return -1;
    for (int k = 1; k <= symbols; ++k)
        if (line[k] < '?' || line[k] > '~') return -1;

    int k = 0;
    int m = 0;
    for (int b = 1; b < *n; ++b) {
        for (int a = 0; a < b; ++a, ++k) {
            const unsigned sextet = (unsigned)(line[1 + k / 6] - '?');
            if (!(sextet & (1u << (5 - k % 6)))) continue;
            neighbors[a] |= UINT32_C(1) << b;
            neighbors[b] |= UINT32_C(1) << a;
            ++m;
        }
    }
    return m;
}

int main(void) {
    int best[LIMIT + 1];
    for (int m = 0; m <= LIMIT; ++m) best[m] = m - m / 5;

    unsigned long checked = 0;
    char line[MAX_LINE];
    while (fgets(line, sizeof line, stdin)) {
        uint32_t neighbors[LIMIT] = {0};
        int n;
        const int m = read_core(line, &n, neighbors);
        if (m < 0 || m < n || m > LIMIT) {
            fprintf(stderr, "Invalid graph6 row %lu\n", checked + 1);
            return 1;
        }
        uint32_t previous[LIMIT] = {0};
        order_vertices(n, neighbors, previous);
        // Fix the first vertex in part zero by symmetry of the two parts.
        const int prior = best[m];
        while (!cut_exists(n, previous, 1, 0, m - best[m])) --best[m];
        if (best[m] < prior)
            fprintf(stderr, "Witness m=%d v=%d maxcut=%d %s",
                    m, n, best[m], line);
        ++checked;
    }
    if (ferror(stdin) || checked == 0) {
        fputs("Missing or unreadable graph input\n", stderr);
        return 1;
    }

    for (int m = 1; m <= LIMIT; ++m) {
        for (int j = 1; j <= m / 2; ++j) {
            const int combined = best[j] + best[m - j];
            if (combined < best[m]) best[m] = combined;
        }
    }
    for (int m = 0; m <= LIMIT; ++m)
        printf("%s%d", m ? ", " : "", best[m]);
    printf("\n");
    fprintf(stderr, "Checked %lu graphs\n", checked);
    return 0;
}
