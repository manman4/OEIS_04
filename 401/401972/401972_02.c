#define _POSIX_C_SOURCE 200809L

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum {
    MAX_EDGES = 31,
    MAX_LINE = (MAX_EDGES * (MAX_EDGES - 1) / 2 + 5) / 6 + 3
};

static uint32_t bit(int v) {
    return UINT32_C(1) << v;
}

static int degree(uint32_t neighbors) {
    return __builtin_popcount(neighbors);
}

static int read_graph(const char *line, int n, int edges, uint32_t adj[]) {
    const int symbols = (n * (n - 1) / 2 + 5) / 6;
    if (line[0] != '?' + n || strlen(line) != (size_t)symbols + 2 ||
        line[symbols + 1] != '\n')
        return 0;
    for (int i = 1; i <= symbols; ++i)
        if (line[i] < '?' || line[i] > '~') return 0;

    int count = 0;
    int pair = 0;
    for (int v = 1; v < n; ++v) {
        for (int u = 0; u < v; ++u, ++pair) {
            if (!((line[1 + pair / 6] - '?') & (1 << (5 - pair % 6))))
                continue;
            if (adj[u] & adj[v]) return 0;
            adj[u] |= bit(v);
            adj[v] |= bit(u);
            ++count;
        }
    }
    return count == edges;
}

/* Candidate new edges must keep the graph triangle-free and meet min_degree. */
static uint32_t candidate_edges(int n, const uint32_t adj[], int min_degree,
                                uint32_t allowed[]) {
    uint32_t deficit = 0;
    for (int v = 0; v < n; ++v) {
        const int d = degree(adj[v]);
        if (d + 1 < min_degree) return 0;
        if (d < min_degree) deficit |= bit(v);
    }
    if (degree(deficit) > 2) return 0;

    uint32_t active = 0;
    for (int u = 0; u < n; ++u) {
        for (int v = u + 1; v < n; ++v) {
            if ((deficit & ~(bit(u) | bit(v))) ||
                (adj[u] & bit(v)) || (adj[u] & adj[v]))
                continue;
            allowed[u] |= bit(v);
        }
        if (allowed[u]) active |= bit(u);
    }
    return active;
}

static void order_vertices(int n, const uint32_t adj[], int order[],
                           uint32_t previous[]) {
    uint32_t placed = 0;
    for (int i = 0; i < n; ++i) {
        int selected = -1;
        int best_score = -1;
        for (int v = 0; v < n; ++v) {
            if (placed & bit(v)) continue;
            const int score = n * degree(adj[v] & placed) + degree(adj[v]);
            if (score > best_score) {
                best_score = score;
                selected = v;
            }
        }
        order[i] = selected;
        previous[i] = adj[selected] & placed;
        placed |= bit(selected);
    }
}

/* At a leaf, budget is target minus the cut size. Every target-size cut
   rules out each candidate edge crossing it. A larger cut rules out all. */
static void filter_extensions(int n, const int order[], const uint32_t previous[],
                              int i, uint32_t side, int budget,
                              uint32_t allowed[], uint32_t *active) {
    if (i == n) {
        if (budget > 0) {
            *active = 0;
            return;
        }
        for (uint32_t rows = *active; rows; rows &= rows - 1) {
            const int u = __builtin_ctz(rows);
            allowed[u] &= (side & bit(u)) ? side : ~side;
            if (!allowed[u]) *active &= ~bit(u);
        }
        return;
    }

    const uint32_t vertex = bit(order[i]);
    const int loss[] = {degree(previous[i] & ~side), degree(previous[i] & side)};
    const uint32_t next_side[] = {side, side | vertex};
    const int first = loss[1] < loss[0];
    for (int step = 0; step < 2 && *active; ++step) {
        const int choice = first ^ step;
        if (loss[choice] <= budget)
            filter_extensions(n, order, previous, i + 1, next_side[choice],
                              budget - loss[choice], allowed, active);
    }
}

static int try_order(int n, int edges, int lower, int min_degree,
                     int source_min_degree, uint64_t *checked) {
    char command[80];
    const int length = snprintf(command, sizeof command, "geng -q -c -t -d%d %d %d:%d",
                                source_min_degree, n, edges - 1, edges - 1);
    if (length < 0 || (size_t)length >= sizeof command) return -1;
    FILE *input = popen(command, "r");
    if (!input) {
        perror("popen geng");
        return -1;
    }

    int result = 0;
    char line[MAX_LINE];
    while (fgets(line, sizeof line, input)) {
        if (result != 0) continue;
        ++*checked;
        uint32_t adj[MAX_EDGES] = {0};
        if (!read_graph(line, n, edges - 1, adj)) {
            fprintf(stderr, "Invalid graph6 input at %d edges, %d vertices\n",
                    edges - 1, n);
            result = -1;
            continue;
        }

        uint32_t allowed[MAX_EDGES] = {0};
        uint32_t active = candidate_edges(n, adj, min_degree, allowed);
        if (!active) continue;

        int order[MAX_EDGES];
        uint32_t previous[MAX_EDGES];
        order_vertices(n, adj, order, previous);
        filter_extensions(n, order, previous, 1, 0, edges - 1 - lower,
                          allowed, &active);
        if (active) {
            const int u = __builtin_ctz(active);
            const int v = __builtin_ctz(allowed[u]);
            fprintf(stderr, "Witness m=%d: add edge (%d,%d) to %s", edges, u, v, line);
            result = 1;
        }
    }

    const int read_error = ferror(input);
    if (pclose(input) != 0 || read_error) {
        fprintf(stderr, "geng failed at %d edges, %d vertices\n", edges - 1, n);
        return -1;
    }
    return result;
}

static int next_value(int m, const int values[]) {
    const int lower = values[m - 1];
    for (int j = 1; j <= m / 2; ++j)
        if (values[j] + values[m - j] == lower) return lower;

    /* Removing a degree-d vertex leaves a cut that extends by ceil(d/2). */
    int min_degree = 2;
    while (min_degree < m &&
           values[m - min_degree] + (min_degree + 1) / 2 > lower)
        ++min_degree;
    int max_vertices = 2 * m / min_degree;
    int source_min_degree = min_degree - 1;

    /* If adjacent degree-two vertices are impossible, there are at most
       floor(m/2) degree-two vertices since their incident edges are disjoint. */
    if (min_degree == 2 && values[m - 3] + 2 > lower) {
        max_vertices = (2 * m + m / 2) / 3;
        /* Without an edge between higher-degree vertices the graph would
           be bipartite. Delete such an edge to preserve minimum degree 2. */
        source_min_degree = 2;
    }

    uint64_t checked = 0;
    for (int n = 4; n <= max_vertices; ++n) {
        if (n * n / 4 < m) continue; /* Mantel bound for the target graph. */
        fprintf(stderr, "m=%d: testing sources on %d vertices (checked %" PRIu64 ")\n",
                m, n, checked);
        const int result = try_order(n, m, lower, min_degree, source_min_degree,
                                     &checked);
        if (result < 0) return -1;
        if (result > 0) {
            fprintf(stderr, "m=%d: tested %" PRIu64 " source graphs\n", m, checked);
            return lower;
        }
    }
    fprintf(stderr, "m=%d: exhausted %" PRIu64 " source graphs\n", m, checked);
    return lower + 1;
}

int main(int argc, char *argv[]) {
    char *end = NULL;
    const long limit = argc == 2 ? strtol(argv[1], &end, 10) : -1;
    if (argc != 2 || end == argv[1] || *end || limit < 0 || limit > MAX_EDGES) {
        fprintf(stderr, "Usage: %s MAX_EDGES (0..%d)\n", argv[0], MAX_EDGES);
        return EXIT_FAILURE;
    }

    /* A triangle-free graph with at most three edges is a forest. */
    int values[MAX_EDGES + 1] = {0, 1, 2, 3};
    for (int m = 4; m <= limit; ++m) {
        values[m] = next_value(m, values);
        if (values[m] < 0) return EXIT_FAILURE;
        fprintf(stderr, "f(%d)=%d\n", m, values[m]);
    }
    for (int m = 0; m <= limit; ++m)
        printf("%s%d", m == 0 ? "" : ", ", values[m]);
    putchar('\n');
    return fflush(stdout) == EOF ? EXIT_FAILURE : EXIT_SUCCESS;
}
