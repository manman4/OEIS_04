/*
 * A402761 (Erdos Problem 543): f(N) = least k such that, for every abelian
 * group G of order N, a uniformly random k-element subset A of G has every
 * element of G as a subset sum (the empty sum being 0) with probability at
 * least 1/2.  Exact integer counts, N <= 64.
 *
 * Representation.  G = Z/d_1 x ... x Z/d_r with d_1 | d_2 | ... | d_r (every
 * abelian group of order N appears once, by the invariant factor theorem).
 * The element with coordinates (x_1, ..., x_r) has index
 * x_1 + d_1 (x_2 + d_2 (x_3 + ...)), and a set of elements is a 64-bit mask.
 * Translation by e acts on each coordinate separately; on coordinate i with
 * t = e_i != 0 it moves an index with x_i < d_i - t up by t*s_i and the others
 * down by (d_i - t)*s_i, where s_i = d_1 ... d_{i-1}.  So S + e is a
 * composition of r masked shifts.  All shift widths are at most N - 1 <= 63.
 * --selftest checks S + e on every singleton against coordinate addition.
 *
 * Counting.  For B a subset of G, let Sigma(B) be its set of subset sums.
 *   (Z) For 0 not in B, Sigma(B + {0}) = Sigma(B), since adding 0 to a sum does
 *       not change it.  Hence the number of covering k-subsets of G is
 *       c_k + c_{k-1}, where c_k counts covering k-subsets of G \ {0}.
 *   (M) Sigma is monotone: B' subset of B implies Sigma(B') subset of Sigma(B).
 *       Sigma(B + {e}) = Sigma(B) u (Sigma(B) + e).
 *   (F) The search lists subsets of G \ {0} as increasing index sequences.
 *       A k-subset B covers iff some prefix of it covers (B is its own prefix;
 *       by (M) a covering prefix makes B cover).  Let j be the length of the
 *       shortest covering prefix.  All shorter prefixes do not cover, so the
 *       search expands them and reaches the length-j prefix, ending in e; there
 *       it adds binom(N-1-e, k-j) to c_k for every k: the number of k-subsets
 *       with exactly this prefix (the other k - j elements have index > e).
 *       Distinct shortest prefixes give disjoint families, so every covering
 *       k-subset is counted exactly once and no other subset is counted.
 *   (P) |Sigma(B + {e})| <= 2 |Sigma(B)|.  So a non-covering prefix with j
 *       elements and |Sigma| * 2^(K-j) < N has no covering extension with at
 *       most K elements; it is not expanded.  Prefixes of length K are not
 *       expanded either.  By (F) every covering k-subset with k <= K has its
 *       shortest covering prefix of length <= k <= K, reached without passing
 *       a cut prefix (a cut prefix has no covering extension of size <= K, but
 *       its extension to that k-subset covers).  So c_k is exact for k <= K.
 * The threshold of G is the least k with 2 (c_k + c_{k-1}) >= binom(N, k).
 * K starts at the least k with 2^k >= N and grows by one until the threshold
 * is found (for k with 2^k < N no subset covers, because |Sigma| <= 2^k).
 * No symmetry, cache, known value or b-file is used.
 *
 * Arithmetic: binom(n, k) <= binom(64, 32) < 2^61, so the counts, and twice
 * the counts, fit in uint64_t.
 *
 * The probability of covering is nondecreasing in k: extend a uniformly
 * chosen k-subset by a uniformly chosen missing element. The resulting
 * (k+1)-subset is uniform and a covering subset stays covering. Therefore
 * the answer for order N is the maximum of the individual group thresholds.
 *
 * Bounds: the Pascal additions are at most binom(64,32) < 2^61. Counts
 * accumulate disjoint families and have the same bound; their double is
 * below 2^62. Each dfs call represents a distinct subset of at most 63
 * nonzero elements, so NODES <= 2^63 per count_all call (including its root).
 * Products/indices in group setup are at most 64; recursion depth <= 64.
 * No random sampling, floating-point probability, or saved terms are used.
 * Empty subset sums include 0; consequently f(1) = 0.
 *
 * Adapted from the independently written, audited calculation for Problem
 * 543, retaining its counting algorithm. No external source code is used.
 *
 * Build: cc -O3 -std=c11 -Wall -Wextra -Wpedantic -Wconversion -Wshadow
 *           -Werror 402761_01.c -o 402761_01
 * Usage:
 *   ./402761_01 NMAX       print f(1), ..., f(NMAX) as they finish, then
 *                         repeat the complete list on its own final line.
 *                         1 <= NMAX <= 64. Progress goes to stderr.
 *                         No files are written.
 *   ./402761_01 --counts N K   exact covering-subset counts for k=0..min(K,N)
 *   ./402761_01 --selftest     test addition in every group of order 1..64
 * Runtime grows rapidly near the upper end; 64 is a representation limit,
 * not a promise of a quick run. There is no automatic time limit.
 */
#define _POSIX_C_SOURCE 200809L
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 64
#define MAXR 6

typedef uint64_t u64;

static u64 C[MAXN + 1][MAXN + 1];

static int N, R;
static int D[MAXR], STRIDE[MAXR];
static u64 FULL;
/* per element e: the masked shifts of its non-zero coordinates */
static int NOPS[MAXN];
static u64 OPLOW[MAXN][MAXR];
static int OPUP[MAXN][MAXR], OPDOWN[MAXN][MAXR];

static int K;
static u64 CNT[MAXN + 1];
static u64 NODES;

static void binomials(void)
{
    for (int n = 0; n <= MAXN; n++) {
        C[n][0] = 1;
        for (int k = 1; k <= n; k++)
            C[n][k] = C[n - 1][k - 1] + (k <= n - 1 ? C[n - 1][k] : 0);
    }
}

static int coord(int x, int i) { return (x / STRIDE[i]) % D[i]; }

static void setup_group(int n, int r, const int *d)
{
    if (n < 1 || n > MAXN || r < 0 || r > MAXR) {
        fprintf(stderr, "internal error: group bounds\n");
        exit(3);
    }
    N = n;
    R = r;
    FULL = (n == 64) ? ~(u64)0 : (((u64)1 << n) - 1);
    int s = 1;
    for (int i = 0; i < r; i++) {
        if (d[i] < 2 || d[i] > n / s ||
            (i > 0 && d[i] % d[i - 1] != 0)) {
            fprintf(stderr, "internal error: invariant factors\n");
            exit(3);
        }
        D[i] = d[i];
        STRIDE[i] = s;
        s *= d[i];
    }
    if (s != n) {
        fprintf(stderr, "factors do not multiply to %d\n", n);
        exit(2);
    }
    for (int e = 0; e < n; e++) {
        NOPS[e] = 0;
        for (int i = 0; i < r; i++) {
            int t = coord(e, i);
            if (t == 0)
                continue;
            u64 low = 0;
            for (int x = 0; x < n; x++)
                if (coord(x, i) < D[i] - t)
                    low |= (u64)1 << x;
            OPLOW[e][NOPS[e]] = low;
            OPUP[e][NOPS[e]] = t * STRIDE[i];
            OPDOWN[e][NOPS[e]] = (D[i] - t) * STRIDE[i];
            NOPS[e]++;
        }
    }
}

static inline u64 translate(u64 S, int e)
{
    for (int k = 0; k < NOPS[e]; k++) {
        u64 low = OPLOW[e][k];
        S = ((S & low) << OPUP[e][k]) | ((S & ~low) >> OPDOWN[e][k]);
    }
    return S;
}

static void dfs(u64 S, int last, int j)
{
    NODES++;
    if (j == K)
        return;
    /* (P); for K - j >= 7 the bound is at least 2^7 > 64 >= N (shift kept < 64) */
    if (K - j < 7 && ((u64)__builtin_popcountll(S) << (K - j)) < (u64)N)
        return;
    for (int e = last + 1; e < N; e++) {
        u64 T = S | translate(S, e);
        if (T == FULL) {
            int rem = N - 1 - e;
            for (int k = j + 1; k <= j + 1 + rem && k <= K; k++)
                CNT[k] += C[rem][k - j - 1];
        } else {
            dfs(T, e, j + 1);
        }
    }
}

/* covering k-subsets of G for k = 0..K into tot[] (valid for k <= K) */
static void count_all(int kmax, u64 *tot)
{
    K = kmax;
    memset(CNT, 0, sizeof CNT);
    NODES = 0;
    if (FULL == 1) { /* N = 1: the empty set already covers */
        CNT[0] = 1;
    } else {
        dfs(1, 0, 0);
    }
    tot[0] = CNT[0];
    for (int k = 1; k <= kmax; k++)
        tot[k] = CNT[k] + CNT[k - 1];
}

static void factors_str(char *buf, size_t len)
{
    buf[0] = 0;
    if (R == 0) {
        snprintf(buf, len, "1");
        return;
    }
    for (int i = 0; i < R; i++) {
        size_t u = strlen(buf);
        snprintf(buf + u, len - u, i ? "x%d" : "%d", D[i]);
    }
}

typedef void (*group_fn)(int n, int r, const int *d, void *ctx);

static void groups_rec(int n, int rest, int prev, int r, int *d, group_fn fn, void *ctx)
{
    if (rest == 1) {
        fn(n, r, d, ctx);
        return;
    }
    if (r >= MAXR) {
        fprintf(stderr, "internal error: too many invariant factors\n");
        exit(3);
    }
    for (int x = 2; x <= rest; x++) {
        if (x % prev == 0 && rest % x == 0) {
            d[r] = x;
            groups_rec(n, rest / x, x, r + 1, d, fn, ctx);
        }
    }
}

static void for_groups(int n, group_fn fn, void *ctx)
{
    int d[MAXR];
    groups_rec(n, n, 1, 0, d, fn, ctx);
}

static int threshold(int n, int r, const int *d, u64 *count_out)
{
    setup_group(n, r, d);
    u64 tot[MAXN + 1];
    int k0 = 0;
    while (((u64)1 << k0) < (u64)n)
        k0++;
    for (int kmax = k0; kmax <= n; kmax++) {
        count_all(kmax, tot);
        for (int k = 0; k <= kmax; k++) {
            if (2 * tot[k] >= C[n][k]) {
                *count_out = tot[k];
                return k;
            }
        }
    }
    fprintf(stderr, "no threshold for N=%d\n", n);
    exit(3);
}

static void run_group(int n, int r, const int *d, void *ctx)
{
    int *best = ctx;
    struct timespec t0, t1;
    if (clock_gettime(CLOCK_MONOTONIC, &t0) != 0) {
        perror("clock_gettime");
        exit(3);
    }
    fprintf(stderr, "N=%d: checking group", n);
    for (int i = 0; i < r; i++)
        fprintf(stderr, "%s%d", i == 0 ? " " : "x", d[i]);
    if (r == 0)
        fprintf(stderr, " 1");
    fprintf(stderr, "\n");
    u64 cnt;
    int th = threshold(n, r, d, &cnt);
    if (clock_gettime(CLOCK_MONOTONIC, &t1) != 0) {
        perror("clock_gettime");
        exit(3);
    }
    char buf[64];
    factors_str(buf, sizeof buf);
    fprintf(stderr, "  N=%d G=%s threshold=%d count=%" PRIu64 " binom=%" PRIu64 " nodes=%" PRIu64 " %.2fs\n",
            n, buf, th, cnt, C[n][th], NODES,
            (double)(t1.tv_sec - t0.tv_sec) + 1e-9 * (double)(t1.tv_nsec - t0.tv_nsec));
    if (th > *best)
        *best = th;
}

static int COUNTS_K;
static void counts_group(int n, int r, const int *d, void *ctx)
{
    (void)ctx;
    setup_group(n, r, d);
    int kmax = COUNTS_K < n ? COUNTS_K : n;
    u64 tot[MAXN + 1];
    count_all(kmax, tot);
    char buf[64];
    factors_str(buf, sizeof buf);
    for (int k = 0; k <= kmax; k++)
        if (printf("%d %s %d %" PRIu64 "\n", n, buf, k, tot[k]) < 0) {
            perror("stdout");
            exit(3);
        }
}

static int SELFTEST_BAD;
static void selftest_group(int n, int r, const int *d, void *ctx)
{
    (void)ctx;
    setup_group(n, r, d);
    for (int e = 0; e < n; e++) {
        for (int x = 0; x < n; x++) {
            int y = 0;
            for (int i = 0; i < r; i++)
                y += ((coord(x, i) + coord(e, i)) % D[i]) * STRIDE[i];
            if (translate((u64)1 << x, e) != ((u64)1 << y))
                SELFTEST_BAD++;
        }
        /* a translation is a bijection of the group */
        if (translate(FULL, e) != FULL)
            SELFTEST_BAD++;
    }
}

/* Strict decimal parsing, with a range check before each multiply. */
static int parse_number(const char *s, int minimum, int maximum, int *out)
{
    int v = 0;
    if (*s == '\0')
        return 0;
    for (; *s != '\0'; s++) {
        if (*s < '0' || *s > '9')
            return 0;
        int digit = *s - '0';
        if (v > (maximum - digit) / 10)
            return 0;
        v = 10 * v + digit;
        if (v > maximum)
            return 0;
    }
    if (v < minimum)
        return 0;
    *out = v;
    return 1;
}

static int finish_stdout(void)
{
    if (fflush(stdout) == EOF) {
        perror("stdout");
        return 3;
    }
    return 0;
}

int main(int argc, char **argv)
{
    if (argc == 2 && strcmp(argv[1], "--help") == 0) {
        if (printf("usage: %s NMAX (1..64) | --counts N K (N=1..64, K=0..64) | --selftest\n", argv[0]) < 0)
            return 3;
        return finish_stdout();
    }
    if (argc == 2 && strcmp(argv[1], "--selftest") == 0) {
        binomials();
        for (int n = 1; n <= MAXN; n++)
            for_groups(n, selftest_group, NULL);
        if (SELFTEST_BAD) {
            fprintf(stderr, "selftest FAILED: %d mismatches\n", SELFTEST_BAD);
            return 1;
        }
        if (printf("selftest ok: addition in every abelian group of order 1..64\n") < 0)
            return 3;
        return finish_stdout();
    }
    if (argc == 4 && strcmp(argv[1], "--counts") == 0) {
        int n;
        if (!parse_number(argv[2], 1, MAXN, &n) ||
            !parse_number(argv[3], 0, MAXN, &COUNTS_K)) {
            fprintf(stderr, "need decimal N in 1..64 and K in 0..64\n");
            return 2;
        }
        binomials();
        for_groups(n, counts_group, NULL);
        return finish_stdout();
    }
    int nmax;
    if (argc != 2 || !parse_number(argv[1], 1, MAXN, &nmax)) {
        fprintf(stderr, "usage: %s NMAX (decimal integer 1..64); see --help\n", argv[0]);
        return 2;
    }
    binomials();
    int results[MAXN];
    for (int n = 1; n <= nmax; n++) {
        int best = -1;
        for_groups(n, run_group, &best);
        if (best < 0 || best > n) {
            fprintf(stderr, "internal error: no valid threshold for order %d\n", n);
            return 3;
        }
        results[n - 1] = best;
        if (printf("%s%d", n == 1 ? "" : ", ", best) < 0)
            return 3;
        if (n == nmax && putchar('\n') == EOF)
            return 3;
        if (finish_stdout() != 0)
            return 3;
    }
    /* All entries are initialized only after their exact computations finish.
       Keep the complete sequence after all progress output in a shared terminal. */
    if (fflush(stderr) == EOF)
        return 3;
    for (int n = 1; n <= nmax; n++) {
        if (printf("%s%d", n == 1 ? "" : ", ", results[n - 1]) < 0)
            return 3;
    }
    if (putchar('\n') == EOF)
        return 3;
    return finish_stdout();
}
