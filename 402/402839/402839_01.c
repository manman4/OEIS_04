/*
 * A402839 -- Erdos Problem 319.
 * Maximum number of terms in a sum of signed unit fractions with distinct
 * denominators in {1,...,n} that equals zero and has no nonempty proper
 * subsum equal to zero. Signs stay fixed when a subsum is selected.
 * The empty sum is permitted, so the answer can be zero.
 *
 * Usage: ./402839_01 [N]   (default 40; 1 <= N <= 80).
 * Compute every term from n=1 to N; print and flush each completed term as
 * "0, 0, 0, 0, 0, 4, ...", with one final newline. No stored answers are
 * used and no files are read or written. There is no automatic timeout.
 * SIGINT/SIGTERM stop the search; incomplete terms are never printed.
 *
 * Exact algorithm and proofs:
 * (1) L=lcm(1,...,n), w_j=L/j. Multiplication by positive L shows that
 *     sum c_j/j=0 iff sum c_j*w_j=0 for c_j in {-1,0,1}.
 * (2) For every prime p and p^k<=n, let T={j:p^k divides j} and
 *     m=p^(v_p(L)-k+1). Every weight outside T is divisible by m.
 *     A zero relation must therefore have sum_{j in T} c_j*w_j=0 mod m.
 *     Check this only after ALL coefficients in T have been assigned.
 * (3) The absolute change attainable from unassigned terms is at most the
 *     sum of their positive weights. If this cannot cancel the current
 *     sum, discard the branch. If the nonzero count plus the number of
 *     remaining coefficients cannot exceed the best proven support, the
 *     branch cannot improve the answer and can also be discarded.
 * (4) A relation and its negative have the same support and minimality.
 *     Requiring the first nonzero coefficient to be positive keeps exactly
 *     one of the two and loses no possible support size.
 * (5) For a zero relation, test ALL in/out choices on its support, keeping
 *     its signs fixed. It is minimal exactly when no nonempty proper
 *     choice sums to zero. The divisibility and remaining-weight tests
 *     in (2),(3) hold for such subrelations as well. Both empty and full
 *     choices are excluded explicitly; no assumption about minimality
 *     is used to prune this test. Enumerating every candidate and taking
 *     the largest support of a minimal relation gives the exact answer.
 *
 * Arithmetic and memory bounds (supported range, not a speed promise):
 * L_80=32433859254793982911622772305630400 < 2^115. This is the product of
 * the largest powers <=80 of each prime <=80, checked by trial division.
 * L_n divides L_80, so every weight, partial sum, remainder sum and sum
 * over a T has absolute value <=80*L_80 < 2^122 < 2^127. The lcm update
 * (L/gcd(L,j))*j is also <=L_80; signed 128-bit arithmetic cannot overflow.
 * Negation is safe since none of these sums is the minimum signed value.
 * Prime powers and their moduli are <=80 (the final unused pk update is
 * <=80^2). There is at most one T per prime power in {2,...,80}, hence
 * fewer than MAXT=80 sets. All element indices are in 1..n<=80, and all
 * depth indices in 0..n. Recursive depth is at most n+1. Storage is fixed;
 * no search-node counter, large table, dynamic allocation or bit shift
 * is needed. Small loop products such as q*q are also <=81 here.
 * Input is checked before setup. An interrupted search does not publish
 * its current lower bound as a completed term.
 *
 * Build (Clang or GCC with __int128; no external library):
 * cc -O3 -std=c11 -Wall -Wextra -Wpedantic -Wconversion -Wshadow -Werror \
 *    402839_01.c -o 402839_01
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <limits.h>
#include <signal.h>
#include <string.h>

#if !defined(__SIZEOF_INT128__) || __SIZEOF_INT128__ != 16
#error "This program requires a compiler with 128-bit integer support."
#endif
__extension__ typedef __int128 i128;

#define MAXN 80
#define MAXT MAXN

static int N, ORD[MAXN];      /* ORD[i] = element fixed at depth i */
static i128 W[MAXN + 1];       /* weight of element j */
static i128 REM[MAXN + 1];     /* REM[i] = sum of weights of ORD[i..N-1] */
static int NT;                /* number of (p, k) sets */
static i128 TMOD[MAXT];
static int TLAST[MAXT];       /* depth of the last element of the set */
static unsigned char INT_[MAXT][MAXN + 1]; /* membership by element */
static int BEST;
static int C[MAXN + 1];       /* coefficient by element */
static volatile sig_atomic_t interrupted;

static void handle_signal(int sig) { interrupted = sig; }


/* lemma (V) at depth d for the coefficient function coef(j) */
static int sets_ok(int d, const int *coef)
{
    for (int t = 0; t < NT; t++) {
        if (TLAST[t] != d)
            continue;
        i128 s = 0;
        for (int j = 1; j <= N; j++)
            if (INT_[t][j])
                s += coef[j] * W[j];
        if (s % TMOD[t] != 0)
            return 0;
    }
    return 1;
}

/* minimality: is there a subset of the support (not empty, not all) with zero sum? */
static int SUB[MAXN + 1];
static int sub_dfs(int d, i128 sum, int inside, int outside)
{
    if (interrupted) return 0;
    if (d == N)
        return sum == 0 && inside > 0 && outside > 0;
    int j = ORD[d];
    if (C[j] == 0) {
        SUB[j] = 0;
        if (!sets_ok(d, SUB))
            return 0;
        return sub_dfs(d + 1, sum, inside, outside);
    }
    i128 rest = 0;
    for (int e = d + 1; e < N; e++)
        if (C[ORD[e]])
            rest += W[ORD[e]];
    for (int pick = 0; pick <= 1; pick++) {
        SUB[j] = pick ? C[j] : 0;
        i128 s2 = sum + SUB[j] * W[j];
        if (s2 > rest || -s2 > rest)
            continue;
        if (!sets_ok(d, SUB))
            continue;
        if (sub_dfs(d + 1, s2, inside + pick, outside + !pick))
            return 1;
    }
    return 0;
}

static void dfs(int d, i128 sum, int nonzero, int seen_nonzero)
{
    if (interrupted) return;
    if (nonzero + (N - d) <= BEST)
        return;
    if (d == N) {
        if (sum != 0 || nonzero <= BEST)
            return;
        if (sub_dfs(0, 0, 0, 0) || interrupted)
            return; /* not minimal, or the computation was interrupted */
        BEST = nonzero;
        return;
    }
    int j = ORD[d];
    for (int c = -1; c <= 1; c++) {
        if (!seen_nonzero && c == -1)
            continue; /* first nonzero coefficient is +1 */
        C[j] = c;
        i128 s2 = sum + c * W[j];
        if (s2 > REM[d + 1] || -s2 > REM[d + 1])
            continue;
        if (!sets_ok(d, C))
            continue;
        dfs(d + 1, s2, nonzero + (c != 0), seen_nonzero || c != 0);
    }
    C[j] = 0;
}

static void setup(int n)
{
    N = n;
    i128 L = 1;
    for (int j = 2; j <= n; j++) {
        i128 a = L, b = j;
        while (b) { i128 t = a % b; a = b; b = t; }
        L = L / a * j;
    }
    for (int j = 1; j <= n; j++)
        W[j] = L / j;
    for (int i = 0; i < n; i++)
        ORD[i] = n - i; /* descending denominators */
    int pos[MAXN + 1];
    for (int i = 0; i < n; i++)
        pos[ORD[i]] = i;
    REM[n] = 0;
    for (int i = n - 1; i >= 0; i--)
        REM[i] = REM[i + 1] + W[ORD[i]];
    NT = 0;
    for (int p = 2; p <= n; p++) {
        int prime = 1;
        for (int q = 2; q * q <= p; q++)
            if (p % q == 0)
                prime = 0;
        if (!prime)
            continue;
        i128 Lp = L;
        int vl = 0;
        while (Lp % p == 0) { Lp /= p; vl++; }
        i128 pk = p;
        for (int k = 1; k <= vl; k++, pk *= p) {
            if (NT >= MAXT) { fprintf(stderr, "too many sets\n"); exit(2); }
            i128 m = 1;
            for (int i = 0; i < vl - k + 1; i++)
                m *= p;
            int last = -1;
            for (int j = 1; j <= n; j++) {
                INT_[NT][j] = (j % pk == 0);
                if (INT_[NT][j] && pos[j] > last)
                    last = pos[j];
            }
            TMOD[NT] = m;
            TLAST[NT] = last;
            NT++;
        }
    }
}

static int parse_limit(const char *text, int *value)
{
    if (*text == '\0') return 0;
    for (const char *p = text; *p; ++p)
        if (*p < '0' || *p > '9') return 0;
    errno = 0;
    char *end = NULL;
    long v = strtol(text, &end, 10);
    if (errno == ERANGE || end == NULL || *end || v < 1 || v > MAXN) return 0;
    *value = (int)v;
    return 1;
}

int main(int argc, char **argv)
{
    int limit = 40;
    if (argc == 2 && (!strcmp(argv[1], "--help") || !strcmp(argv[1], "-h"))) {
        if (printf("Usage: %s [N] (default 40; 1 <= N <= %d)\n", argv[0], MAXN) < 0 || fflush(stdout) != 0) return 1;
        return 0;
    }
    if (argc > 2 || (argc == 2 && !parse_limit(argv[1], &limit))) {
        fprintf(stderr, "Usage: %s [N]; N must be a decimal integer in 1..%d.\n", argv[0], MAXN);
        return 1;
    }
    if (signal(SIGINT, handle_signal) == SIG_ERR || signal(SIGTERM, handle_signal) == SIG_ERR) {
        perror("signal");
        return 1;
    }
    for (int n = 1; n <= limit && !interrupted; ++n) {
        setup(n);
        BEST = 0;
        memset(C, 0, sizeof(C));
        memset(SUB, 0, sizeof(SUB));
        dfs(0, 0, 0, 0);
        if (interrupted) break;
        if (printf(n == 1 ? "%d" : ", %d", BEST) < 0 || fflush(stdout) != 0) {
            perror("write standard output");
            return 1;
        }
    }
    if (printf("\n") < 0 || fflush(stdout) != 0) {
        perror("write standard output");
        return 1;
    }
    if (interrupted) {
        fprintf(stderr, "Stopped; output contains only completed terms.\n");
        return interrupted == SIGINT ? 130 : 143;
    }
    return 0;
}
