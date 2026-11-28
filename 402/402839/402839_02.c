/*
 * A402839 -- minimal vanishing sums of distinct signed unit fractions.
 * a(n) is the largest |S|, S subset {1,...,n}, for which fixed signs
 * e_j in {-1,1} give sum e_j/j=0 with no nonempty proper zero subsum.
 * The empty set is allowed. All arithmetic and primality tests are exact.
 *
 * Usage: ./402839_02 [N] (default 40; 1 <= N <= 80).
 * Compute n=1,...,N, printing and flushing each completed term, separated
 * by commas. No input/result files, stored terms or automatic timeout.
 * SIGINT/SIGTERM stop without emitting the term being computed.
 *
 * Proofs of the reductions and bounds:
 * 1. For each prime p, let e be the greatest p-adic valuation among
 *    remaining denominators and q=p^e. Multiplication by their lcm,
 *    followed by reduction modulo p, gives the necessary condition
 *      sum c_j * inverse(j/q modulo p) = 0 modulo p
 *    over denominators having valuation e. For at most six such terms,
 *    enumerate all ternary patterns. Any variable that is zero in every
 *    surviving pattern must be zero in EVERY rational zero relation.
 *    Delete these variables and repeat. Larger groups are left intact.
 *    In particular a unique term of greatest valuation is deleted.
 * 2. L=lcm(remaining denominators), w_j=L/j. Rational zero relations are
 *    exactly ternary integer zero relations sum c_j*w_j=0. All ternary
 *    choices on the remaining denominators are searched. The order is by
 *    decreasing largest prime-power divisor; it changes no feasible set.
 * 3. Unassigned terms change a partial sum by at most their weight sum.
 *    Their contribution is divisible by their weight gcd. Both tests
 *    are necessary conditions only. A support-size upper bound discards
 *    branches unable to beat an already proved lower bound. Negating a
 *    relation preserves its support/minimality; its first nonzero sign
 *    can consequently be fixed to +1.
 * 4. To test a zero relation for minimality, a proper nonempty zero
 *    subrelation can be required to contain its first term: otherwise
 *    its complement does. Exhaustive in/out search on the other terms
 *    therefore suffices. Signed suffix bounds [sum of negatives, sum
 *    of positives] and the suffix gcd are necessary conditions for a
 *    zero completion. A zero chosen prefix is proper if some term has
 *    been omitted or remains to be omitted. The whole relation is
 *    explicitly excluded. No unproved minimality shortcut is used.
 * 5. a(n-1) <= a(n): the same signed fractions remain valid. Thus the
 *    PREVIOUSLY COMPLETED result from this execution is a valid starting
 *    lower bound for n. No external answers are used for pruning.
 *
 * 6. Precompute zero relations of size three and four. Each is minimal:
 *    a proper zero subrelation and its zero complement would require at
 *    least three terms each (one or two distinct unit fractions cannot
 *    sum to zero). These give independently verified lower bounds.
 *    For a longer zero candidate, repeatedly find a proper zero subset
 *    until exhaustive subset search verifies a minimal zero relation.
 *    Its size updates the lower bound before it is cached. A partial
 *    assignment containing a cached relation, with either global sign,
 *    cannot improve this lower bound: equality is already known and a
 *    strict superset is nonminimal. Cache inclusion uses exact two-word
 *    sign masks, not hashes. Forgetting entries when the cache is full
 *    changes speed only; no feasible improving relation is discarded.
 * 7. For n=p^e, e>=1, only denominator n has maximal p-adic valuation,
 *    so a(n)=a(n-1). For n=2p, prime p>=5, denominators p,2p have
 *    coefficients u,v with 2u+v=0 modulo p. Since |2u+v|<=3<p,
 *    u=v=0. Again a(n)=a(n-1), so these terms need no search.
 *
 * Exact 64-bit range proof for n<=80:
 * A prime power q>40 has at most one multiple <=80, namely q itself.
 * If present it is removed by step 1. Every remaining denominator thus
 * has all prime-power factors <=40 and divides lcm(1,...,40), equal to
 * B=5342931457063200 < 2^53. Hence L divides B, all prefix lcm values
 * are <=B, and the total weight is <=80*B < 2^59. Signed sums, suffix
 * bounds, their differences and all tests are within (-2^61,2^61),
 * far inside int64_t. Lcm multiplication is also guarded before use.
 * Negation/absolute value never sees INT64_MIN. Gcd divisors are positive
 * when used; an empty suffix is handled without division by zero.
 * Factoring/order keys and loop counters are <=80, with small trial
 * products <=80 (modular inverse products are <6400). There are <=80 elements, all array indices are in
 * 0..79, and suffix indices in 0..80. The two nested recursive searches
 * each have <=81 frames, <=162 together. Local pattern enumeration
 * has at most seven frames and runs separately during setup. Sign masks
 * use index/64 in 0..1 and shift index%64 in 0..63. Local pattern masks
 * shift only by 0..6. Cache indices are 0..4095 or the sentinel -1.
 * Local modular sums have absolute value <480, their masks use six bits.
 * All storage is fixed. No overflowing node counters or large tables.
 * Input is validated before any setup; interrupted searches publish no
 * incomplete lower bound as an exact term.
 *
 * Build:
 * cc -O3 -std=c11 -Wall -Wextra -Wpedantic -Wconversion -Wshadow -Werror \
 *    402839_02.c -o 402839_02
 */
#include <errno.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 80
#define LCM_BOUND INT64_C(5342931457063200)

static int count, denominator[MAXN], coefficient[MAXN], best;
static int64_t weight[MAXN], remaining[MAXN + 1], remaining_gcd[MAXN + 1];
#define MAX_CACHE 4096
struct ZeroRelation { uint64_t positive[2], negative[2]; int next; };
static struct ZeroRelation cache[MAX_CACHE], recent;
static uint64_t positive[2], negative[2];
static int cache_count, cache_head[MAXN], recent_valid;
static int term_index[MAXN], chosen[MAXN];
static int sub_count;
static int64_t term[MAXN], low[MAXN + 1], high[MAXN + 1], sub_gcd[MAXN + 1];
static volatile sig_atomic_t stopped;

static void on_signal(int sig) { stopped = sig; }

static int64_t gcd64(int64_t a, int64_t b)
{
    while (b != 0) { int64_t r = a % b; a = b; b = r; }
    return a;
}

static int prime(int p)
{
    for (int d = 2; d <= p / d; ++d) if (p % d == 0) return 0;
    return p >= 2;
}

static int valuation(int x, int p)
{
    int v = 0;
    while (x % p == 0) { x /= p; ++v; }
    return v;
}

static int largest_prime_power(int x)
{
    int value = 1;
    for (int p = 2; p <= x / p; ++p) {
        int power = 1;
        while (x % p == 0) { x /= p; power *= p; }
        if (power > value) value = power;
    }
    return x > value ? x : value;
}

/* Enumerate the at most 3^6 local ternary coefficient patterns exactly. */
static void local_patterns(int d, int k, int p, const int *r,
                           int sum, unsigned mask, unsigned *allowed)
{
    if (*allowed == (1U << k) - 1U) return;
    if (d == k) { if (sum % p == 0) *allowed |= mask; return; }
    local_patterns(d + 1, k, p, r, sum, mask, allowed);
    local_patterns(d + 1, k, p, r, sum + r[d], mask | (1U << d), allowed);
    local_patterns(d + 1, k, p, r, sum - r[d], mask | (1U << d), allowed);
}

static int inverse_mod(int a, int p)
{
    for (int b = 1; b < p; ++b) if ((a * b) % p == 1) return b;
    return 0;
}

static int prepare(int n)
{
    int keep[MAXN + 1] = {0}, key[MAXN + 1];
    for (int j = 1; j <= n; ++j) keep[j] = 1;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int p = 2; p <= n; ++p) if (prime(p)) {
            int greatest = 0;
            for (int j = 1; j <= n; ++j) if (keep[j]) {
                int v = valuation(j, p);
                if (v > greatest) greatest = v;
            }
            if (greatest == 0) continue;
            int members[6], residues[6], k = 0, q = 1;
            for (int e = 0; e < greatest; ++e) q *= p;
            for (int j = 1; j <= n; ++j) if (keep[j] && valuation(j, p) == greatest) {
                if (k < 6) {
                    members[k] = j;
                    residues[k] = inverse_mod(j / q, p);
                    if (residues[k] == 0) return 0;
                }
                ++k;
            }
            if (k > 6) continue; /* No conclusion: leave all these variables. */
            unsigned allowed = 0;
            local_patterns(0, k, p, residues, 0, 0, &allowed);
            for (int i = 0; i < k; ++i) if (!(allowed & (1U << i))) {
                keep[members[i]] = 0; changed = 1;
            }
        }
    }
    count = 0;
    int64_t lcm = 1;
    for (int j = 1; j <= n; ++j) if (keep[j]) {
        denominator[count++] = j;
        key[j] = largest_prime_power(j);
        if (LCM_BOUND % j != 0) return 0;
        int64_t a = lcm / gcd64(lcm, j);
        if (a > LCM_BOUND / j) return 0;
        lcm = a * j;
    }
    for (int i = 0; i < count; ++i)
        for (int j = i + 1; j < count; ++j) {
            int a = denominator[i], b = denominator[j];
            if (key[b] > key[a] || (key[b] == key[a] && b > a)) {
                denominator[i] = b; denominator[j] = a;
            }
        }
    for (int i = 0; i < count; ++i) weight[i] = lcm / denominator[i];
    remaining[count] = remaining_gcd[count] = 0;
    for (int i = count; i > 0; --i) {
        int d = i - 1;
        remaining[d] = remaining[d + 1] + weight[d];
        remaining_gcd[d] = gcd64(weight[d], remaining_gcd[d + 1]);
    }
    memset(coefficient, 0, sizeof(coefficient));
    return 1;
}

static void set_bit(uint64_t *mask, int i)
{
    mask[i / 64] |= UINT64_C(1) << (i % 64);
}

static void set_coefficient(int i, int c)
{
    uint64_t bit = UINT64_C(1) << (i % 64);
    positive[i / 64] &= ~bit; negative[i / 64] &= ~bit;
    if (c > 0) positive[i / 64] |= bit;
    if (c < 0) negative[i / 64] |= bit;
    coefficient[i] = c;
}

static int contains_relation(const struct ZeroRelation *r)
{
    int same = 1, reverse = 1;
    for (int k = 0; k < 2; ++k) {
        if ((positive[k] & r->positive[k]) != r->positive[k] ||
            (negative[k] & r->negative[k]) != r->negative[k]) same = 0;
        if ((positive[k] & r->negative[k]) != r->negative[k] ||
            (negative[k] & r->positive[k]) != r->positive[k]) reverse = 0;
    }
    return same || reverse;
}

static void remember(struct ZeroRelation r, int last)
{
    recent = r; recent_valid = 1;
    if (cache_count == MAX_CACHE) return; /* Forgetting affects speed only. */
    r.next = cache_head[last]; cache[cache_count] = r;
    cache_head[last] = cache_count++;
}

/* Every zero relation with 3 or 4 distinct denominators is minimal. */
static void add_small(int a, int b, int c, int d, int arity, int signs)
{
    if (arity != 3 && arity != 4) abort(); /* Internal caller invariant. */
    struct ZeroRelation r = {{0,0},{0,0},-1};
    int indices[4] = {a,b,c,d};
    set_bit(r.positive, a);
    for (int j = 1; j < arity; ++j)
        set_bit(signs & (1 << (j - 1)) ? r.negative : r.positive, indices[j]);
    if (arity > best) best = arity;
    remember(r, indices[arity - 1]);
}

static void build_cache(void)
{
    cache_count = recent_valid = 0;
    positive[0] = positive[1] = negative[0] = negative[1] = 0;
    for (int d = 0; d < count; ++d) cache_head[d] = -1;
    for (int a = 0; a < count && !stopped; ++a)
        for (int b = a + 1; b < count; ++b)
            for (int c = b + 1; c < count; ++c) {
                for (int bits = 0; bits < 4; ++bits) {
                    int64_t sum = weight[a] + (bits & 1 ? -weight[b] : weight[b]) + (bits & 2 ? -weight[c] : weight[c]);
                    if (sum == 0) add_small(a, b, c, 0, 3, bits);
                }
                for (int d = c + 1; d < count; ++d)
                    for (int bits = 0; bits < 8; ++bits) {
                        int64_t sum = weight[a] + (bits & 1 ? -weight[b] : weight[b]) + (bits & 2 ? -weight[c] : weight[c]) + (bits & 4 ? -weight[d] : weight[d]);
                        if (sum == 0) add_small(a, b, c, d, 4, bits);
                    }
            }
}

static int cached_zero(int d)
{
    for (int t = cache_head[d]; t >= 0; t = cache[t].next)
        if (contains_relation(&cache[t])) return 1;
    return 0;
}

/* First term is already included, so every chosen prefix is nonempty. */
static int proper_zero(int d, int64_t sum, int omitted)
{
    if (stopped) return 0;
    if (sum == 0) {
        if (!(omitted || d < sub_count)) return 0;
        for (int i = d; i < sub_count; ++i) chosen[i] = 0;
        return 1;
    }
    if (d == sub_count) return 0;
    if (sum + low[d] > 0 || sum + high[d] < 0 || sum % sub_gcd[d] != 0) return 0;
    chosen[d] = 0;
    if (proper_zero(d + 1, sum, 1)) return 1;
    chosen[d] = 1;
    return proper_zero(d + 1, sum + term[d], omitted);
}

static int minimal(void)
{
    sub_count = 0;
    for (int i = 0; i < count; ++i) if (coefficient[i] != 0) {
        term_index[sub_count] = i;
        term[sub_count++] = coefficient[i] * weight[i];
    }
    if (sub_count == 0) return 0;
    int original = sub_count;
    for (;;) {
        low[sub_count] = high[sub_count] = sub_gcd[sub_count] = 0;
        for (int i = sub_count; i > 0; --i) {
            int d = i - 1; int64_t x = term[d];
            low[d] = low[d + 1] + (x < 0 ? x : 0);
            high[d] = high[d + 1] + (x > 0 ? x : 0);
            sub_gcd[d] = gcd64(x < 0 ? -x : x, sub_gcd[d + 1]);
        }
        chosen[0] = 1;
        int found = proper_zero(1, term[0], 0);
        if (stopped) return 0;
        if (!found) break;
        int smaller = 0;
        for (int i = 0; i < sub_count; ++i) if (chosen[i]) {
            term[smaller] = term[i]; term_index[smaller++] = term_index[i];
        }
        sub_count = smaller;
    }
    /* A fully verified minimal zero subrelation is now known. */
    if (sub_count > best) best = sub_count;
    struct ZeroRelation r = {{0,0},{0,0},-1};
    for (int i = 0; i < sub_count; ++i)
        set_bit(term[i] > 0 ? r.positive : r.negative, term_index[i]);
    remember(r, term_index[sub_count - 1]);
    return sub_count == original;
}

static int possible(int d, int64_t sum)
{
    if (sum > remaining[d] || sum < -remaining[d]) return 0;
    return remaining_gcd[d] == 0 ? sum == 0 : sum % remaining_gcd[d] == 0;
}

static void search(int d, int64_t sum, int used, int seen)
{
    if (stopped || used + count - d <= best) return;
    if (recent_valid && contains_relation(&recent)) return;
    if (d == count) {
        if (sum == 0 && minimal() && !stopped) best = used;
        return;
    }
    /* Nonzero choices first, to find a useful lower bound sooner. */
    set_coefficient(d, 1);
    if (possible(d + 1, sum + weight[d]) && !cached_zero(d)) search(d + 1, sum + weight[d], used + 1, 1);
    if (seen) {
        set_coefficient(d, -1);
        if (possible(d + 1, sum - weight[d]) && !cached_zero(d)) search(d + 1, sum - weight[d], used + 1, 1);
    }
    set_coefficient(d, 0);
    if (possible(d + 1, sum)) search(d + 1, sum, used, seen);
    set_coefficient(d, 0);
}

static int parse(const char *text, int *n)
{
    if (*text == '\0') return 0;
    for (const char *p = text; *p; ++p) if (*p < '0' || *p > '9') return 0;
    errno = 0; char *end = NULL;
    long value = strtol(text, &end, 10);
    if (errno == ERANGE || end == NULL || *end || value < 1 || value > MAXN) return 0;
    *n = (int)value;
    return 1;
}

int main(int argc, char **argv)
{
    int limit = 40;
    if (argc == 2 && (!strcmp(argv[1], "--help") || !strcmp(argv[1], "-h"))) {
        if (printf("Usage: %s [N] (default 40; 1 <= N <= %d)\n", argv[0], MAXN) < 0 || fflush(stdout)) return 1;
        return 0;
    }
    if (argc > 2 || (argc == 2 && !parse(argv[1], &limit))) {
        fprintf(stderr, "Usage: %s [N]; N must be a decimal integer in 1..%d.\n", argv[0], MAXN);
        return 1;
    }
    if (signal(SIGINT, on_signal) == SIG_ERR || signal(SIGTERM, on_signal) == SIG_ERR) {
        perror("signal"); return 1;
    }
    int previous = 0;
    for (int n = 1; n <= limit && !stopped; ++n) {
        best = previous;
        int skip = n > 1 && (largest_prime_power(n) == n ||
                            (n % 2 == 0 && n / 2 >= 5 && prime(n / 2)));
        if (!skip) {
            if (!prepare(n)) {
                if (n > 1) { (void)printf("\n"); (void)fflush(stdout); }
                fprintf(stderr, "Internal error: denominator or lcm bound failed.\n");
                return 1;
            }
            build_cache();
            search(0, 0, 0, 0);
        }
        if (stopped) break;
        previous = best;
        if (printf(n == 1 ? "%d" : ", %d", best) < 0 || fflush(stdout)) {
            perror("write standard output"); return 1;
        }
    }
    if (printf("\n") < 0 || fflush(stdout)) { perror("write standard output"); return 1; }
    if (stopped) {
        fprintf(stderr, "Stopped; output contains only completed terms.\n");
        return stopped == SIGINT ? 130 : 143;
    }
    return 0;
}
