/*
 * Erdős Problem 284: decide if 1 is a sum of K distinct unit fractions
 * with all denominators at least MIN. Usage: fk-exact K MIN CPU_SECONDS.
 * Exit 0: witness on stdout; 1: invalid input or timer error at startup;
 * 2: interrupted search; 3: complete search with no witness.
 * Usage: fk-exact --range FIRST LAST CPU_SECONDS_PER_K.
 * Output: "K VALUE" for a proved maximum, "K LOW..HIGH" for a range.
 * Exit 2 if any requested value is still uncertain.
 * CPU limits are checked every 65,536 search steps and can be exceeded
 * between checks.
 *
 * Search denominators in strictly increasing order. For a remainder a/b
 * and m >= 2 terms, the next denominator d satisfies b/a < d <= m*b/a.
 * The sum of the m consecutive reciprocals starting at 1/d is an upper
 * bound and decreases with d. Floating point only proposes that cutoff.
 * A branch is removed only after an exact GMP rational comparison.
 */
#include <stdio.h> /* before gmp.h, so that mpz_out_str is declared */
#include <errno.h>
#include <float.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <gmp.h>
#include <time.h>

#define MAXK 200

static mpz_t path[MAXK];
static unsigned long long calls;
static clock_t deadline_start;
static double deadline_limit;
static int timed_out;
static unsigned long long steps; /* loop iterations, for the time check */

static int time_expired(void)
{
    if ((++steps & 0xFFFFULL) == 0) {
        clock_t now = clock();
        if (now == (clock_t)-1 || now < deadline_start ||
            ((double)now - (double)deadline_start) / CLOCKS_PER_SEC >= deadline_limit) {
            timed_out = 1;
        }
    }
    return timed_out;
}

/* Sum of 1/(d+j), j = 0..m-1, in long double. */
static long double consecutive_sum(long double base, int m)
{
    long double s = 0.0L;
    for (int j = m - 1; j >= 0; j--) {
        s += 1.0L / (base + (long double)j);
    }
    return s;
}


static int exact_below(const mpz_t d, int m, const mpz_t a, const mpz_t b)
{
    mpq_t sum, term, target;
    mpq_inits(sum, term, target, NULL);
    mpz_set(mpq_numref(target), a);
    mpz_set(mpq_denref(target), b);
    mpq_set_ui(term, 1, 1);
    mpz_set(mpq_denref(term), d);
    for (int j = 0; j < m; j++) {
        mpq_add(sum, sum, term);
        mpz_add_ui(mpq_denref(term), mpq_denref(term), 1);
    }
    int below = mpq_cmp(sum, target) < 0;
    mpq_clears(sum, term, target, NULL);
    return below;
}

static unsigned long long divisor_calls, fallbacks;
typedef struct {
    unsigned long a, b, square, minimum;
    unsigned long prime[sizeof(unsigned long) * CHAR_BIT];
    unsigned int exponent[sizeof(unsigned long) * CHAR_BIT];
    size_t count;
    unsigned long x, y;
} Tail;

/* For 1/x + 1/y = a/b, (a*x-b)*(a*y-b) = b*b.
 * Enumerate u = a*x-b with 0 < u < b, which is equivalent to x < y
 * for v = b*b/u. Check both divisions by a and the lower bound on x. */
static int visit_divisors(Tail *s, size_t index, unsigned long u)
{
    if (index == s->count) {
        unsigned long v = s->square / u;
        if ((u + s->b) % s->a || (v + s->b) % s->a) {
            return 0;
        }
        s->x = (u + s->b) / s->a;
        s->y = (v + s->b) / s->a;
        return s->x >= s->minimum;
    }
    unsigned long p = s->prime[index];
    for (unsigned int e = 0; ; ++e) {
        if (visit_divisors(s, index + 1, u)) {
            return 1;
        }
        if (e == 2 * s->exponent[index] || u > (s->b - 1) / p) {
            return 0;
        }
        u *= p;
    }
}

/* Recover the second denominator as y = b*x/(a*x-b).
 * For x < y, x*(a*x-b) < b*x, hence x <= floor((2*b-1)/a). */
static int solve_tail_gmp(const mpz_t a, const mpz_t b, const mpz_t lo, int depth)
{
    mpz_t x, last, den, num, y;
    mpz_inits(x, last, den, num, y, NULL);
    mpz_fdiv_q(x, b, a);
    mpz_add_ui(x, x, 1);
    if (mpz_cmp(x, lo) < 0) {
        mpz_set(x, lo);
    }
    mpz_mul_ui(last, b, 2);
    mpz_sub_ui(last, last, 1);
    mpz_fdiv_q(last, last, a);
    int found = 0;
    for (; mpz_cmp(x, last) <= 0; mpz_add_ui(x, x, 1)) {
        if (time_expired()) {
            break;
        }
        mpz_mul(den, a, x);
        mpz_sub(den, den, b);
        mpz_mul(num, b, x);
        if (mpz_divisible_p(num, den)) {
            mpz_divexact(y, num, den);
            mpz_set(path[depth], x);
            mpz_set(path[depth + 1], y);
            found = 1;
            break;
        }
    }
    mpz_clears(x, last, den, num, y, NULL);
    return found;
}

/* Return -1 to fall back to the original exhaustive search. */
static int solve_tail(const mpz_t a, const mpz_t b, const mpz_t lo, int depth)
{
    if (mpz_cmp(lo, b) > 0 && mpz_cmp_ui(a, 2) >= 0) {
        return 0; /* 1/x + 1/y < 2/lo < a/b */
    }
    if (!mpz_fits_ulong_p(b) || !mpz_fits_ulong_p(a) || !mpz_fits_ulong_p(lo)) {
        return -1;
    }
    Tail s = {.a = mpz_get_ui(a), .b = mpz_get_ui(b), .minimum = mpz_get_ui(lo)};
    if (s.b <= 1) {
        return -1;
    }
    if (s.b > (ULONG_MAX - s.b) / s.b) {
        return -1;
    }
    /* Direct search wins for short ranges. Avoid a second GMP setup there
       by testing each x and recovering y with a single exact division. */
    unsigned long first = s.b / s.a + 1;
    if (first < s.minimum) {
        first = s.minimum;
    }
    unsigned long last = 2 * s.b / s.a;
    if (last < first) {
        return 0;
    }
    if (last - first < 32 && last <= ULONG_MAX / s.b) {
        for (unsigned long x = first; x <= last; ++x) {
            unsigned long divisor = s.a * x - s.b;
            unsigned long product = s.b * x;
            if (product % divisor == 0 && product / divisor > x) {
                mpz_set_ui(path[depth], x);
                mpz_set_ui(path[depth + 1], product / divisor);
                return 1;
            }
        }
        return 0;
    }

    s.square = s.b * s.b;
    /* Trial division proves the factors. If the trial cap is reached
     * before the factorization is complete, use the GMP search instead. */
    unsigned long remaining = s.b;
    unsigned long p;
    for (p = 2; p <= remaining / p && p <= 1000; p += p == 2 ? 1 : 2) {
        if (remaining % p == 0) {
            s.prime[s.count] = p;
            do {
                remaining /= p;
                ++s.exponent[s.count];
            } while (remaining % p == 0);
            ++s.count;
        }
    }
    if (p <= remaining / p) {
        return -1;
    }
    if (remaining > 1) {
        s.prime[s.count] = remaining;
        s.exponent[s.count++] = 1;
    }
    ++divisor_calls;
    if (visit_divisors(&s, 0, 1)) {
        mpz_set_ui(path[depth], s.x);
        mpz_set_ui(path[depth + 1], s.y);
        return 1;
    }
    return 0;
}

/* q = a/b in lowest terms, a > 0, b > 0. */
static int exists(const mpz_t a, const mpz_t b, int m, const mpz_t lo, int depth)
{
    calls++;
    if (time_expired()) {
        return 0;
    }
    if (m == 1) {
        if (mpz_cmp_ui(a, 1) == 0 && mpz_cmp(b, lo) >= 0) {
            mpz_set(path[depth], b);
            return 1;
        }
        return 0;
    }

    if (m == 2) {
        int result = solve_tail(a, b, lo, depth);
        if (result >= 0) {
            return result;
        }
        ++fallbacks;
        return solve_tail_gmp(a, b, lo, depth);
    }
    int found = 0;
    mpz_t d, top, na, nb, g;
    mpz_inits(d, top, na, nb, g, NULL);

    /* d starts at max(lo, floor(b/a) + 1) */
    mpz_fdiv_q(d, b, a);
    mpz_add_ui(d, d, 1);
    if (mpz_cmp(d, lo) < 0) {
        mpz_set(d, lo);
    }
    /* top = floor(m*b/a) */
    mpz_mul_ui(top, b, (unsigned long)m);
    mpz_fdiv_q(top, top, a);

    /* If b has g more bits than a, then a/b > 2^(-g-1).
       Leave room above DBL_MIN for the margin in the cutoff test. */
    const size_t reciprocal_bits = (size_t)(-(DBL_MIN_EXP + 1));
    const size_t a_bits = mpz_sizeinbase(a, 2);
    const size_t b_bits = mpz_sizeinbase(b, 2);
    const int use_approximation = b_bits <= a_bits ||
                                  b_bits - a_bits <= reciprocal_bits;
    long double qd = 0.0L;
    if (use_approximation) {
        mpq_t q;
        mpq_init(q);
        mpz_set(mpq_numref(q), a);
        mpz_set(mpq_denref(q), b);
        qd = (long double)mpq_get_d(q);
        mpq_clear(q);
    }

    for (; mpz_cmp(d, top) <= 0; mpz_add_ui(d, d, 1)) {
        if (time_expired()) {
            break;
        }
        /* Also keep d and the reciprocals of d+j in the normal range.
           Otherwise, try the exact bound directly. */
        size_t d_bits = mpz_sizeinbase(d, 2);
        int try_exact_bound = !use_approximation ||
                              d_bits >= DBL_MAX_EXP || d_bits > reciprocal_bits;
        if (!try_exact_bound) {
            long double h = consecutive_sum((long double)mpz_get_d(d), m);
            try_exact_bound = h * (1.0L + 1e-12L) < qd * (1.0L - 1e-12L);
        }
        if (try_exact_bound && exact_below(d, m, a, b)) {
            break; /* bound (3) */
        }
        /* new q = a/b - 1/d = (a*d - b) / (b*d) */
        mpz_mul(na, a, d);
        mpz_sub(na, na, b);
        if (mpz_sgn(na) <= 0) {
            continue; /* cannot happen because d > b/a; kept as a guard */
        }
        mpz_mul(nb, b, d);
        mpz_gcd(g, na, nb);
        mpz_divexact(na, na, g);
        mpz_divexact(nb, nb, g);
        mpz_add_ui(g, d, 1); /* next lower bound d + 1 */
        if (exists(na, nb, m - 1, g, depth + 1)) {
            mpz_set(path[depth], d);
            found = 1;
            break;
        }
    }
    mpz_clears(d, top, na, nb, g, NULL);
    return found;
}


static int parse_positive(const char *text, unsigned long *value)
{
    if (*text < '1' || *text > '9') {
        return 0;
    }
    char *end;
    errno = 0;
    *value = strtoul(text, &end, 10);
    return errno == 0 && *end == '\0';
}

/* Previously found representations, checked with GMP before use. */
static const struct {
    int k;
    const char *denominators;
} witnesses[] = {
    {21, "11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 561 71820 1315600"},
    {23, "12 13 14 15 16 17 18 19 20 21 22 24 25 27 28 29 30 32 35 36 52 26519514 4409675395725600"},
    {25, "13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 30 32 33 34 35 44 2259 7360848 270353095365600"},
    {26, "14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 32 33 34 35 39 44 58 1384416 1591995600"},
    {29, "15 16 17 18 19 20 21 22 23 24 25 26 28 29 30 31 32 33 34 35 36 38 39 40 44 70 14212 623609127 550278181425117600"},
};

static int check_witness(int k)
{
    mpq_t sum, term;
    mpq_inits(sum, term, NULL);
    mpq_set_ui(term, 1, 1);
    int valid = 1;
    for (int i = 0; i < k; ++i) {
        if (mpz_sgn(path[i]) <= 0 || (i > 0 && mpz_cmp(path[i - 1], path[i]) >= 0)) {
            valid = 0;
            break;
        }
        mpz_set(mpq_denref(term), path[i]);
        mpq_add(sum, sum, term);
    }
    valid = valid && mpq_cmp_ui(sum, 1, 1) == 0;
    mpq_clears(sum, term, NULL);
    return valid;
}

static int stored_lower_bound(int k)
{
    for (size_t i = 0; i < sizeof(witnesses) / sizeof(witnesses[0]); ++i) {
        if (witnesses[i].k != k) {
            continue;
        }
        char line[512];
        int size = snprintf(line, sizeof(line), "%s", witnesses[i].denominators);
        if (size < 0 || (size_t)size >= sizeof(line)) {
            return -1;
        }
        char *part = strtok(line, " ");
        for (int j = 0; j < k; ++j) {
            if (part == NULL || mpz_set_str(path[j], part, 10) != 0) {
                return -1;
            }
            part = strtok(NULL, " ");
        }
        if (part != NULL || !check_witness(k) || mpz_cmp_ui(path[0], (unsigned long)k) > 0) {
            return -1;
        }
        return (int)mpz_get_ui(path[0]);
    }
    return 0;
}

static int run_range(int first, int last, unsigned long seconds)
{
    for (int i = 0; i < last; ++i) {
        mpz_init(path[i]);
    }
    mpz_t one, minimum;
    mpz_init_set_ui(one, 1);
    mpz_init(minimum);
    int lower = 1;
    int status = 0;
    for (int k = 1; k <= last; ++k) {
        if (k == 2) {
            continue;
        }
        int stored = stored_lower_bound(k);
        if (stored < 0) {
            fprintf(stderr, "Invalid stored witness for k=%d\n", k);
            status = 1;
            break;
        }
        /* Splitting the largest denominator preserves the minimum for k >= 3.
         * The k=1 bound of 1 is also valid for k >= 3 by the 3-term example. */
        if (stored > lower) {
            lower = stored;
        }
        if (k < first) {
            continue;
        }
        int upper = k;
        while (upper > lower) {
            mpz_set_ui(minimum, (unsigned long)upper);
            if (!exact_below(minimum, k, one, one)) {
                break;
            }
            --upper;
        }
        deadline_start = clock();
        if (deadline_start == (clock_t)-1) {
            fputs("CPU timer unavailable\n", stderr);
            status = 1;
            break;
        }
        deadline_limit = (double)seconds;
        timed_out = 0;
        steps = 0;
        while (upper > lower) {
            mpz_set_ui(minimum, (unsigned long)upper);
            if (exists(one, one, k, minimum, 0)) {
                if (!check_witness(k) || mpz_cmp(path[0], minimum) != 0) {
                    fprintf(stderr, "Invalid search witness for k=%d\n", k);
                    status = 1;
                    break;
                }
                lower = upper;
            } else if (timed_out) {
                break;
            } else {
                --upper;
            }
        }
        if (status == 1) {
            break;
        }
        if (lower == upper) {
            printf("%d %d\n", k, lower);
        } else {
            printf("%d %d..%d\n", k, lower, upper);
            status = 2;
        }
        if (fflush(stdout) == EOF || ferror(stdout)) {
            status = 1;
            break;
        }
    }
    mpz_clears(one, minimum, NULL);
    for (int i = 0; i < last; ++i) {
        mpz_clear(path[i]);
    }
    return status;
}

int main(int argc, char **argv)
{
    unsigned long count, minimum, seconds;
    if (argc > 1 && strcmp(argv[1], "--range") == 0) {
        unsigned long first, last;
        if (argc != 5 || !parse_positive(argv[2], &first) ||
            !parse_positive(argv[3], &last) || first > last || last > MAXK ||
            !parse_positive(argv[4], &seconds)) {
            fprintf(stderr, "usage: %s --range FIRST LAST CPU_SECONDS (1 <= FIRST <= LAST <= %d)\n",
                    argv[0], MAXK);
            return 1;
        }
        return run_range((int)first, (int)last, seconds);
    }
    if (argc != 4 || !parse_positive(argv[1], &count) || count > MAXK ||
        !parse_positive(argv[2], &minimum) || !parse_positive(argv[3], &seconds)) {
        fprintf(stderr, "usage: %s K MIN CPU_SECONDS (1 <= K <= %d)\n", argv[0], MAXK);
        return 1;
    }
    deadline_start = clock();
    if (deadline_start == (clock_t)-1) {
        fputs("CPU timer unavailable\n", stderr);
        return 1;
    }
    deadline_limit = (double)seconds;

    int k = (int)count;
    for (int i = 0; i < k; ++i) {
        mpz_init(path[i]);
    }
    mpz_t one, lo;
    mpz_init_set_ui(one, 1);
    mpz_init_set_ui(lo, minimum);
    int found = exists(one, one, k, lo, 0);
    if (found) {
        for (int i = 0; i < k; ++i) {
            if (i > 0) {
                putchar(' ');
            }
            mpz_out_str(stdout, 10, path[i]);
        }
        putchar('\n');
    }
    for (int i = 0; i < k; ++i) {
        mpz_clear(path[i]);
    }
    mpz_clears(one, lo, NULL);
    fprintf(stderr, "%s (%llu calls, %llu divisor searches, %llu GMP tail searches)\n",
            timed_out ? "unknown" : (found ? "witness found" : "no representation"),
            calls, divisor_calls, fallbacks);
    if (found && (fflush(stdout) == EOF || ferror(stdout))) {
        return 1;
    }
    return timed_out ? 2 : (found ? 0 : 3);
}
