/*
 * A402762 / Erdos Problem 525.
 * Count degree-n polynomials with every coefficient +1 or -1 and
 * |f(z)| >= 1 on the entire unit circle. Both f and -f are counted.
 *
 * Build (MPFR/GMP libraries and the external PARI/GP executable are needed):
 *   mpfr_prefix=$(pkg-config --variable=prefix mpfr)
 *   gmp_prefix=$(pkg-config --variable=prefix gmp)
 *   cc -O3 -std=c11 -Wall -Wextra -Wpedantic -Wconversion -Wshadow -Werror \
 *      -isystem "$mpfr_prefix/include" -isystem "$gmp_prefix/include" \
 *      402762_01.c $(pkg-config --libs mpfr gmp) -lm -o 402762_01
 * Run: ./402762_01 NMAX          (0 <= NMAX <= 40; default 20)
 *      ./402762_01 --exact-only NMAX   (slower reference path)
 * Prints a(0),...,a(NMAX) once, on a single final line on stdout.
 * During computation only complete progress lines are printed to stderr.
 * No result, checkpoint, or temporary files are made.
 * Large degrees take exponentially longer; 40 is a safe representation limit,
 * not a promise of a quick run. No automatic time limit is applied.
 * The external command `gp -fq -s 64M` must be available on PATH.
 * This independently written application communicates with GP through pipes;
 * it neither includes PARI headers nor links to the PARI library.
 *
 * Mathematical reductions:
 *  (1) For coefficients e_j, set c_k=sum_j e_j*e_{j+k}. Then
 *      g(t)=|f(exp(it))|^2-1=n+2 sum c_k*cos(k*t). It is enough to test
 *      0 <= t <= pi. Every comparison in the count is inclusive (>=).
 *  (2) Negation, reversal, and e_j -> (-1)^j e_j preserve the condition.
 *      Their orbit has at most eight distinct masks. Count its smallest
 *      mask with the exact orbit size. The smallest mask always has leading
 *      coefficient +1, so only masks below 2^n need be scanned. The sum of
 *      all orbit sizes is checked against 2^(n+1). No known terms are used.
 *  (3) Every cosine used in screening/certification is computed by MPFR at
 *      192 bits, then correctly rounded to binary64. The argument k*t is
 *      exact at that precision (t has 53 significant bits and k <= 40).
 *      Thus the cosine's absolute error is < 2^-52. With |c_k| <= 40 and
 *      sum |c_k| <= n(n+1)/2, the usual gamma_m bound for round-to-nearest
 *      multiplication/addition gives absolute error < 2^-30 in a dot product
 *      for n <= 40. EVAL_ERROR=2^-24 is a conservative uniform bound.
 *      Non-IEEE binary64 and fast-math builds are rejected. Rounding is set
 *      to nearest. There is no assumption about the accuracy of system cos.
 *      If a computed g(t) < -EVAL_ERROR, the polynomial fails rigorously.
 *  (4) Let S2=sum 2|c_k|k^2 and S3=sum 2|c_k|k^3. They are exact integers
 *      below 2^53. Linear interpolation on [a,b] gives
 *      g(t) >= min(g(a),g(b)) - S2*(b-a)^2/8. We subtract EVAL_ERROR and
 *      round the penalty upwards at each operation using nextafter.
 *      An interval is accepted only if this rigorous lower bound is >=0.
 *      Bisection depth is bounded. Undecided cases go to the exact path.
 *  (5) At 0,pi/3,pi/2,2pi/3,pi the values 2g, a nonzero real multiple of
 *      g', and 2g'' are integers. Negative g or an interior simple zero
 *      rejects. At a zero with g'=0 and g''>0, Taylor's remainder proves
 *      nonnegativity for |t-t0| <= 3g''/S3. MPFR directed rounding constructs
 *      an interval strictly inside half this radius. No double approximation
 *      of t0 or the radius is trusted without enclosing it.
 *  (6) Exact fallback: P(x)=n+2 sum c_k*T_k(x), x=cos(t), has integer
 *      coefficients. The first nonzero coefficient of P(1-u) gives its sign
 *      immediately left of 1. Yun's gcd-based squarefree decomposition gives
 *      the product O of factors of odd multiplicity. Remove roots +-1 from
 *      O. P is nonnegative on [-1,1] iff the initial sign is positive and O
 *      has no root in (-1,1), by continuity and sign changes at odd roots.
 *      GP uses exact rational polynomial arithmetic and Sturm root counts.
 *      No approximate roots, probabilistic primality tests, or conjectures
 *      enter the fallback. Errors terminate the run, never supply a value.
 *
 * Arithmetic/memory: n<=40, masks have <=41 bits, counts <=2^41, signed
 * special-point sums are bounded by 4*40*sum_{k<=40}k^2 < 2^22.
 * S3 <= 2*40*sum_{k<=40}k^3 < 2^26. Cache: 8193*41 doubles (<3 MiB).
 * Recursion depth <=13. Polynomial arithmetic in GP is arbitrary precision.
 * Fixed degree 0 is handled directly: f=+1,-1, hence a(0)=2.
 */
#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <fcntl.h>
#include <fenv.h>
#include <float.h>
#include <inttypes.h>
#include <math.h>
#include <signal.h>
#include <spawn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#include <mpfr.h>

#if defined(__FAST_MATH__)
#error "Do not compile this exact-count program with fast-math."
#endif
#if FLT_RADIX != 2 || DBL_MANT_DIG != 53 || DBL_MAX_EXP != 1024
#error "IEEE binary64 double is required."
#endif

#define MAXN 40
#define DEPTH 13
#define POINTS (1U << DEPTH)
#define PRECISION 192
#define EVAL_ERROR 0x1p-24

typedef uint64_t u64;
extern char **environ;
static int degree, length, corr[MAXN + 1], grid_m, nneigh;
static u64 second_bound, third_bound;
static double pi_upper, grid[4 * MAXN + 1][MAXN + 1];
static double (*cache)[MAXN + 1];
static unsigned char ready[POINTS + 1];
static double neigh_lo[5], neigh_hi[5];
static mpfr_t arg, value, pi_lo_mp, pi_hi_mp, center_lo, center_hi, radius;
static FILE *gp_in, *gp_out;
static pid_t gp_pid = -1;

static void stop_gp(void)
{
    if (gp_pid > 0) {
        (void)kill(gp_pid, SIGTERM);
        if (gp_in) { (void)fclose(gp_in); gp_in = NULL; }
        if (gp_out) { (void)fclose(gp_out); gp_out = NULL; }
        int status;
        while (waitpid(gp_pid, &status, 0) < 0 && errno == EINTR) { }
        gp_pid = -1;
    }
}

static void fail(const char *message)
{
    fprintf(stderr, "\nError: %s\n", message);
    exit(2);
}

static void make_pipe(int p[2])
{
    if (pipe(p) < 0) fail("cannot create GP pipe");
    for (int i = 0; i < 2; i++) {
        if (p[i] < 3) {
            int fd = fcntl(p[i], F_DUPFD, 3);
            if (fd < 0) fail("cannot duplicate GP pipe");
            (void)close(p[i]);
            p[i] = fd;
        }
        if (fcntl(p[i], F_SETFD, FD_CLOEXEC) < 0) fail("cannot protect GP pipe");
    }
}

static void gp_expect(const char *expected)
{
    char line[128];
    if (!fgets(line, sizeof line, gp_out) || strcmp(line, expected) != 0)
        fail("GP protocol failed (no exact result accepted)");
}

static void start_gp(void)
{
    int to_gp[2], from_gp[2];
    make_pipe(to_gp); make_pipe(from_gp);
    posix_spawn_file_actions_t actions;
    if (posix_spawn_file_actions_init(&actions) != 0) fail("GP spawn setup");
    if (posix_spawn_file_actions_adddup2(&actions, to_gp[0], STDIN_FILENO) != 0 ||
        posix_spawn_file_actions_adddup2(&actions, from_gp[1], STDOUT_FILENO) != 0)
        fail("GP spawn redirects");
    for (int i = 0; i < 2; i++) {
        if (posix_spawn_file_actions_addclose(&actions, to_gp[i]) != 0 ||
            posix_spawn_file_actions_addclose(&actions, from_gp[i]) != 0)
            fail("GP spawn close actions");
    }
    char *args[] = {(char *)"gp", (char *)"-fq", (char *)"-s", (char *)"64M", NULL};
    int err = posix_spawnp(&gp_pid, "gp", &actions, NULL, args, environ);
    (void)posix_spawn_file_actions_destroy(&actions);
    (void)close(to_gp[0]); (void)close(from_gp[1]);
    if (err != 0) { gp_pid = -1; fail("cannot start gp; install PARI/GP and check PATH"); }
    gp_in = fdopen(to_gp[1], "w"); gp_out = fdopen(from_gp[0], "r");
    if (!gp_in || !gp_out) fail("cannot open GP streams");
    /* Gcd-only squarefree decomposition; no factorization is required. */
    const char *definition =
        "a402762_exact(n,V)={my(P=n+2*sum(k=1,n,V[k]*polchebyshev(k)),Q,A,W,Y,H,oddpart=1,i=1);"
        "if(!P,return(1));Q=subst(P,x,1-x);"
        "if(polcoef(Q,valuation(Q,x))<0,return(0));"
        "A=gcd(P,P');W=P/A;"
        "while(poldegree(W)>0,Y=gcd(W,A);H=W/Y;if(i%2,oddpart*=H);W=Y;A/=Y;i++);"
        "if(subst(oddpart,x,1)==0,oddpart/=x-1);if(subst(oddpart,x,-1)==0,oddpart/=x+1);"
        "if(poldegree(oddpart)>0 && polsturm(oddpart,[-1,1]),0,1)};\nprint(\"READY\");\n";
    if (fputs(definition, gp_in) == EOF || fflush(gp_in) == EOF) fail("GP initialization write failed");
    gp_expect("READY\n");
}

static int exact_decision(void)
{
    if (!gp_in) start_gp();
    if (fprintf(gp_in, "iferr(print(\"V \",a402762_exact(%d,[", degree) < 0)
        fail("GP write failed");
    for (int k = 1; k <= degree; k++)
        if (fprintf(gp_in, "%s%d", k == 1 ? "" : ",", corr[k]) < 0) fail("GP write failed");
    if (fputs("])),E,print(\"ERR\");quit(1));\n", gp_in) == EOF || fflush(gp_in) == EOF)
        fail("GP request failed");
    char line[128];
    if (!fgets(line, sizeof line, gp_out)) fail("GP closed without an exact result");
    if (strcmp(line, "V 0\n") == 0) return 0;
    if (strcmp(line, "V 1\n") == 0) return 1;
    fail("GP exact arithmetic failed; this term was not completed");
    return 0;
}

static void finish_gp(void)
{
    if (gp_pid <= 0) return;
    if (fputs("quit;\n", gp_in) == EOF || fflush(gp_in) == EOF) fail("GP termination write failed");
    if (fclose(gp_in) != 0) { gp_in = NULL; fail("GP stream close failed"); }
    gp_in = NULL;
    (void)fclose(gp_out); gp_out = NULL;
    int status = 0;
    pid_t got;
    do { got = waitpid(gp_pid, &status, 0); } while (got < 0 && errno == EINTR);
    gp_pid = -1;
    if (got < 0 || !WIFEXITED(status) || WEXITSTATUS(status) != 0) fail("GP exited unsuccessfully");
}

static void init_math(void)
{
    if (fesetround(FE_TONEAREST) != 0) fail("cannot set round-to-nearest");
    mpfr_inits2(PRECISION, arg, value, pi_lo_mp, pi_hi_mp,
                center_lo, center_hi, radius, (mpfr_ptr)0);
    (void)mpfr_const_pi(pi_lo_mp, MPFR_RNDD);
    (void)mpfr_const_pi(pi_hi_mp, MPFR_RNDU);
    pi_upper = mpfr_get_d(pi_hi_mp, MPFR_RNDU);
    cache = calloc((size_t)POINTS + 1, sizeof *cache);
    if (!cache) fail("cosine cache allocation failed");
}

static double certified_cos(double t, unsigned k)
{
    (void)mpfr_set_d(arg, t, MPFR_RNDN);
    (void)mpfr_mul_ui(arg, arg, (unsigned long)k, MPFR_RNDN);
    (void)mpfr_cos(value, arg, MPFR_RNDN);
    return mpfr_get_d(value, MPFR_RNDN);
}

static double position(unsigned j)
{
    return ldexp(pi_upper * (double)j, -DEPTH);
}

static double eval_row(const double *row)
{
    double v = (double)degree;
    for (int k = 1; k <= degree; k++) v += 2.0 * (double)corr[k] * row[k];
    return v;
}

static double eval_at(unsigned j)
{
    if (!ready[j]) {
        double t = position(j);
        for (int k = 1; k <= degree; k++) cache[j][k] = certified_cos(t, (unsigned)k);
        ready[j] = 1;
    }
    return eval_row(cache[j]);
}

static void setup_degree(int n)
{
    degree = n; length = n + 1; grid_m = 4 * n;
    memset(ready, 0, sizeof ready);
    for (int i = 0; i <= grid_m; i++) {
        double t = pi_upper * (double)i / (double)grid_m;
        for (int k = 1; k <= n; k++) grid[i][k] = certified_cos(t, (unsigned)k);
    }
}

static void autocorrelation(u64 mask)
{
    second_bound = third_bound = 0;
    for (int k = 1; k <= degree; k++) {
        u64 x = (mask ^ (mask >> k)) & ((UINT64_C(1) << (length - k)) - 1);
        corr[k] = (length - k) - 2 * __builtin_popcountll(x);
        u64 a = (u64)(corr[k] < 0 ? -corr[k] : corr[k]);
        u64 kk = (u64)k;
        second_bound += 2 * a * kk * kk;
        third_bound += 2 * a * kk * kk * kk;
    }
}

static int certify(unsigned a, unsigned b, double ga, double gb)
{
    double ta = position(a), tb = position(b);
    for (int i = 0; i < nneigh; i++)
        if (ta >= neigh_lo[i] && tb <= neigh_hi[i]) return 1;
    double w = nextafter(tb - ta, INFINITY);
    double penalty = nextafter(w * w, INFINITY);
    penalty = nextafter((penalty * 0.125) * (double)second_bound, INFINITY);
    double lower = nextafter(fmin(ga, gb) - EVAL_ERROR, -INFINITY);
    lower = nextafter(lower - penalty, -INFINITY);
    if (lower >= 0.0) return 1;
    if (b - a <= 1) return 2;
    unsigned mid = (a + b) / 2;
    double gm = eval_at(mid);
    if (gm < -EVAL_ERROR) return 0;
    int left = certify(a, mid, ga, gm);
    if (left != 1) return left;
    return certify(mid, b, gm, gb);
}

static void zero_neighborhood(int j, int64_t gpp2)
{
    /* radius = 3*gpp2/(4*S3), rounded down; R/2 in statement (5). */
    (void)mpfr_set_si(radius, (long)gpp2, MPFR_RNDN);
    (void)mpfr_mul_ui(radius, radius, 3, MPFR_RNDD);
    (void)mpfr_div_ui(radius, radius, (unsigned long)(4 * third_bound), MPFR_RNDD);
    (void)mpfr_mul_ui(center_lo, pi_lo_mp, (unsigned long)j, MPFR_RNDD);
    (void)mpfr_div_ui(center_lo, center_lo, 6, MPFR_RNDD);
    (void)mpfr_mul_ui(center_hi, pi_hi_mp, (unsigned long)j, MPFR_RNDU);
    (void)mpfr_div_ui(center_hi, center_hi, 6, MPFR_RNDU);
    (void)mpfr_sub(value, center_hi, radius, MPFR_RNDU);
    double lo = mpfr_get_d(value, MPFR_RNDU);
    (void)mpfr_add(value, center_lo, radius, MPFR_RNDD);
    double hi = mpfr_get_d(value, MPFR_RNDD);
    if (lo < hi) {
        if (nneigh >= 5) fail("neighborhood count exceeded its bound");
        neigh_lo[nneigh] = lo; neigh_hi[nneigh] = hi; nneigh++;
    }
}

/* 0 bad, 1 good, 2 requires exact polynomial arithmetic. */
static int filtered_decision(void)
{
    for (int i = 0; i <= grid_m; i++)
        if (eval_row(grid[i]) < -EVAL_ERROR) return 0;
    static const int co[12] = {2, 99, 1, 0, -1, 99, -2, 99, -1, 0, 1, 99};
    static const int si[12] = {0, 99, 1, 1, 1, 99, 0, 99, -1, -1, -1, 99};
    static const int js[5] = {0, 2, 3, 4, 6};
    nneigh = 0;
    for (int q = 0; q < 5; q++) {
        int j = js[q]; int64_t g2 = 2 * degree, gp = 0, gpp2 = 0;
        for (int k = 1; k <= degree; k++) {
            int ph = (k * j) % 12;
            if (co[ph] == 99 || si[ph] == 99) fail("invalid exact angle");
            g2 += 2 * (int64_t)corr[k] * co[ph];
            gp += (int64_t)corr[k] * k * si[ph];
            gpp2 -= 2 * (int64_t)corr[k] * k * k * co[ph];
        }
        if (g2 < 0) return 0;
        if (g2 == 0) {
            if (gp != 0) return 0;
            if (gpp2 <= 0) return 2;
            zero_neighborhood(j, gpp2);
        }
    }
    return certify(0, POINTS, eval_at(0), eval_at(POINTS));
}

static u64 reversal(u64 x)
{
    x = ((x & UINT64_C(0x5555555555555555)) << 1) | ((x >> 1) & UINT64_C(0x5555555555555555));
    x = ((x & UINT64_C(0x3333333333333333)) << 2) | ((x >> 2) & UINT64_C(0x3333333333333333));
    x = ((x & UINT64_C(0x0f0f0f0f0f0f0f0f)) << 4) | ((x >> 4) & UINT64_C(0x0f0f0f0f0f0f0f0f));
    x = ((x & UINT64_C(0x00ff00ff00ff00ff)) << 8) | ((x >> 8) & UINT64_C(0x00ff00ff00ff00ff));
    x = ((x & UINT64_C(0x0000ffff0000ffff)) << 16) | ((x >> 16) & UINT64_C(0x0000ffff0000ffff));
    x = ((x & UINT64_C(0x00000000ffffffff)) << 32) | ((x >> 32) & UINT64_C(0x00000000ffffffff));
    return x >> (64 - length);
}

static u64 count_degree(int n, int exact_only)
{
    if (n == 0) return 2;
    setup_degree(n);
    u64 limit = UINT64_C(1) << n, fullmask = (limit << 1) - 1, odd = 0;
    for (int j = 1; j < length; j += 2) odd |= UINT64_C(1) << j;
    u64 answer = 0, accounted = 0, representatives = 0, exact_calls = 0;
    for (u64 m = 0; m < limit; m++) {
        u64 r = reversal(m);
        u64 images[8] = {m, m ^ fullmask, r, r ^ fullmask,
                         m ^ odd, m ^ odd ^ fullmask, r ^ odd, r ^ odd ^ fullmask};
        u64 distinct[8]; int size = 0, least = 1;
        for (int i = 0; i < 8; i++) {
            if (images[i] < m) { least = 0; break; }
            int duplicate = 0;
            for (int k = 0; k < size; k++) if (distinct[k] == images[i]) duplicate = 1;
            if (!duplicate) distinct[size++] = images[i];
        }
        if (!least) continue;
        representatives++; accounted += (u64)size;
        autocorrelation(m);
        int decision = exact_only ? 2 : filtered_decision();
        if (decision == 2) { exact_calls++; decision = exact_decision(); }
        if (decision == 1) answer += (u64)size;
    }
    if (accounted != (limit << 1) || answer > accounted) fail("orbit accounting failed");
    fprintf(stderr, "n=%d: representatives=%" PRIu64 ", exact_checks=%" PRIu64 "\n",
            n, representatives, exact_calls);
    return answer;
}

static int parse_limit(const char *s, int *out)
{
    if (!*s) return 0;
    unsigned v = 0;
    for (; *s; s++) {
        if (*s < '0' || *s > '9') return 0;
        unsigned digit = (unsigned)(*s - '0');
        if (v > (MAXN - digit) / 10U) return 0;
        v = v * 10U + digit;
        if (v > MAXN) return 0;
    }
    *out = (int)v; return 1;
}

static double elapsed(const struct timespec *a, const struct timespec *b)
{
    return (double)(b->tv_sec - a->tv_sec) + 1e-9 * (double)(b->tv_nsec - a->tv_nsec);
}

int main(int argc, char **argv)
{
    int nmax = 20, exact_only = 0;
    if (argc == 2 && strcmp(argv[1], "--help") == 0) {
        if (printf("Usage: %s [NMAX] | --exact-only NMAX (0..40)\nRequires MPFR/GMP and gp on PATH.\n", argv[0]) < 0) return 2;
        return fflush(stdout) == 0 ? 0 : 2;
    }
    if (argc == 3 && strcmp(argv[1], "--exact-only") == 0) {
        exact_only = 1;
        if (!parse_limit(argv[2], &nmax)) fail("NMAX must be a decimal integer in 0..40");
    } else if (argc == 2) {
        if (!parse_limit(argv[1], &nmax)) fail("NMAX must be a decimal integer in 0..40");
    } else if (argc != 1) fail("usage: 402762_01 [NMAX] | --exact-only NMAX");
    if (atexit(stop_gp) != 0) fail("cannot register GP cleanup");
    if (signal(SIGPIPE, SIG_IGN) == SIG_ERR) fail("cannot handle pipe errors");
    init_math();
    u64 results[MAXN + 1];
    for (int n = 0; n <= nmax; n++) {
        struct timespec t0, t1;
        if (clock_gettime(CLOCK_MONOTONIC, &t0) != 0) fail("clock_gettime failed");
        fprintf(stderr, "n=%d: computing\n", n);
        results[n] = count_degree(n, exact_only);
        if (clock_gettime(CLOCK_MONOTONIC, &t1) != 0) fail("clock_gettime failed");
        fprintf(stderr, "n=%d: a(n)=%" PRIu64 " (%.3fs)\n", n, results[n], elapsed(&t0, &t1));
    }
    finish_gp();
    if (fflush(stderr) == EOF) fail("cannot finish progress output");
    for (int n = 0; n <= nmax; n++)
        if (printf("%s%" PRIu64, n ? ", " : "", results[n]) < 0) fail("cannot write final list");
    if (putchar('\n') == EOF || fflush(stdout) != 0) fail("cannot finish final list");
    free(cache);
    mpfr_clears(arg, value, pi_lo_mp, pi_hi_mp, center_lo, center_hi, radius, (mpfr_ptr)0);
    return 0;
}
