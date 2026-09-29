/*
 * a(0) = 1;
 * a(n) = (n-1)! * Sum_{j=0..floor((n-1)/3)} (3*j+1) * a(n-1-3*j)/(n-1-3*j)!
 *                 * Sum_{k=0..j} a(k)*a(j-k)/(k!*(j-k)!).
 *
 * build: gcc -O2 -o 400528_01 400527_01.c -lgmp
 */
#include <stdio.h>
#include <stdlib.h>
#include <gmp.h>

#define N 450

int main(void)
{
    mpz_t fact[N + 1];
    mpq_t a[N + 1];
    mpq_t s, t, term, tmp;
    int i, j, k;

    /* factorials */
    for (i = 0; i <= N; i++) {
        mpz_init(fact[i]);
        if (i < 2) mpz_set_ui(fact[i], 1);
        else       mpz_mul_ui(fact[i], fact[i - 1], i);
    }

    mpq_init(s); mpq_init(t); mpq_init(term); mpq_init(tmp);
    for (i = 0; i <= N; i++) mpq_init(a[i]);

    mpq_set_ui(a[0], 1, 1);
    for (i = 1; i <= N; i++) {
        mpq_set_ui(s, 0, 1);
        for (j = 0; j <= (i - 1) / 3; j++) {
            /* t = Sum_{k=0..j} a(k)*a(j-k)/(k!*(j-k)!) */
            mpq_set_ui(t, 0, 1);
            for (k = 0; k <= j; k++) {
                mpq_mul(tmp, a[k], a[j - k]);
                mpz_mul(mpq_denref(tmp), mpq_denref(tmp), fact[k]);
                mpz_mul(mpq_denref(tmp), mpq_denref(tmp), fact[j - k]);
                mpq_canonicalize(tmp);
                mpq_add(t, t, tmp);
            }
            /* term = (3j+1) * a(i-1-3j) / (i-1-3j)! * t */
            mpq_set(term, a[i - 1 - 3 * j]);
            mpz_mul_ui(mpq_numref(term), mpq_numref(term), 3 * j + 1);
            mpz_mul(mpq_denref(term), mpq_denref(term), fact[i - 1 - 3 * j]);
            mpq_canonicalize(term);
            mpq_mul(term, term, t);
            mpq_add(s, s, term);
        }
        /* a(i) = (i-1)! * s */
        mpz_mul(mpq_numref(s), mpq_numref(s), fact[i - 1]);
        mpq_canonicalize(s);
        mpq_set(a[i], s);
    }

    for (i = 0; i <= N; i++) {
        if (mpz_cmp_ui(mpq_denref(a[i]), 1) != 0) break;
        char *str = mpz_get_str(NULL, 10, mpq_numref(a[i]));
        size_t len = 0;
        while (str[len]) len++;
        if (len > 1000) { free(str); break; }
        printf("%d %s\n", i, str);
        free(str);
    }

    for (i = 0; i <= N; i++) { mpq_clear(a[i]); mpz_clear(fact[i]); }
    mpq_clear(s); mpq_clear(t); mpq_clear(term); mpq_clear(tmp);
    return 0;
}
