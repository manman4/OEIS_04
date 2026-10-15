\\ a(n) = min_{1 <= k < n} max{d : 1 <= d <= n and d | binomial(n,k)}.
a401107(n, k) = my(b=binomial(n, k), d=n); while(b%d, d--); d;
a(n) = vecmin(vector(n\2, k, a401107(n, k)));
for(n=2, 72, print1(a(n), ", "));

\\ a(n) = n if and only if n is prime.
for(n=2, 100, if(a(n) == n, print1(n, ", ")));
