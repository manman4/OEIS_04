\\ a(n) = max_{1 <= k < n} (k + tau(k)) - n, where tau(k) is the number of positive divisors of k.
a(n) = vecmax(vector(n-1, k, k+numdiv(k)))-n;
for(n=2, 100, print1(a(n), ", "));

