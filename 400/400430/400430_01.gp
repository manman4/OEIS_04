\\ a(n) = max_{1 <= k < n} (k + omega(k)) - n, where omega(k) is the number of distinct prime divisors of k.
a(n) = vecmax(vector(n-1, k, k+omega(k)))-n;
for(n=2, 100, print1(a(n), ", "));

