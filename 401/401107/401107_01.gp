\\ Triangle read by rows: T(n,k) = max{d : 1 <= d <= n and d | binomial(n,k)}, for n >= 2 and 1 <= k < n.
T(n, k) = my(b=binomial(n, k), d=n); while(b%d, d--); d;
for(n=2, 13, for(k=1, n-1, print1(T(n, k), ", ")));

