\\ Square array A(n,k), n >= 1, k >= 1, read by antidiagonals downwards, where A(n,k) is the number of integers j with n < j <= n+k whose greatest prime factor exceeds k.
a(n, k) = sum(j=1, k, vecmax(factor(n+j)[, 1])>k);
for(n=1, 13, for(k=1, n, print1(a(k, n-k+1), ", ")));


\\ For 1 <= k <= n, A(n,k) = k - A080786(n+k,k) + A080786(n,k).
B(n,k) = 1 + sum(j=2,n,vecmax(factor(j)[,1])<=k);
for(n=1, 13, for(k=1, n, print1(B(n, k), ", ")));

A(n,k) = k - B(n+k,k) + B(n,k);
for(n=1, 13, for(k=1, n, print1(a(k, n-k+1)-A(k, n-k+1), ", ")));
