\\ Square array A(n,k), n >= 1, k >= 1, read by antidiagonals downwards, where A(n,k) is the number of integers j with n < j <= n+k whose greatest prime factor exceeds k.
a(n, k) = sum(j=1, k, vecmax(factor(n+j)[, 1])>k);
for(n=1, 13, for(k=1, n, print1(a(k, n-k+1), ", ")));

