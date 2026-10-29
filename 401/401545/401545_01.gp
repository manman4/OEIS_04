\\ Square array A(n,k), n >= 1, k >= 0, read by antidiagonals downwards: A(n,k) = n + Sum_{j=0..k-1} tau(A(n,j)).
a(n, k) = for(j=1, k, n+=numdiv(n)); n;
for(n=1, 12, for(k=1, n, print1(a(k, n-k),", ")));

