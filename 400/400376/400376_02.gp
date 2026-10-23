\\ a(0) = 1; a(n) = Sum_{k=1..n} A381016(k) * binomial(n,k) * a(n-k).
a381016(n) = -sum(k=1, n\2, (-1)^k*(n-2*k)!*binomial(n, 2*k-1));
a(n) = if(n==0, 1, sum(k=1, n, a381016(k) * binomial(n, k) * a(n-k)));
for(n=0, 18, print1(a(n), ", "));

