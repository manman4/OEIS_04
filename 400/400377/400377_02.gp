\\ a(0) = 1; a(n) = Sum_{k=1..n} (-1)^(k-1) * A009410(k) * binomial(n,k) * a(n-k).
\\ a(n) = Sum_{k=0..floor((n-1)/2)} (-1)^(n-k-1) * binomial(n,2*k) * (n-2*k-1)!. 
a009410(n) = sum(k=0, (n-1)\2, (-1)^(n-k-1) * (n-2*k-1)! * binomial(n, 2*k));
for(n=0, 18, print1(a009410(n), ", "));
a(n) = if(n==0, 1, sum(k=1, n, (-1)^(k-1) * a009410(k) * binomial(n, k) * a(n-k)));
for(n=0, 18, print1(a(n), ", "));

