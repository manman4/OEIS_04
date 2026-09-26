\\ a(0) = 1; a(2*n+1) = 2*a(n) and a(2*n+2) = Sum_{k=0..n} a(k)*a(n-k) for n >= 0.
a(n) = if(n==0, 1, if(n%2==1, 2*a((n-1)/2), sum(k=0, (n-2)/2, a(k)*a((n-2)/2-k))));
for(n=0, 25, print1(a(n), ", "));

