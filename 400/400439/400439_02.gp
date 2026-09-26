\\ a(0) = 1; a(3*n+1) = 2*a(n), a(3*n+2) = Sum_{k=0..n} a(k)*a(n-k), and a(3*n+3) = 0 for n >= 0.
a(n) = if(n==0, 1, if(n%3==1, 2*a((n-1)/3), if(n%3==2, sum(k=0, (n-2)/3, a(k)*a((n-2)/3-k)), 0)));
for(n=0, 25, print1(a(n), ", "));