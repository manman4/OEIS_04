\\ a(0) = 1; a(4*n+1) = 2*a(n), a(4*n+2) = Sum_{k=0..n} a(k)*a(n-k), and a(4*n+3) = a(4*n+4) = 0 for n >= 0.
a(n) = if(n==0, 1, if(n%4==1, 2*a((n-1)/4), if(n%4==2, sum(k=0, (n-2)/4, a(k)*a((n-2)/4-k)), 0)));
for(n=0, 55, print1(a(n), ", "));