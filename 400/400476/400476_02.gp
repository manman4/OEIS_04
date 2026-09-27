\\ a(0) = 1; a(2*n+1) = 3*a(n) + Sum_{i,j,k>=0 and i+j+k=n-1} a(i)*a(j)*a(k) and a(2*n+2) = 3*Sum_{k=0..n} a(k)*a(n-k) for n >= 0.
a(n) = if(n==0, 1, if(n%2==1, 3*a((n-1)/2) + sum(i=0, (n-1)/2-1, sum(j=0, (n-1)/2-1-i, a(i)*a(j)*a((n-1)/2-1-i-j))), 3*sum(k=0, (n-2)/2, a(k)*a((n-2)/2-k))));
for(n=0, 16, print1(a(n), ", "));

