\\ a(0) = 1; a(3*n+1) = 3*a(n), a(3*n+2) = 3*Sum_{k=0..n} a(k)*a(n-k) and a(3*n+3) = Sum_{i,j,k>=0 and i+j+k=n} a(i)*a(j)*a(k) for n >= 0.
a(n) = if(n==0, 1, if(n%3==1, 3*a((n-1)/3), if(n%3==2, 3*sum(k=0, (n-2)/3, a(k)*a((n-2)/3-k)), sum(i=0, (n-3)/3, sum(j=0, (n-3)/3-i, a(i)*a(j)*a((n-3)/3-i-j))))));
for(n=0, 19, print1(a(n), ", "));