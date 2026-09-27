\\ a(0) = 1; a(2*n+1) = 4*a(n) + 4*Sum_{i,j,k>=0 and i+j+k=n-1} a(i)*a(j)*a(k) and a(2*n+2) = 6*Sum_{k=0..n} a(k)*a(n-k) + Sum_{i,j,k,l>=0 and i+j+k+l=n-1} a(i)*a(j)*a(k)*a(l) for n >= 0.
a(n) = if(n==0, 1, if(n%2==1, 4*a((n-1)/2) + 4*sum(i=0, (n-1)/2-1, sum(j=0, (n-1)/2-1-i, a(i)*a(j)*a((n-1)/2-1-i-j))), 6*sum(k=0, (n-2)/2, a(k)*a((n-2)/2-k)) + sum(i=0, (n-2)/2-1, sum(j=0, (n-2)/2-1-i, sum(k=0, (n-2)/2-1-i-j, a(i)*a(j)*a(k)*a((n-2)/2-1-i-j-k))))));
for(n=0, 16, print1(a(n), ", "));


