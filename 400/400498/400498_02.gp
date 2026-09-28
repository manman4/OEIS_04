\\ a(0) = 1; a(n) = (1/n) * Sum_{k=0..floor((n-1)/5)} (n+5*k+1)*a(k)*a(n-1-5*k).
a(n) = if(n==0, 1, sum(j=0, (n-1)\5, (n+5*j+1)*a(j)*a(n-1-5*j))/n);
for(n=0, 15, print1(a(n), ", "));

