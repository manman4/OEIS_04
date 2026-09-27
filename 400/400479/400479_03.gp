\\ a(0) = 1; a(n) = (1/n) * Sum_{k=0..floor((n-1)/3)} (12*k+4-n)*a(k)*a(n-1-3*k).
a(n) = if(n==0, 1, 1/n * sum(k=0, (n-1)\3, (12*k+4-n)*a(k)*a(n-1-3*k)));
for(n=0, 16, print1(a(n), ", "));