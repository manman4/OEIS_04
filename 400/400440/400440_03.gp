\\ a(0) = 1; a(n) = (1/n) * Sum_{k=0..floor((n-1)/4)} (12*k+3-n)*a(k)*a(n-1-4*k).
a(n) = if(n==0, 1, 1/n * sum(k=0, (n-1)\4, (12*k+3-n)*a(k)*a(n-1-4*k)));
for(n=0, 30, print1(a(n), ", "));

