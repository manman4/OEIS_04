\\ a(0) = 1; a(n) = n! * Sum_{j=0..floor((n-1)/2)} (n-j)^(j-1) * Sum_{k=j+1..n-j} binomial(n+j,2*j+k) * Stirling1(k-1,j)/(k-1)!.
a(n) = if(n==0, 1, n!*sum(j=0, (n-1)\2, (n-j)^(j-1)*sum(k=j+1, n-j, binomial(n+j, 2*j+k)*stirling(k-1, j, 1)/(k-1)!)));
for(n=0, 16, print1(a(n),", "));

print("以下はNG");
a(n) = n!*sum(j=0, (n-1)\2, (n-j)^(j-1)*sum(k=j+1, n-j, binomial(n+j, 2*j+k)*stirling(k-1, j, 1)/(k-1)!));
for(n=0, 16, print1(a(n),", "));