\\ a(0) = 1; a(n) = n! * Sum_{j=0..floor((n-1)/3)} (n-2*j)^j * Sum_{k=j+1..n-2*j} binomial(n-2*j-1,k-1) * Stirling1(k-1,j)/k!.
a(n) = if(n==0, 1, n!*sum(j=0, (n-1)\3, (n-2*j)^j*sum(k=j+1, n-2*j, binomial(n-2*j-1, k-1)*stirling(k-1, j, 1)/k!)));
for(n=0, 15, print1(a(n),", "));

print("以下はNG");
a(n) = n!*sum(j=0, (n-1)\3, (n-2*j)^j*sum(k=j+1, n-2*j, binomial(n-2*j-1, k-1)*stirling(k-1, j, 1)/k!));
for(n=0, 15, print1(a(n),", "));

