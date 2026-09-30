\\ a(0) = 1; a(n) = n! * Sum_{j=0..floor(n/3)} j^(n-3*j) * Sum_{k=n-3*j+1..j} binomial(j-1,k-1) * Stirling2(k-1,n-3*j)/k!.
a(n) = if(n==0, 1, n!*sum(j=0, n\3, j^(n-3*j)*sum(k=n-3*j+1, j, binomial(j-1, k-1)*stirling(k-1, n-3*j, 2)/k!)));
for(n=0, 15, print1(a(n),", "));

print("以下はNG");
a(n) = n!*sum(j=0, n\3, j^(n-3*j)*sum(k=n-3*j+1, j, binomial(j-1, k-1)*stirling(k-1, n-3*j, 2)/k!));
for(n=0, 15, print1(a(n),", "));

