M=30;

\\ a(n) = n! * Sum_{k=0..floor(n/4)} (n+1)^(n-4*k-1) * |Stirling1(k,n-4*k)|/k!.
a(n) = n!*sum(k=0, n\4, (n+1)^(n-4*k-1)*abs(stirling(k, n-4*k, 1))/k!);
for(n=0, M, print1(a(n), ", "));
