M=30;

\\ a(n) = n! * Sum_{k=0..floor(n/5)} (n+1)^(k-1) * |Stirling1(n-4*k,k)|/(n-4*k)!.
a(n) = n!*sum(k=0, n\5, (n+1)^(k-1)*abs(stirling(n-4*k, k, 1))/(n-4*k)!);
for(n=0, M, print1(a(n), ", "));
