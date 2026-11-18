M=14;

\\ Partial sums of A051296.
\\ a(0) = 1; a(n) = Sum_{k=1..n} a(n-k)*k! for n>0.
a051296(n) = if(n==0, 1, sum(k=1, n, a051296(n-k)*k!));
a(n) = sum(i=0, n, a051296(i));
for(n=0, M, print1(a(n), ", "));




