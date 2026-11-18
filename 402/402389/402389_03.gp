M=14;

\\ Partial sums of A277610.
{a277610(n) = polcoeff( 1/(1 - sum(k=1, n+1, k^k * x^k +x*O(x^n)) ), n)};
a(n) = sum(i=0, n, a277610(i));
for(n=0, M, print1(a(n), ", "));




