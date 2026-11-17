M=20;

{a000670(n) = polcoeff(sum(m=0, n, m!*x^m/prod(k=1, m, 1-k*x+x*O(x^n))), n)};
\\ a(n) = A000670(n+3) - (n+3)*A000670(n+2) - binomial(n+3,2)*A000670(n+1).
a(n) = a000670(n+3) - (n+3)*a000670(n+2) - binomial(n+3,2)*a000670(n+1);
for(n=0, M, print1(a(n), ", "));




