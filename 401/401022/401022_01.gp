\\ a(n) = A065331(n*(n+1))
a(n) = 2^valuation(n*(n+1), 2)*3^valuation(n*(n+1), 3);
for(n=1, 100, print1(a(n), ", "));

\\ A065331(n) * A065331(n+1).
b(n) = 2^valuation(n, 2)*3^valuation(n, 3);
c(n) = b(n) * b(n+1);
for(n=1, 100, print1(a(n)-c(n), ", "));

