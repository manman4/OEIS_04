M=20;

\\ G.f. A(x) satisfies A(x) = (1-3*x)/(1+x) * (2*A(z) - 1/(1-z)), where z = x/(1+x)^4.
\\ A = R のとき A = 2*A - R
a(n) = my(A=1); for(i=1, n, A = 2*A - (1-3*x)/(1+x + x*O(x^n)) * (2*subst(A, x, x/(1+x)^4) - 1/(1 - x/(1+x)^4) +x*O(x^n)) ); polcoeff(A, n);
for(n=0, M, print1(a(n), ", "));