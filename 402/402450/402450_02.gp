M=25;

\\ G.f. A(x) satisfies A(x) = (1-4*x) * (2*A(z) - 1/(1-z)), where z = x*(1-x)^3.
\\ A = R のとき A = 2*A - R
a(n) = my(A=1, z=x*(1-x)^3 + x*O(x^n)); for(i=1, n, A = 2*A - (1-4*x) * (2*subst(A, x, z) - 1/(1 - z) +x*O(x^n)) ); polcoeff(A, n);
for(n=0, M, print1(a(n), ", "));
