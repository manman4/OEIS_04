M=25;

\\ G.f. A(x) satisfies 2*A(x) - 1/(1-x) = A(x/(1-x))/(1-x)^4.
a(n) = my(A=1, x='x+O('x^(n+1))); for(n=0, M, A = -A + 1/(1-x) + subst(A, 'x, x/(1-x))/(1-x)^4 ); polcoeff(A, n);
for(n=0, M, print1(a(n), ", "));

\\ G.f. A(x) satisfies A(x) = (2*A(z) - 1/(1-z))/(1+x)^4, where z = x/(1+x).
\\ A = R のとき A = 2*A - R
a(n) = my(A=1, z=x/(1+x) + x*O(x^n)); for(i=1, n, A = 2*A - (2*subst(A, x, z) - 1/(1 - z) +x*O(x^n))/(1+x)^4 ); polcoeff(A, n);
for(n=0, M, print1(a(n), ", "));