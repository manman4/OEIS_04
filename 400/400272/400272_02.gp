\\ G.f. A(x) satisfies A(x) = (1 + x) * A(x^4 * (1 + x)^2), with A(0) = 1.
a(n) = my(A=1); for(i=1, n, A = (1+x) * subst(A, x, x^4 * (1+x+x*O(x^n))^2) ); polcoeff(A, n);
for(n=0, 35, print1(a(n), ", "));