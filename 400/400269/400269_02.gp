\\ G.f. A(x) satisfies A(x) = (1 + x) * A(x^3 * (1 + x)^4), with A(0) = 1.
a(n) = my(A=1); for(i=1, n, A = (1+x) * subst(A, x, x^3 * (1+x + O(x^n))^4) ); polcoeff(A, n);
for(n=0, 35, print1(a(n), ", "));