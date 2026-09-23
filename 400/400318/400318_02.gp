\\ G.f. A(x) satisfies A(x) = (1 + x)^3 * A(x^4 * (1 + x)), with A(0) = 1.
a(n) = my(A=1); for(i=1, n, A = (1+x)^3 * subst(A, x, x^4 * (1+x+x*O(x^n))) ); polcoeff(A, n);
for(n=0, 35, print1(a(n), ", "));

v(n) = my(A=1); for(i=1, n, A = (1+x)^3 * subst(A, x, x^4 * (1+x+x*O(x^n))) ); Vec(A);
v(35)
\\ G.f.: B(x)^3 where B(x) is the g.f. of A400271.
v(n) = my(A=1); for(i=1, n, A = (1+x)^3 * subst(A, x, x^4 * (1+x+x*O(x^n))) ); Vec(A^(1/3));
v(35)