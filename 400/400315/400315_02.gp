\\ G.f. A(x) satisfies A(x) = A(x^4/(1 - x)) / (1 - x)^2, with A(0) = 1.
a(n) = my(A=1); for(i=1, n, A = subst(A, x, x^4/(1-x+x*O(x^n))) / (1-x+x*O(x^n))^2 ); polcoeff(A, n);
for(n=0, 35, print1(a(n), ", "));

v(n) = my(A=1); for(i=1, n, A = subst(A, x, x^4/(1-x+x*O(x^n))) / (1-x+x*O(x^n))^2 ); Vec(A);
v(35)
\\ G.f.: B(x)^2 where B(x) is the g.f. of A352041.
v(n) = my(A=1); for(i=1, n, A = subst(A, x, x^4/(1-x+x*O(x^n))) / (1-x+x*O(x^n))^2 ); Vec(A^(1/2));
v(35)