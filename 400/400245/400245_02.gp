\\ G.f. A(x) satisfies A(x) = A(x^2/(1 - x)^3) / (1 - x)^3, with A(0) = 1.
a(n) = my(A=1); for(i=1, n, A = subst(A, x, x^2/(1-x+x*O(x^n))^3) / (1-x+x*O(x^n))^3 ); polcoeff(A, n);
for(n=0, 35, print1(a(n), ", "));

v(n) = my(A=1); for(i=1, n, A = subst(A, x, x^2/(1-x+x*O(x^n))^3) / (1-x+x*O(x^n))^3 ); Vec(A);
v(35)
\\ G.f.: B(x)^3 where B(x) is the g.f. of A400241.
v(n) = my(A=1); for(i=1, n, A = subst(A, x, x^2/(1-x+x*O(x^n))^3) / (1-x+x*O(x^n))^3 ); Vec(A^(1/3));
v(35)