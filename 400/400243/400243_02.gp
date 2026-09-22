\\ G.f. A(x) satisfies A(x) = A(x^2/(1 - x)^3) / (1 - x)^2, with A(0) = 1.
a(n) = my(A=1); for(i=1, n, A = subst(A, x, x^2/(1-x+x*O(x^n))^3) / (1-x+x*O(x^n))^2 ); polcoeff(A, n);
for(n=0, 35, print1(a(n), ", "));