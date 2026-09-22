\\ G.f. A(x) satisfies A(x) = A(x^3/(1 - x)^4) / (1 - x)^3, with A(0) = 1.
a(n) = my(A=1); for(i=1, n, A = subst(A, x, x^3/(1-x+x*O(x^n))^4) / (1-x+x*O(x^n))^3 ); polcoeff(A, n);
for(n=0, 35, print1(a(n), ", "));