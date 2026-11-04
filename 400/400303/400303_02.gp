\\ G.f. A(x) satisfies A(x) = (1-8*x) * (5*A(x*(1-4*x)) - 4).
\\ A = R のとき 4*A = 5*A - R
a(n) = my(A=1); for(i=1, n, A = ( 5*A - (1-8*x) * (5*subst(A, x, x*(1-4*x)) - 4 +x*O(x^n)) )/4); polcoeff(A, n);
for(n=0, 15, print1(a(n), ", "));

