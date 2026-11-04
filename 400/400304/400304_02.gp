\\ G.f. A(x) satisfies A(x) = (1-4*x) * (3*A(x*(1-2*x)) - 2).
\\ A = R のとき 2*A = 3*A - R
a(n) = my(A=1); for(i=1, n, A = ( 3*A - (1-4*x) * (3*subst(A, x, x*(1-2*x)) - 2 +x*O(x^n)) )/2); polcoeff(A, n);
for(n=0, 15, print1(a(n), ", "));

