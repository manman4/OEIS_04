\\ G.f. A(x) satisfies A(x) = (1-6*x) * (4*A(x*(1-3*x)) - 3).
\\ A = R のとき 3*A = 4*A - R
a(n) = my(A=1); for(i=1, n, A = ( 4*A - (1-6*x) * (4*subst(A, x, x*(1-3*x)) - 3 +x*O(x^n)) )/3); polcoeff(A, n);
for(n=0, 15, print1(a(n), ", "));

