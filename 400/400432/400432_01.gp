\\ G.f. A(x) satisfies A(x) = 1 + 3*x*A(3*x)^(1/3).
a(n) = my(A=1); for(i=0, n, A=1 + 3*x*subst(A, x, 3*x)^(1/3) + x*O(x^n)); Vec(A);
a(30)
