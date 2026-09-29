\\ E.g.f. A(x) satisfies A(x) = exp(x*A(x^3)^2).
a(n) = my(A=1+x*O(x^n)); for(i=0, n, A=exp(x*subst(A, x, x^3)^2 + x*O(x^n))); Vec(serlaplace(A));
a(50)

