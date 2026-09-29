\\ E.g.f. A(x) satisfies A(x) = exp(2*x*A(x^3)).
a(n) = my(A=1+x*O(x^n)); for(i=0, n, A=exp(2*x*subst(A, x, x^3) + x*O(x^n))); Vec(serlaplace(A));
a(30)

\\ E.g.f.: B(x)^2 where B(x) is the e.g.f. of A400528.
a(n) = my(A=1+x*O(x^n)); for(i=0, n, A=exp(2*x*subst(A, x, x^3) + x*O(x^n))); Vec(serlaplace(A^(1/2)));
a(30)