M=17;

\\ G.f. A(x) satisfies A(x) = 1/(1-x) + Sum_{k>=1} (k*x)^k * A(k*x).
a(n) = my(A=1, x='x+O('x^(n+1))); for(i=1, n, A = 1/(1-x) + sum(k=1, n, (k*x)^k*subst(A, 'x, k*x))); Vec(A);
a(M)

