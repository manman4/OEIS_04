\\ G.f. A(x) satisfies A(x) = 1/(1 - x * A(x^4))^2.
a(n) = my(A=1+x*O(x^n)); for(i=0, n, A=1/(1-x*subst(A, x, x^4) + x*O(x^n))^2); Vec(A);
a(50)

\\ G.f.: B(x)^2 where B(x) is the g.f. of A399166.
a(n) = my(A=1+x*O(x^n)); for(i=0, n, A=1/(1-x*subst(A, x, x^4) + x*O(x^n))^2); Vec(A^(1/2));
a(50)
