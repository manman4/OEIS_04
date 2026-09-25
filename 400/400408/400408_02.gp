M=30;

\\ E.g.f. A(x) satisfies A(x) = 1/(1 - x*A(x))^(x^4*A(x)^4).
seq(n) = my(A=1); for(i=1, n, A=1/(1-x*A + x*O(x^n))^(x^4*A^4)); Vec(serlaplace(A));
seq(M) 


