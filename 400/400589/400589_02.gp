\\ E.g.f. A(x) satisfies A(x) = 1/(1 - x*A(x)^(x*A(x))).
a(n) = my(A=1+x*O(x^n)); for(i=0, n, A=1/(1-x*A^(x*A +x*O(x^n))) ); Vec(serlaplace(A));
a(20)
