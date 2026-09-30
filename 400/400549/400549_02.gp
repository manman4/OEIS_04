\\ E.g.f. A(x) satisfies A(x) = 1/(1 - x^2*A(x)^x).
a(n) = my(A=1+x*O(x^n)); for(i=0, n, A=1/(1-x^2*A^x + x*O(x^n)) ); Vec(serlaplace(A));
a(25)
