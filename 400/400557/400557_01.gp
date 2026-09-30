\\ E.g.f. A(x) satisfies A(x) = 1/( 1 - x*exp( x^3*( exp(A(x)-1)-1 ) ) ).
a(n) = my(A=1+x*O(x^n)); for(i=0, n, A=1/(1-x*exp(x^3*(exp(A-1 +x*O(x^n))-1))) ); Vec(serlaplace(A));
a(25)
