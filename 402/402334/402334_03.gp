M=25;

\\ E.g.f.: d^4/dx^4 ( (1 - x - x^2/2 - x^3/6)/(2 - exp(x)) ).
my(N=M, x='x+O('x^N)); Vec(serlaplace(deriv(deriv(deriv(deriv((1 - x - x^2/2 - x^3/6)/(2 - exp(x))))))))


\\ a(n) = (n+4)! * [x^(n+4)] (exp(x) - 1 - x - x^2/2 - x^3/6)/(2 - exp(x)).
a(n) = my(x='x+O('x^(n+5))); (n+4)! * polcoeff((exp(x) - 1 - x - x^2/2 - x^3/6)/(2 - exp(x)), n+4);
for(n=0, M, print1(a(n), ", "));

