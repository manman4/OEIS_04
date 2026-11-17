M=25;

\\ E.g.f.: d^3/dx^3 ( (1 - x - x^2/2)/(2 - exp(x)) ).
my(N=M, x='x+O('x^N)); Vec(serlaplace(deriv(deriv(deriv((1 - x - x^2/2)/(2 - exp(x)))))))


\\ a(n) = (n+3)! * [x^(n+3)] (exp(x) - 1 - x - x^2/2)/(2 - exp(x)).
a(n) = my(x='x+O('x^(n+4))); (n+3)! * polcoeff((exp(x) - 1 - x - x^2/2)/(2 - exp(x)), n+3);
for(n=0, M, print1(a(n), ", "));

