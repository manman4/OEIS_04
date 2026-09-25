\\ E.g.f.: (1/x) * Series_Reversion( x*(1 - x^3)^x ).
my(N=40, x='x+O('x^N)); Vec(serlaplace(serreverse(x*(1-x^3)^x)/x))


