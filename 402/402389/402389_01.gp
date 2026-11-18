\\ G.f.: 1/((1-x) * (1 - Sum_{k>=1} (k*x)^k)).
my(N=30, x='x+O('x^N)); Vec(1/((1-x)*(1-sum(k=1, N, (k*x)^k))))

