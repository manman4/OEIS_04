\\ E.g.f. A(x) satisfies A(x) = 1/(1 - x*A(x)^(x*A(x))).
\\ Interpret A(x)^(x*A(x)) as exp(x*A(x)*log(A(x))).
\\ Run with: gp -q -f 400589_01.gp, then enter the maximum index.
\\ Output: b400589_01.txt in the current directory (overwritten).

default(parisizemax, 4000000000);

coefficients(N) = {
  if(type(N) != "t_INT" || N < 0,
    error("n must be a nonnegative integer")
  );
  \\ E.g.f. coefficients of A, L = log(A), P = A*L, and H = exp(x*P).
  \\ A = 1 + x*A*H, L' = A*(H+x*H'), H' = H*(P+x*P').
  my(a = vector(N + 1), l = vector(N + 1));
  my(p = vector(N + 1), h = vector(N + 1));
  a[1] = h[1] = 1;

  for(n = 1, N,
    my(sa = 0, sl = 0, sh = 0, choose = 1);
    for(j = 0, n - 1,
      my(r = n - j, ah = choose*a[j + 1]*h[r]);
      sa += ah;
      sl += r*ah;
      sh += choose*r*h[j + 1]*p[r];
      if(j < n - 1, choose = choose*(n - 1 - j)/(j + 1));
    );
    a[n + 1] = n*sa;
    l[n + 1] = sl;
    h[n + 1] = sh;

    \\ P = A*L: p(n) = sum(j=0,n,binomial(n,j)*a(j)*l(n-j)).
    \\ The j=n term vanishes because l(0)=0.
    my(sp = 0);
    choose = 1;
    for(j = 0, n - 1,
      sp += choose*a[j + 1]*l[n - j + 1];
      if(j < n - 1, choose = choose*(n - j)/(j + 1));
    );
    p[n + 1] = sp;
  );
  a;
};

write_bfile(N) = {
  my(values = coefficients(N));
  for(n = 0, N,
    if(type(values[n + 1]) != "t_INT",
      error(Str("nonintegral coefficient at n=", n))
    );
  );

  my(out = fileopen("b400589_01.txt", "w"));
  for(n = 0, N,
    filewrite(out, Str(n, " ", values[n + 1]))
  );
  fileclose(out);
};

{
print1("n = ");
N = input();
write_bfile(N);
}
