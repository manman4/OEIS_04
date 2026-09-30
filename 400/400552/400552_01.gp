\\ E.g.f. A(x) satisfies A(x) = 1/(1 - x*A(x)^(x^3)).
\\ Interpret A(x)^(x^3) as exp(x^3*log(A(x))).
\\ Run with: gp -q -f 400552_01.gp, then enter the maximum index.
\\ Output: b400552_01.txt in the current directory (overwritten).

default(parisizemax, 4000000000);

coefficients(N) = {
  if(type(N) != "t_INT" || N < 0,
    error("n must be a nonnegative integer")
  );
  \\ E.g.f. coefficients of A, H = exp(x^3*log(A)), and L = log(A).
  \\ A = 1 + x*A*H, H' = H*(3*x^2*L+x^3*L'), L' = A*(H+x*H').
  my(a = vector(N + 1), h = vector(N + 1), l = vector(N + 1));
  a[1] = h[1] = 1;

  for(n = 1, N,
    my(sa = 0, sh = 0, sl = 0, choose = 1);
    for(j = 0, n - 1,
      my(r = n - j, ah = choose*a[j + 1]*h[r]);
      sa += ah;
      sl += r*ah;
      if(r >= 3, sh += choose*r*(r - 1)*(r - 2)*h[j + 1]*l[r - 2]);
      if(j < n - 1, choose = choose*(n - 1 - j)/(j + 1));
    );
    a[n + 1] = n*sa;
    h[n + 1] = sh;
    l[n + 1] = sl;
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

  my(out = fileopen("b400552_01.txt", "w"));
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
