\\ E.g.f. A(x) satisfies A(x) = 1/(1 - x*A(x)^x).
\\ Interpret A(x)^x as exp(x*log(A(x))).
\\ Run with: gp -q -f 400548_01.gp, then enter the maximum index.
\\ Output: b400548_01.txt in the current directory (overwritten).

default(parisizemax, 4000000000);

series_a(N) = {
  if(type(N) != "t_INT" || N < 0,
    error("n must be a nonnegative integer")
  );
  my(A = 1 + O(x^(N + 1)), q = 1);

  \\ An error O(x^q) becomes O(x^(q+2)) after one defining iteration.
  while(q <= N,
    A = 1/(1 - x*exp(x*log(A)) + O(x^(N + 1)));
    q += 2;
  );
  A;
};

write_bfile(N) = {
  my(A = series_a(N), values = vector(N + 1), factorial = 1);
  for(n = 0, N,
    if(n > 0, factorial *= n);
    values[n + 1] = factorial*polcoef(A, n);
    if(type(values[n + 1]) != "t_INT",
      error(Str("nonintegral coefficient at n=", n))
    );
  );

  my(out = fileopen("b400548_01.txt", "w"));
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
