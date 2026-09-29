\\ OEIS A400528
\\
\\ E.g.f. A(x) satisfies
\\
\\   A(x) = exp(x*A(x^3)^2).
\\
\\ Put B(x) = A(x)^2.  The coefficient recurrences used below are
\\
\\   b(n+1) = 2*sum(k=0, floor(n/3),
\\     (3*k+1)*n!/(k!*(n-3*k)!)*b(k)*b(n-3*k)),
\\
\\   a(n+1) = sum(k=0, floor(n/3),
\\     (3*k+1)*n!/(k!*(n-3*k)!)*b(k)*a(n-3*k)).
\\
\\ Each inner weight is updated from the preceding one, so factorials are
\\ not recomputed in the loop.

write_bfile(N) = {
  if(type(N) != "t_INT" || N < 0,
    error("n must be a nonnegative integer")
  );

  my(a = vector(N + 1), b = vector(N + 1));
  a[1] = 1;
  b[1] = 1;

  for(n = 0, N - 1,
    my(sum_a = 0, sum_b = 0, weight = 1, last_k = n \ 3);

    for(k = 0, last_k,
      my(factor = (3*k + 1)*weight);
      sum_a += factor*b[k + 1]*a[n - 3*k + 1];
      sum_b += factor*b[k + 1]*b[n - 3*k + 1];

      if(k < last_k,
        weight = weight*(n - 3*k)*(n - 3*k - 1)*(n - 3*k - 2)/(k + 1)
      );
    );

    a[n + 2] = sum_a;
    b[n + 2] = 2*sum_b;
  );

  my(out = fileopen("b400528_01.txt", "w"));
  for(n = 0, N,
    filewrite(out, Str(n, " ", a[n + 1]))
  );
  fileclose(out);
};

{
print1("n = ");
N = input();
write_bfile(N);
}
