\\ OEIS A400527
\\
\\ E.g.f. A(x) satisfies
\\
\\   A(x) = exp(x*A(x^2)^2).
\\
\\ Put B(x) = A(x)^2.  The coefficient recurrences used below are
\\
\\   b(n+1) = 2*sum(k=0, floor(n/2),
\\     (2*k+1)*n!/(k!*(n-2*k)!)*b(k)*b(n-2*k)),
\\
\\   a(n+1) = sum(k=0, floor(n/2),
\\     (2*k+1)*n!/(k!*(n-2*k)!)*b(k)*a(n-2*k)).
\\
\\ Each inner weight is updated from the preceding one, so factorials are
\\ not recomputed in the loop.

\\ 実行
\\ ls -l 400527_01.gp    
\\ gp -q -f ./400527_01.gp

write_bfile(N) = {
  if(type(N) != "t_INT" || N < 0,
    error("n must be a nonnegative integer")
  );

  my(a = vector(N + 1), b = vector(N + 1));
  a[1] = 1;
  b[1] = 1;

  for(n = 0, N - 1,
    my(sum_a = 0, sum_b = 0, weight = 1, last_k = n \ 2);

    for(k = 0, last_k,
      my(factor = (2*k + 1)*weight);
      sum_a += factor*b[k + 1]*a[n - 2*k + 1];
      sum_b += factor*b[k + 1]*b[n - 2*k + 1];

      if(k < last_k,
        weight = weight*(n - 2*k)*(n - 2*k - 1)/(k + 1)
      );
    );

    a[n + 2] = sum_a;
    b[n + 2] = 2*sum_b;
  );

  my(out = fileopen("b400527_01.txt", "w"));
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
