\\ OEIS A400480
\\
\\ Compute A(x) through x^M from
\\
\\   A(x) = (1 + x*A(x^2))^4.
\\
\\ No coefficient recurrence or recursive coefficient computation is used.
\\ Starting with A = 1, iterate the defining equation itself.  If the
\\ current approximation is correct modulo x^q, one more iteration is
\\ correct modulo x^(2*q+1), so only logarithmically many iterations are
\\ needed.

\\ Allow PARI/GP to enlarge its stack during the degree-10000 products.
default(parisizemax, 4000000000);

series_a(M) = {
  if(M < 0, error("M must be nonnegative"));
  my(A = 1, q = 1);

  while(q <= M,
    A = (1 + x*subst(A, x, x^2) + O(x^(M + 1)))^4;
    q = 2*q + 1;
  );
  A;
};

{
M = 10000;
v = series_a(M);

\\ Open once in write mode.  This truncates an existing b-file and avoids
\\ reopening the file for every coefficient.
out = fileopen("b400480_1.txt", "w");
for(n = 0, M,
  filewrite(out, Str(n, " ", polcoef(v, n)))
);
fileclose(out);
}
