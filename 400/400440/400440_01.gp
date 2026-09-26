series_a(M) = {
  if(M < 0, error("M must be nonnegative"));
  if(M == 0, return(1 + O(x)));

  my(N = (M - 1) \ 4);
  my(S = series_a(N));
  my(S2 = S^2);

  \\ Expand the square before substituting.  Squaring S at degree about M/4
  \\ is much faster than squaring the degree-M sparse substitution directly.
  1 + 2*x*subst(S, x, x^4)
    + x^2*subst(S2, x, x^4)
    + O(x^(M + 1));
};

{
M = 10000;
v = series_a(M);

\\ Open once in write mode.  This both truncates an existing b-file and
\\ avoids reopening the file for every coefficient.
out = fileopen("b400440_1.txt", "w");
for(n = 0, M,
  filewrite(out, Str(n, " ", polcoef(v, n)))
);
fileclose(out);
}

