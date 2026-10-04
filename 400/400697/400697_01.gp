M=100;
\\ a(n) = A008966(n^2 + 3).
a(n) = issquarefree(n^2+3);
for(n=0, M, print1(abs(a(n)), ", "));

