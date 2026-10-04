M=100;
\\ a(n) = A008966(n^2 + 2).
a(n) = issquarefree(n^2+2);
for(n=0, M, print1(abs(a(n)), ", "));

