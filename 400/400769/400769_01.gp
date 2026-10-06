M=79;
a(n) = moebius(n^2+n+1);
for(n=0, M, print1(a(n),", "));

\\ a(n) = A008683(A002061(n+1)).
a002061(n) = n^2 - n + 1;
b(n) = moebius(a002061(n+1));
for(n=0, M, print1(a(n)-b(n),", "));
