\\ a(n) = Sum_{k=1..n} A046801(k).
a(n) = sum(k=1, n, numdiv(2^k-1));
for(n=1, 100, print1(a(n),", "));
