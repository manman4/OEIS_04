M=10000;
a(n) = sum(k=0, n, moebius(k^2+1));
for(n=0, M, write("b400698.txt", n, " ", a(n)));

