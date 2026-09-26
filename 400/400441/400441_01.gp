M=10000;
a(n) = my(A=1); for(i=0, n, A=(1+x*subst(A, x, x^5) +x*O(x^n))^2); A;
v=a(M);
for(n=0, M, write("b400441_1.txt", n, " ", polcoef(v, n)));

