M=17;

\\ a(n) = 1 + Sum_{k=1..n} k^n * a(n-k).
a(n) = 1 + sum(k=1, n, k^n * a(n-k));
for(n=0, 10, print1(a(n), ", "));

a_vector(n) = my(v=vector(n+1)); for(i=0, n, v[i+1]=1+sum(j=1, i, j^i*v[i-j+1])); v;
a_vector(M)

