\\ a(0) = 1; a(n) = Sum_{k=1..n} binomial(n+k+1,k) * a(n-k).
a(n,s) = if(n==0, 1, sum(k=1,n, binomial(n+k+s,k)*a(n-k,s)));
for(n=0, 15, print1(a(n,1), ", "));

a_vector(n) = my(v=vector(n+1)); v[1]=1; for(i=1, n, v[i+1]=sum(j=1, i, binomial(i+j+1, j)*v[i-j+1])); v;
a_vector(25)
