\\ a(0) = 1; a(n) = Sum_{k=0..floor(n/4)} binomial(n-3*k+1,k+1) * a(k).
a(n) = if(n==0, 1, sum(k=0, n\4, binomial(n-3*k+1, k+1) * a(k))); 
for(n=0, 15, print1(a(n), ", "));

a_vector(n) = my(v=vector(n+1)); v[1]=1; for(i=1, n, v[i+1]=sum(j=0, i\4, binomial(i-3*j+1, j+1)*v[j+1])); v;
a_vector(45)