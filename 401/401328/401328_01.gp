s(n, k) = my(r=1); forprime(p=2, k-1, r*=p^valuation(n, p)); r;
a(n, k) = #Set(vector(k, j, s(n+j, k)));

for(n=0, 12, for(k=0, n, print1(a(k,n-k+1),", ")));