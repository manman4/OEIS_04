T(n, k) = if(k<2, if(k, (n>1)+(n>2), n==1), my(r=k-1, c=0); forsubset([max(0, n-3), r], s, c+=sum(i=1, r, max(0, s[i]+2+i-r))<=n); c);
for(n=1, 18, for(k=0, sqrtint(4*n+3)-2, print1(T(n, k), ", ")));

