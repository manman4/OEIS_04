T(n, k) = if(k<2, if(k, min(n-1, 2), n==1), my(r=k-1, cnt=0); forsubset([n-1, r], s, if(s[1]>=3, cnt+=sum(i=1, r, max(0, s[i]+i-r))<=n)); cnt);
a(n) = sum(k=0, sqrtint(4*n+3)-2, T(n, k));
for(n=1, 30, print1(a(n), ", "));

