\\ Irregular triangle read by rows: T(n,k) is the number of k-element sets of line sizes that can arise from configurations of n distinct points in the real plane, for n >= 1 and 0 <= k <= floor(sqrt(4*n+3)) - 2.
T(n, k) = if(k<2, if(k, min(n-1, 2), n==1), my(r=k-1, cnt=0); forsubset([n-1, r], s, if(s[1]>=3, cnt+=sum(i=1, r, max(0, s[i]+i-r))<=n)); cnt);
for(n=1, 18, for(k=0, sqrtint(4*n+3)-2, print1(T(n, k), ", ")));

