sums(S) = my(V=[0]); for(j=1,#S,V=setunion(V,Set(vector(#V,i,V[i]+S[j])))); V;
a(n) = my(H=n*(n+1)/2,V=vector(H)); forsubset(n,S,my(W=sums(S)); 
for(m=1,H,if(!setsearch(W,m),V[m]=max(V[m],#S)))); vecmin(V);

for(n=1, 10, print1(a(n),", "));
