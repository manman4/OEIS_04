F(n,u,v)=my(r=0,t); for(i=u,logint(n,2),for(j=0,min(v,logint(n\2^i,3)),t=2^i*3^j; r=max(r,if(t==n,t,min(t,F(n-t,i+1,j-1)))))); r;
a(n)=F(n,0,logint(n,3));
for(n=1, 101, print1(a(n), ", "));

