\\ a(0) = 1, a(1) = 3; a(n) = (1/27) * (3^(n+2)*a(n-1) - Sum_{1<=i,j,k<=n-1 and i+j+k=n+2} a(i) * a(j) * a(k)).
print("NG");
a(n) = if(n<1, 1, (1/27) * (3^(n+2)*a(n-1) - sum(i=1, n-1, sum(j=1, n-1, sum(k=1, n-1, if(i+j+k==n+2, a(i) * a(j) * a(k), 0))))));
for(n=0, 8, print1(a(n),", "));

print("OK");
a(n) = if(n<2, 3^n, (1/27) * (3^(n+2)*a(n-1) - sum(i=1, n-1, sum(j=1, n-1, sum(k=1, n-1, if(i+j+k==n+2, a(i) * a(j) * a(k), 0))))));
for(n=0, 8, print1(a(n),", "));