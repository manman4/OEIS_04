\\ a(0) = 1, a(1) = 2; a(n) = (1/4) * (2^(n+1)*a(n-1) - Sum_{k=2..n-1} a(k) * a(n+1-k)).
print("NG");
a(n) = if(n<1, 1, (1/4) * (2^(n+1)*a(n-1) - sum(k=2, n-1, a(k) * a(n+1-k))));
for(n=0, 8, print1(a(n),", "));

print("OK");
a(n) = if(n<2, 2^n, (1/4) * (2^(n+1)*a(n-1) - sum(k=2, n-1, a(k) * a(n+1-k))));
for(n=0, 8, print1(a(n),", "));