\\ a(n) = Product_{k=prime(n)+1..prime(n+1)-1} A014963(k).
a(n) = my(p); prod(k=prime(n)+1, prime(n+1)-1, if(isprimepower(k, &p), p, 1));
for(n=1, 100, print1(a(n), ", "));

