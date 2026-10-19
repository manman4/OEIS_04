\\ Number of pairs of coprime positive integers i < j < n with sigma(i) = sigma(j), where sigma is the sum of divisors function.
a(n) = sum(i=1, n-2, sum(j=i+1, n-1, gcd(i, j)==1 && sigma(i)==sigma(j)));
for(n=1, 101, print1(a(n), ", "));

