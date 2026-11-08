\\ a(n) = n - #{1 <= k <= n : k is odd and squarefree}.
a(n) = n-sum(k=1, (n+1)\2, issquarefree(2*k-1));
for(n=1, 100, print1(a(n),", "));

