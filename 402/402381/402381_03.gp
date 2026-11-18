M=14;

\\ a(n) = 2 * (4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4)).
a(n) = my(v=[1, 5, 31, 195]); if(n<4, v[n+1], 2 * (4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4)));
for(n=0, M, print1(a(n), ", "));

\\ Partial sums of A145840.
for(n=0, M, print1(a(n+1)-a(n), ", "));




