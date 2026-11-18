M=14;

\\ a(n) = 2 * (3*a(n-1) - 3*a(n-2) + a(n-3)).
a(n) = my(v=[1, 4, 19]); if(n<3, v[n+1], 2 * (3*a(n-1) - 3*a(n-2) + a(n-3)));
for(n=0, M, print1(a(n), ", "));

\\ Partial sums of A145839.
for(n=0, M, print1(a(n+1)-a(n), ", "));




