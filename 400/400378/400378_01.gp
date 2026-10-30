\\ Maximum number of consecutive integers in [n, 2*n] all satisfying omega(k) > log(log(k))
a(n) = my(r=0, m=0); for(k=n, 2*n, r=if(omega(k)>log(log(k)), r+1, 0); m=max(m, r)); m;
for(n=2, 101, print1(a(n), ", "));

