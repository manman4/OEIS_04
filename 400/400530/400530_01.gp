\\ a(0) = 1; a(n) = 2 * (n-1)! * Sum_{k=0..floor((n-1)/3)} (3*k+1) * a(k) * a(n-1-3*k)/(k! * (n-1-3*k)!).
a_vector(n) = my(v=vector(n+1)); v[1]=1; for(i=1, n, v[i+1]=2*(i-1)!*sum(j=0, (i-1)\3, (3*j+1)*v[j+1]*v[i-3*j]/(j!*(i-1-3*j)!))); v;
a_vector(30)

