\\ Triangle read by rows: T(n,k) is the number of common elements of {j*(n-j): 1 <= j <= floor(n/2)} and {j*(k-j): 1 <= j <= floor(k/2)}, for n >= 2 and 1 <= k < n.
S(n) = Set(vector(n\2, j, j*(n-j)));
T(n, k) = #setintersect(S(n), S(k));
\\ for(n=2, 14, for(k=1, n-1, print1(T(n, k), ", ")));
cnt=2;
\\ n=141までをb401140_02.txtに保存する
for(n=2, 141, for(k=1, n-1, write("b401140_02.txt", cnt, " ", T(n, k)); cnt++));

