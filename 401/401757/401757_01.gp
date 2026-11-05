\\ Least positive integer k such that j is squarefree if and only if j+k is squarefree for every j from 1 to n.
a(n) = my(k=0); until(sum(j=1, n, issquarefree(j)!=issquarefree(j+k))==0, k++); k;
for(n=1, 54, print1(a(n),", "));

