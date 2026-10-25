a(n) = {
  my(b=vector(primepi(n)), r=0, f, v, h);
  for(m=1, n,
    f=factor(m);
    v=sum(j=1, matsize(f)[1], (f[j,2]%2)*2^(primepi(f[j,1])-1));
    while(v,
      h=logint(v, 2)+1;
      if(b[h], v=bitxor(v, b[h]), b[h]=v; break)
    );
    if(!v, r++; b=vector(#b))
  );
  r
};

for(n=1, 100, print1(a(n),", "));
