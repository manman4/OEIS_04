\\ a(n) = n - min_{k > n, k composite} (k - spf(k)), where spf(k) is the smallest prime factor of k.
a(n) = if(n<2, n-2, my(r=n); forcomposite(k=n+1, 2*n, r=min(r, k-factor(k)[1, 1])); n-r);
for(n=0, 101, print1(a(n), ", "));

