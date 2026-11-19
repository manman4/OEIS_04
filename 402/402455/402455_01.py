# a(n) = 1 + Sum_{k=1..n} k^n * a(n-k).
def A(n):
    ary = [1]
    for n_ in range(1, n + 1):
        s = 1
        for k in range(1, n_ + 1):
            s += k**n_ * ary[n_ - k]
        ary.append(s)
    return ary

n = 200
ary = A(n)
for i, j in enumerate(ary):
    if len(str(j)) > 1000:
        break
    print(i, j) 
    
