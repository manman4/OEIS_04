# a(0) = 1; a(2*n+1) = 4*a(n) + 4*Sum_{i,j,k>=0 and i+j+k=n-1} a(i)*a(j)*a(k) and a(2*n+2) = 6*Sum_{k=0..n} a(k)*a(n-k) + Sum_{i,j,k,l>=0 and i+j+k+l=n-1} a(i)*a(j)*a(k)*a(l) for n >= 0.
def a(n):
    list = [1]
    while len(list) <= n:
        m = len(list)
        if m % 2 == 1:
            k = (m - 1) // 2
            s = 0
            for i in range(k):
                for j in range(k):
                    for l in range(k):
                        if i + j + l == k - 1:
                            s += list[i] * list[j] * list[l]
            list.append(4 * list[k] + 4 * s)
        else:
            k = (m - 2) // 2
            s1 = 0
            for i in range(k + 1):
                s1 += list[i] * list[k - i]
            s2 = 0
            for i in range(k):
                for j in range(k):
                    for l in range(k):
                        for p in range(k):
                            if i + j + l + p == k - 1:
                                s2 += list[i] * list[j] * list[l] * list[p]
            list.append(6 * s1 + s2)
    return list

print(a(50))

