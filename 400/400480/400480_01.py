# a(0) = 1; a(2*n+1) = 3*a(n) + Sum_{i,j,k>=0 and i+j+k=n-1} a(i)*a(j)*a(k) and a(2*n+2) = 3*Sum_{k=0..n} a(k)*a(n-k) for n >= 0.
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
            list.append(3 * list[k] + s)
        else:
            k = (m - 2) // 2
            s = 0
            for i in range(k + 1):
                s += list[i] * list[k - i]
            list.append(3 * s)
    return list

print(a(30))

