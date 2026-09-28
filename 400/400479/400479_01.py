# a(0) = 1; a(3*n+1) = 3*a(n), a(3*n+2) = 3*Sum_{k=0..n} a(k)*a(n-k) and a(3*n+3) = Sum_{i,j,k>=0 and i+j+k=n} a(i)*a(j)*a(k) for n >= 0.
def a(n):
    list = [1]
    while len(list) <= n:
        m = len(list)
        if m % 3 == 1:
            n_ = (m - 1) // 3
            list.append(3 * list[n_])
        elif m % 3 == 2:
            n_ = (m - 2) // 3
            s = 0
            for k in range(n_ + 1):
                s += list[k] * list[n_ - k]
            list.append(3 * s)
        else:
            n_ = (m - 3) // 3
            s = 0
            for i in range(n_ + 1):
                for j in range(n_ + 1):
                    for k in range(n_ + 1):
                        if i + j + k == n_:
                            s += list[i] * list[j] * list[k]
            list.append(s)
    return list

print(a(50))

