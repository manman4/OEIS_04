# Erdős Problem #889: v_1(n)
# v(n,k) = n+k の素因数 p（相異なる）のうち、n+i (0 <= i < k) のどれも割らないものの個数
#        = n+k の相異なる素因数のうち p > k であるものの個数
# v_1(n) = max_{k >= 1} v(n,k)
# n = 1..10000 について計算し b401014_01.txt に "n v_1(n)" 形式で保存
#
# k の範囲の打ち切り:
#   v(n,k) >= 2 なら k より大きい素数 2 個の積が n+k を割るので (k+1)^2 <= n+k。
#   よって 2 以上の値は (k+1)^2 <= n+k を満たす k だけ調べればよい。
#   一方 v(n,k) = 1 は k >= 1 でも常に実現できる（p > n なる素数 p に対し k = p - n >= 1 とすれば p > k）。
#   したがって v_1(n) = max(1, max_{k >= 1, (k+1)^2 <= n+k} v(n,k))。

N = 10000
K = 200                           # (k+1)^2 <= n+k を満たす k の上限より十分大きい
M = N + K

SPF = Array.new(M + 1, 0)
(2..M).each do |i|
  next if SPF[i] != 0
  (i..M).step(i) { |j| SPF[j] = i if SPF[j] == 0 }
end

# m の相異なる素因数のうち k より大きいものの個数
def count_big(m, k)
  c = 0
  while m > 1
    p = SPF[m]
    c += 1 if p > k
    m /= p while m % p == 0
  end
  c
end

def v1(n)
  best = 1
  k = 1
  while (k + 1)**2 <= n + k
    v = count_big(n + k, k)
    best = v if v > best
    k += 1
  end
  best
end

File.open('b401014_01.txt', 'w') do |f|
  (1..N).each { |n| f.puts "#{n} #{v1(n)}" }
end
