# Erdős Problem #387
# a(n) = min_{1 <= k < n} ( C(n,k) の約数のうち n 以下で最大のもの )
# n = 2..10000 について計算し b401108_01.txt に "n a(n)" 形式で保存
# （n = 1 は k が存在せず定義されないので n = 2 から）
#
# 方針:
#   対称性 C(n,k) = C(n,n-k) より 1 <= k <= n/2 を調べればよい。
#   d | C(n,k) は d の各素因数 p^e について v_p(C(n,k)) >= e を確かめて判定する
#   （v_p(C(n,k)) = (s_p(k) + s_p(n-k) - s_p(n)) / (p-1)、Kummer / Legendre）。
#   P を n 以下の最大の素数とする。P > n/2 なので
#     P | C(n,k)  <=>  n - P < k < P
#   となり、k > n - P では最大の約数は P 以上。
#   (1) k <= n - P については、最大の約数を d = n から下に探して正確に求める。
#   (2) k > n - P については、その最小値が P より大きいときだけ
#       d ∈ (P, n] を上から調べる（見つからなければ値は P）。

N = 10000

SPF = Array.new(N + 1, 0)
(2..N).each do |i|
  next if SPF[i] != 0
  (i..N).step(i) { |j| SPF[j] = i if SPF[j] == 0 }
end
FACT = Array.new(N + 1) { [] }
(2..N).each do |i|
  m = i
  f = []
  while m > 1
    p = SPF[m]
    e = 0
    while m % p == 0
      m /= p
      e += 1
    end
    f << [p, e]
  end
  FACT[i] = f
end

def digit_sum(x, p)
  s = 0
  while x > 0
    s += x % p
    x /= p
  end
  s
end

# d | C(n,k) か（sn は s_p(n) のキャッシュ）
def divides?(d, n, k, sn)
  FACT[d].all? do |p, e|
    s = (sn[p] ||= digit_sum(n, p))
    digit_sum(k, p) + digit_sum(n - k, p) - s >= e * (p - 1)
  end
end

def a(n)
  return n if SPF[n] == n               # n が素数なら p | C(p,k) なので a(n) = n
  pr = n - 1
  pr -= 1 while SPF[pr] != pr           # n 以下の最大の素数 P
  sn = {}
  best = n
  # (1) k <= n - P : 最大の約数を正確に求める
  (1..[n - pr, n / 2].min).each do |k|
    d = n
    d -= 1 until d == 1 || divides?(d, n, k, sn)
    best = d if d < best
  end
  # (2) n - P < k <= n/2 : 最大の約数は P 以上
  if best > pr
    (n - pr + 1..n / 2).each do |k|
      d = n
      d -= 1 while d > pr && !divides?(d, n, k, sn)
      best = d if d < best              # d == pr なら P が最大の約数
      break if best == pr
    end
  end
  best
end

File.open('b401108_01.txt', 'w') do |f|
  (2..N).each { |n| f.puts "#{n} #{a(n)}" }
end
