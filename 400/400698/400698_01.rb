# A400698: a(n) = Sum_{k=0..n} mu(k^2 + 1).
# n = 0..10000 を計算し、b400698_01.txt に "n a(n)" 形式で保存する。
#
# アルゴリズム (多項式値の篩):
#   v[k] = k^2 + 1 (k = 0..N) を用意し、素因数で割っていく。
#   k^2 + 1 を割る素数は 2 か p ≡ 1 (mod 4) のみ。
#     p = 2   : k が奇数のとき k^2+1 ≡ 2 (mod 4) なので 2 がちょうど 1 回割る。
#     p ≡ 1 (mod 4) : x^2 ≡ -1 (mod p) の解 ±r に対し k ≡ ±r (mod p) の k だけを調べる。
#   p <= N の素数で篩えば、残った cofactor が 1 より大きければそれは N より大きい素数 1 個。
#   (N より大きい素数 2 個の積は (N+1)^2 > N^2+1 >= v[k] となり不可能)
#   素因数の個数 (重複があれば mu = 0) から mu を決め、累積和をとる。

N = 10000

# エラトステネスの篩
is_prime = Array.new(N + 1, true)
is_prime[0] = is_prime[1] = false
(2..Integer.sqrt(N)).each do |i|
  next unless is_prime[i]
  (i * i).step(N, i) { |j| is_prime[j] = false }
end

v   = Array.new(N + 1) { |k| k * k + 1 }
cnt = Array.new(N + 1, 0)      # 異なる素因数の個数
zero = Array.new(N + 1, false) # 平方因子を持つ

# p = 2
1.step(N, 2) do |k|
  v[k] /= 2
  cnt[k] += 1
end

# x^2 ≡ -1 (mod p) の解を求める (平方非剰余 c に対し c^((p-1)/4))
def sqrt_minus_one(p)
  c = 2
  c += 1 while c.pow((p - 1) / 2, p) != p - 1
  c.pow((p - 1) / 4, p)
end

(5..N).each do |p|
  next unless is_prime[p] && p % 4 == 1
  r = sqrt_minus_one(p)
  [r, p - r].each do |s|
    s.step(N, p) do |k|
      next if zero[k]
      v[k] /= p
      cnt[k] += 1
      zero[k] = true if v[k] % p == 0
    end
  end
end

File.open('b400698_01.txt', 'w') do |f|
  sum = 0
  (0..N).each do |n|
    unless zero[n]
      c = cnt[n] + (v[n] > 1 ? 1 : 0)
      sum += c.even? ? 1 : -1
    end
    f.puts "#{n} #{sum}"
  end
end
