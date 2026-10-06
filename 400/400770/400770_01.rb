# A400770: a(n) = Sum_{k=0..n} mu(k^2 + k + 1).
# n = 0..10000 を計算し、b400770_01.txt に "n a(n)" 形式で保存する。
#
# アルゴリズム (多項式値の篩):
#   v[k] = k^2 + k + 1 (k = 0..N) を用意し、素因数で割っていく。
#   4(k^2+k+1) = (2k+1)^2 + 3 なので、k^2+k+1 を割る素数は 3 か p ≡ 1 (mod 3) のみ。
#     p = 3 : k ≡ 1 (mod 3) のとき 3 がちょうど 1 回割る (9 は決して割らない)。
#     p ≡ 1 (mod 3) : x^2+x+1 ≡ 0 (mod p) の解は 1 の原始 3 乗根 r, r^2 (= p-1-r)。
#                     k ≡ r, p-1-r (mod p) の k だけを調べる。
#   p <= N の素数で篩えば、残った cofactor が 1 より大きければそれは N より大きい素数 1 個。
#   (N より大きい素数 2 個の積は (N+1)^2 > N^2+N+1 >= v[k] となり不可能)
#   素因数の個数 (重複があれば mu = 0) から mu を決め、累積和をとる。

N = 10000

# エラトステネスの篩
is_prime = Array.new(N + 1, true)
is_prime[0] = is_prime[1] = false
(2..Integer.sqrt(N)).each do |i|
  next unless is_prime[i]
  (i * i).step(N, i) { |j| is_prime[j] = false }
end

v    = Array.new(N + 1) { |k| k * k + k + 1 }
cnt  = Array.new(N + 1, 0)     # 異なる素因数の個数
zero = Array.new(N + 1, false) # 平方因子を持つ

# p = 3
1.step(N, 3) do |k|
  v[k] /= 3
  cnt[k] += 1
end

# 1 の原始 3 乗根 mod p (p ≡ 1 mod 3): c^((p-1)/3) != 1 となる c を探す
def cube_root_of_unity(p)
  c = 2
  c += 1 while c.pow((p - 1) / 3, p) == 1
  c.pow((p - 1) / 3, p)
end

(7..N).each do |p|
  next unless is_prime[p] && p % 3 == 1
  r = cube_root_of_unity(p)
  [r, p - 1 - r].each do |s|
    s.step(N, p) do |k|
      next if zero[k]
      v[k] /= p
      cnt[k] += 1
      zero[k] = true if v[k] % p == 0
    end
  end
end

File.open('b400770_01.txt', 'w') do |f|
  sum = 0
  (0..N).each do |n|
    unless zero[n]
      c = cnt[n] + (v[n] > 1 ? 1 : 0)
      sum += c.even? ? 1 : -1
    end
    f.puts "#{n} #{sum}"
  end
end
