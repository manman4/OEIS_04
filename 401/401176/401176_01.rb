# Erdős Problem #463
# a(n) = n - min_{k > n, k composite} (k - spf(k)),  spf(k) = k の最小素因数
# n = 0..10000 について計算し b401176_01.txt に "n a(n)" 形式で保存
#
# 探索の打ち切り:
#   合成数 k では spf(k) <= floor(sqrt(k)) なので k - spf(k) >= k - floor(sqrt(k))。
#   k - floor(sqrt(k)) は k について単調非減少なので、これが現在の最小値を超えたら打ち切れる。
#   また n >= 2 では min <= n（n+1 が合成数なら k = n+1、そうでなければ k = n+2 は偶数）なので
#   調べる k は n + sqrt(n) + 1 程度まで。

N = 10000
M = N + 200

SPF = Array.new(M + 1, 0)
(2..M).each do |i|
  next if SPF[i] != 0
  (i..M).step(i) { |j| SPF[j] = i if SPF[j] == 0 }
end

def a(n)
  # n = 0, 1 も定義どおり計算できる（最小値は k = 4 の 4 - 2 = 2 で a(0) = -2, a(1) = -1）
  best = nil
  k = n + 1
  while best.nil? || k - Integer.sqrt(k) <= best
    p = SPF[k]
    if p != 0 && p != k           # k は合成数（k = 1 は SPF[1] = 0 で除外）
      v = k - p
      best = v if best.nil? || v < best
    end
    k += 1
  end
  n - best
end

File.open('b401176_01.txt', 'w') do |f|
  (0..N).each { |n| f.puts "#{n} #{a(n)}" }
end
