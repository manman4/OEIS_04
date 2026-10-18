# Erdős Problem #1184
# Square array read by ascending antidiagonals:
#   T(n,k) = #{ i : 1 <= i <= k, P(n+i) > k },  P(m) = m の最大素因数 (P(1) = 1),
#   n >= 1, k >= 1
# 読む順序: T(1,1); T(1,2), T(2,1); T(1,3), T(2,2), T(3,1); ...
#   （反対角線 n + k = s ごとに n を 1 から増やす）
# 反対角線 N 本ぶんを b401209_01.txt に "i T" 形式（i は通し番号, OFFSET 1 に合わせて 1 から）で保存
# （N = 140 で 9870 項、N = 141 で 10011 項）

N = 140
M = 2 * N + 2                     # n + i <= n + k = s <= N + 1 なので十分

# 最大素因数 P(m)
GPF = Array.new(M + 1, 1)
(2..M).each do |p|
  next if GPF[p] != 1             # p は素数（まだ更新されていない）
  (p..M).step(p) { |j| GPF[j] = p }
end

def t(n, k)
  (1..k).count { |i| GPF[n + i] > k }
end

File.open('b401209_01.txt', 'w') do |f|
  idx = 0
  (2..N + 1).each do |s|          # s = n + k
    (1...s).each do |n|
      k = s - n
      idx += 1
      f.puts "#{idx} #{t(n, k)}"
    end
  end
end
