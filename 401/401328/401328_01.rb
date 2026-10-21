# Erdős Problem #461
# Square array A(n,t), n >= 0, t >= 1, read by antidiagonals downwards:
#   A(n,t) = m = n+1, ..., n+t における s_t(m) の値の種類数,
#   s_t(m) = m を割る素数 p < t についての p^{v_p(m)} の積（m の t-smooth 部分）
# 読む順序: A(0,1); A(0,2), A(1,1); A(0,3), A(1,2), A(2,1); ...
#   （反対角線 d = n + t - 1 ごとに n を 0 から増やす）
# 反対角線 d = 0..N を b401328_01.txt に "i A" 形式（i は通し番号, OFFSET 0 に合わせて 0 から）で保存
# （N = 139 で 9870 項、N = 140 で 10011 項）

N = 139
M = N + 2                         # m <= n + t = d + 1 <= N + 1

SPF = Array.new(M + 1, 0)
(2..M).each do |i|
  next if SPF[i] != 0
  (i..M).step(i) { |j| SPF[j] = i if SPF[j] == 0 }
end

# m の t-smooth 部分（素数 p < t の部分）
def smooth(m, t)
  r = 1
  while m > 1
    p = SPF[m]
    while m % p == 0
      m /= p
      r *= p if p < t
    end
  end
  r
end

def a(n, t)
  (n + 1..n + t).map { |m| smooth(m, t) }.uniq.size
end

File.open('b401328_01.txt', 'w') do |f|
  idx = -1
  (0..N).each do |d|
    (0..d).each do |n|
      t = d - n + 1
      idx += 1
      f.puts "#{idx} #{a(n, t)}"
    end
  end
end
