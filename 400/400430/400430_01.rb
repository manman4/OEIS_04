# Erdős Problem #413
# a(n) = max_{1 <= m < n} (m + omega(m)) - n,  omega(m) = m の相異なる素因数の個数
# n = 2..10000 について計算し b400430_01.txt に "n a(n)" 形式で保存
# （n = 1 は m が存在せず定義されないので n = 2 から。a(2) = -1, n >= 3 では a(n) >= 0）
# n が barrier（A005236）であることと a(n) <= 0 は同値。

N = 10000

# omega(m) をふるいで計算
omega = Array.new(N, 0)
(2...N).each do |p|
  next if omega[p] > 0            # p は素数
  (p...N).step(p) { |m| omega[m] += 1 }
end

File.open('b400430_01.txt', 'w') do |f|
  mx = nil                        # max_{1 <= m < n} (m + omega(m))
  (2..N).each do |n|
    m = n - 1
    v = m + omega[m]
    mx = v if mx.nil? || v > mx
    f.puts "#{n} #{mx - n}"
  end
end
