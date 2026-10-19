# Erdős Problem #824
# a(n) = #{ (a,b) : 1 <= a < b <= n, gcd(a,b) = 1, sigma(a) = sigma(b) }
# （問題の h(x) は b < x なので h(x) = a(x-1)）
# n = 1..10000 について計算し b401252_01.txt に "n a(n)" 形式で保存

N = 10000

# sigma(m) をふるいで計算
sig = Array.new(N + 1, 0)
(1..N).each { |d| (d..N).step(d) { |m| sig[m] += d } }

groups = Hash.new { |h, k| h[k] = [] }   # sigma の値 -> それまでに現れた数
File.open('b401252_01.txt', 'w') do |f|
  total = 0
  (1..N).each do |b|
    # b を大きいほうとする組 (a, b) の数を足す
    total += groups[sig[b]].count { |a| a.gcd(b) == 1 }
    groups[sig[b]] << b
    f.puts "#{b} #{total}"
  end
end
