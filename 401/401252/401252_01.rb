# Erdős Problem #824
# a(n) = h(n) = #{ (a,b) : 1 <= a < b < n, gcd(a,b) = 1, sigma(a) = sigma(b) }
# n = 1..10000 について計算し b401252_01.txt に "n a(n)" 形式で保存

N = 10000

# sigma(m) をふるいで計算（b < n <= N なので N-1 まで使う）
sig = Array.new(N + 1, 0)
(1..N).each { |d| (d..N).step(d) { |m| sig[m] += d } }

groups = Hash.new { |h, k| h[k] = [] }   # sigma の値 -> それまでに現れた数
File.open('b401252_01.txt', 'w') do |f|
  total = 0                               # b < n を満たす組の個数
  (1..N).each do |n|
    f.puts "#{n} #{total}"
    # 次の n のために b = n を大きいほうとする組を足す
    b = n
    total += groups[sig[b]].count { |a| a.gcd(b) == 1 }
    groups[sig[b]] << b
  end
end
