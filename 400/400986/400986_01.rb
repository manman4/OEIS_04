# A400986 (cf. Erdős Problem #647)
# a(n) = max_{1 <= k < n} (k + tau(k)) - n,  tau(k) = 約数の個数
# n = 2..10000 について計算し b400986_01.txt に "n a(n)" 形式で保存
# （n = 1 は k が存在せず定義されないので n = 2 から）

N = 10000

# tau(k) をふるいで計算
tau = Array.new(N, 0)
(1...N).each { |d| (d...N).step(d) { |m| tau[m] += 1 } }

File.open('b400986_01.txt', 'w') do |f|
  mx = -1                         # max_{1 <= k < n} (k + tau(k))
  (2..N).each do |n|
    k = n - 1
    v = k + tau[k]
    mx = v if v > mx
    f.puts "#{n} #{mx - n}"
  end
end
