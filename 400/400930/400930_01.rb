# Erdős Problem #696: h(n)
# h(n) = 素因数 p_1 < ... < p_l (すべて n を割る) で
#        p_{i+1} ≡ 1 (mod p_i) を満たす列の最大長 l
# n = 1..10000 について計算し b400930_01.txt に "n h(n)" 形式で保存

require 'prime'

N = 10000

def h(n)
  primes = n.prime_division.map(&:first) # 昇順
  len = {}
  best = 0
  primes.each do |p|
    l = 1
    primes.each do |q|
      break if q >= p
      l = len[q] + 1 if (p - 1) % q == 0 && len[q] + 1 > l
    end
    len[p] = l
    best = l if l > best
  end
  best
end

File.open('b400930_01.txt', 'w') do |f|
  (1..N).each { |n| f.puts "#{n} #{h(n)}" }
end
