# Erdős Problem #933
# n(n+1) = 2^k 3^l m, gcd(m,6) = 1 と書いたときの a(n) = 2^k 3^l
# （n(n+1) の 3-smooth 部分 = A065331(n) * A065331(n+1)）
# n = 1..10000 について計算し b401022_01.txt に "n a(n)" 形式で保存

N = 10000

# x の 3-smooth 部分（x を割る最大の 2^i 3^j）
def smooth3(x)
  r = 1
  [2, 3].each do |p|
    while x % p == 0
      x /= p
      r *= p
    end
  end
  r
end

File.open('b401022_01.txt', 'w') do |f|
  (1..N).each { |n| f.puts "#{n} #{smooth3(n * (n + 1))}" }
end
