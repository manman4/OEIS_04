# a(0) = 1;
# a(n) = n! * Sum_{j=0..floor((n-1)/2)} (n-j)^j *
#        Sum_{k=j+1..n-j} binomial(n-j-1,k-1) * Stirling1(k-1,j)/k!
# Stirling1 は符号付き

# 符号付き第1種スターリング数の表 s[i][j] (0 <= i, j <= m)
def stirling1_table(m)
  s = Array.new(m + 1) { Array.new(m + 1, 0) }
  s[0][0] = 1
  (1..m).each do |i|
    (1..i).each do |j|
      s[i][j] = s[i - 1][j - 1] - (i - 1) * s[i - 1][j]
    end
  end
  s
end

def binomial(n, k)
  return 0 if k < 0 || k > n
  k = n - k if k > n - k
  r = 1
  (1..k).each { |i| r = r * (n - k + i) / i }
  r
end

def factorial_table(m)
  f = [1]
  (1..m).each { |i| f << f[-1] * i }
  f
end

def a(n, s, f)
  return 1 if n == 0
  sum = 0r
  (0..(n - 1) / 2).each do |j|
    inner = 0r
    (j + 1..n - j).each do |k|
      inner += Rational(binomial(n - j - 1, k - 1) * s[k - 1][j], f[k])
    end
    sum += (n - j)**j * inner
  end
  r = f[n] * sum
  raise "not integer: #{r}" unless r.denominator == 1
  r.to_i
end

def seq(max)
  s = stirling1_table(max)
  f = factorial_table(max)
  (0..max).map{|n| a(n, s, f)}
end

n = 20
ary = seq(n)
(0..n).each{|i|
  j = ary[i]
  break if j.to_s.size > 1000
  print i
  print " "
  puts j
}
