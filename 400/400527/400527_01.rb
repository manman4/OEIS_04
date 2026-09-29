def f(n)
  return 1 if n < 2
  (1..n).inject(:*)
end

# a(0) = 1; a(n) = (n-1)! * Sum_{j=0..floor((n-1)/2)} (2*j+1) * a(n-1-2*j)/(n-1-2*j)! * Sum_{k=0..j} a(k)*a(j-k)/(k!*(j-k)!).
def A(n)
  ary = [1]
  (1..n).each{|i| ary << (f(i-1) * (0..((i-1)/2)).inject(0){|s, j| s + (2*j+1) * ary[i-1-2*j] / f(i-1-2*j).to_r * (0..j).inject(0){|t, k| t + ary[k] * ary[j-k] / (f(k) * f(j-k)).to_r}})}
  ary
end

n = 100
ary = A(n)
(0..n).each{|i| 
  j = ary[i]
  break if j.denominator != 1
  j = j.to_i
  break if j.to_s.size > 1000
  print i
  print " "
  puts j
}
