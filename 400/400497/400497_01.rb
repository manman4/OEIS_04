# a(0) = 1; a(n) = (1/n) * Sum_{k=0..floor((n-1)/4)} (n+4*k+1)*a(k)*a(n-1-4*k).
def A(n)
  ary = [1]
  (1..n).each{|i| ary << (0..(i-1)/4).inject(0){|s, j| s + (i + 4*j + 1) * ary[j] * ary[i-1-4*j]} / i}
  ary
end

n = 1000
ary = A(n)
(0..n).each{|i| 
  j = ary[i]
  break if j.to_s.size > 1000
  print i
  print " "
  puts j
}
