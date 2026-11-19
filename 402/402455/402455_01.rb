# a(n) = 1 + Sum_{k=1..n} k^n * a(n-k).
def A(n)
  ary = [1]
  (1..n).each{|i|
    s = 1
    (1..i).each{|k|
      s += k**i * ary[i-k]
    }
    ary << s
  }
  ary
end

n = 200
ary = A(n)
(0...ary.size).each{|i|
  j = ary[i]
  break if j.to_s.size > 1000
  print i
  print ' '
  puts j
}
