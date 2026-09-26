# a(0) = 1, a(1) = 3; a(n) = (1/27) * (3^(n+2)*a(n-1) - Sum_{1<=i,j,k<=n-1 and i+j+k=n+2} a(i) * a(j) * a(k)).
def A(n)
  ary = [1, 3]
  (2..n).each{|i|
    s = (3 ** (i + 2)) * ary[i - 1]
    (1..i - 1).each{|j|
      (1..i - 1).each{|k|
        l = i + 2 - j - k
        if l >= 1 && l <= i - 1
          s -= ary[j] * ary[k] * ary[l]
        end
      }
    }
    ary << s / 27.to_r
  }
  ary
end

n = 100
ary = A(n)
(0..n).each{|i| 
  break if ary[i].denominator != 1
  j = ary[i].numerator
  break if j.to_s.size > 1000
  print i
  print ' '
  puts j
}