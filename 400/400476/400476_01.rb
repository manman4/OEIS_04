# a(0) = 1; 
# a(2*n+1) = 3*a(n) + Sum_{i,j,k>=0 and i+j+k=n-1} a(i)*a(j)*a(k) and 
# a(2*n+2) = 3*Sum_{k=0..n} a(k)*a(n-k) for n >= 0,

def A(n)
  ary = [1]
  (1..n).each{|i|
    if i.odd?
      m = (i-1)/2
      sum = 0
      (0..m - 1).each{|x|
        (0..m - 1 - x).each{|y|
          z = m - 1 - x - y
          sum += ary[x]*ary[y]*ary[z]
        }
      }
      ary << 3*ary[m] + sum
    else
      m = (i-2)/2
      sum = 0
      (0..m).each{|k|
        sum += ary[k]*ary[m-k]
      }
      ary << 3*sum
    end
  }
  ary
end

n = 10000
ary = A(n)
(0..n).each{|i| 
  j = ary[i]
  break if j.to_s.size > 1000
  print i
  print " "
  puts j
}
