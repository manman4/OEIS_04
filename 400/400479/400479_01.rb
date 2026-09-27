# a(0) = 1; 
# a(3*n+1) = 3*a(n), 
# a(3*n+2) = 3*Sum_{k=0..n} a(k)*a(n-k) and
# a(3*n+3) = Sum_{i,j,k>=0 and i+j+k=n} a(i)*a(j)*a(k) for n >= 0.

def A(n)
  ary = [1]
  (1..n).each{|i|
    if i % 3 == 1
      m = (i-1)/3
      ary << 3*ary[m]
    elsif i % 3 == 2
      m = (i-2)/3
      sum = 0
      (0..m).each{|j|
        sum += ary[j]*ary[m-j]
      }
      ary << 3*sum
    elsif i % 3 == 0
      m = (i-3)/3
      sum = 0
      (0..m).each{|x|
        (0..m - x).each{|y|
          z = m - x - y
          sum += ary[x]*ary[y]*ary[z]
        }
      }
      ary << sum
    end
  }
  ary
end

n = 100
p ary = A(n)
# (0..n).each{|i| 
#   j = ary[i]
#   break if j.to_s.size > 1000
#   print i
#   print " "
#   puts j
# }
