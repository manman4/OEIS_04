# a(0) = 1; 
# a(2*n+1) = 4*a(n) + 4*Sum_{i,j,k>=0 and i+j+k=n-1} a(i)*a(j)*a(k) and 
# a(2*n+2) = 6*Sum_{j=0..n} a(j)*a(n-j) + Sum_{i,j,k,l>=0 and i+j+k+l=n-1} a(i)*a(j)*a(k)*a(l) for n >= 0.

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
      ary << 4*ary[m] + 4*sum
    else
      m = (i-2)/2
      sum = 0
      (0..m).each{|j|
        sum += ary[j]*ary[m-j]
      }
      quad_sum = 0
      (0..m - 1).each{|x|
        (0..m - 1 - x).each{|y|
          (0..m - 1 - x - y).each{|z|
            w = m - 1 - x - y - z
            quad_sum += ary[x]*ary[y]*ary[z]*ary[w]
          }
        }
      }
      ary << 6*sum + quad_sum
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
