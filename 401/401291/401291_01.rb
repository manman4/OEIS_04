# A401291: Maximum possible smallest part in a partition of n into
# 3-smooth numbers, no part dividing another.
#
# Two parts 2^a*3^b and 2^c*3^d (distinct) do not divide each other
# iff (a - c) and (b - d) have opposite signs. So if the parts are
# listed with a strictly decreasing, b must be strictly increasing.
#
# best(rem, amax, bmin) = max over such partitions of rem whose parts
# 2^a*3^b all satisfy a < amax and b > bmin, of the smallest part
# (INF if rem == 0, 0 if no partition exists).

N = 10000
INF = N + 1

AMAX = (0..).find { |a| 2**a > N }   # a ranges over 0...AMAX
BMAX = (0..).find { |b| 3**b > N }   # b ranges over 0...BMAX

POW2 = (0...AMAX).map { |a| 2**a }
POW3 = (0...BMAX).map { |b| 3**b }

# memo index: rem, amax in 0..AMAX, bmin in -1..BMAX-1
@memo = Array.new((N + 1) * (AMAX + 1) * (BMAX + 1))

def best(rem, amax, bmin)
  return INF if rem == 0
  key = (rem * (AMAX + 1) + amax) * (BMAX + 1) + (bmin + 1)
  v = @memo[key]
  return v if v

  res = 0
  (0...amax).each do |a|
    p2 = POW2[a]
    break if p2 > rem
    ((bmin + 1)...BMAX).each do |b|
      part = p2 * POW3[b]
      break if part > rem
      next if part <= res
      sub = best(rem - part, a, b)
      next if sub == 0
      m = part < sub ? part : sub
      res = m if m > res
    end
  end
  @memo[key] = res
end

File.open('b401291_01.txt', 'w') do |f|
  (1..N).each do |n|
    f.puts "#{n} #{best(n, AMAX, -1)}"
  end
end
