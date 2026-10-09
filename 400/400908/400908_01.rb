# A400908: min of gcd(C(n,i), C(n,j)) over 2 <= i <= j <= floor(n/2).
# Writes b400908.txt for n = 4..N (default N = 10000).
#
# Method
#   g(i,j) = prod_{p | C(n,i)} p^min(v_p(C(n,i)), v_p(C(n,j))),
#   with v_p(C(n,j)) = (s_p(j) + s_p(n-j) - s_p(n)) / (p-1)  (Legendre/Kummer).
# Pruning (B = current minimum)
#   C(n,i) | C(n,j)*C(j,i)  =>  g(i,j) >= C(n,i)/C(j,i).
#   * j-loop: skip j while C(n,i)/C(j,i) >= B.
#   * i-loop: stop once C(n,i)/C(m,i) >= B (this bound grows with i).
#   * product over primes stops as soon as it reaches B.

N = (ARGV[0] || 10000).to_i

# smallest prime factor sieve
SPF = Array.new(N + 1, 0)
(2..N).each do |k|
  next if SPF[k] != 0
  (k..N).step(k) { |t| SPF[t] = k if SPF[t] == 0 }
end

def add_factors(h, x, sgn)
  while x > 1
    p = SPF[x]
    while x % p == 0
      h[p] += sgn
      x /= p
    end
  end
end

def digit_sum(x, p)
  s = 0
  while x > 0
    s += x % p
    x /= p
  end
  s
end

def a(n)
  m = n / 2
  best = n * (n - 1) / 2          # pair (2,2)
  exps = Hash.new(0)
  add_factors(exps, n, 1)         # C(n,1) = n
  sn = {}                          # cache of s_p(n)
  (2..m).each do |i|
    add_factors(exps, n - i + 1, 1)
    add_factors(exps, i, -1)

    # i-loop bound: C(n,i)/C(m,i) = prod (n-t)/(m-t)
    lb = 0.0
    i.times { |t| lb += Math.log(n - t) - Math.log(m - t) }
    break if lb > Math.log(best) + 1e-9

    primes = exps.select { |_, e| e > 0 }.sort_by { |p, _| -p }
    primes.each { |p, _| sn[p] ||= digit_sum(n, p) }

    # j-loop start: skip j while C(n,i)/C(j,i) >= best
    j = i
    while j < m
      lj = 0.0
      i.times { |t| lj += Math.log(n - t) - Math.log(j - t) }
      break if lj <= Math.log(best) + 1e-9
      j += 1
    end

    while j <= m
      g = 1
      primes.each do |p, e|
        v = (digit_sum(j, p) + digit_sum(n - j, p) - sn[p]) / (p - 1)
        k = e < v ? e : v
        g *= p**k if k > 0
        break if g >= best
      end
      best = g if g < best
      j += 1
    end
  end
  best
end

File.open("b400908.txt", "w") do |f|
  (4..N).each do |n|
    f.puts "#{n} #{a(n)}"
    $stderr.print "\r#{n}" if n % 100 == 0
  end
end
$stderr.puts
