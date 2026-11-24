# A402485: Number of partitions of n such that (greatest part)/(least part) > number of parts.
#
# Usage: ruby 402485_01.rb [N]        (default N = 10000, writes b402485.txt)
#        ruby 402485_01.rb --check [N] (compare with brute force and the original g.f., default N = 40)
#
# ---------------------------------------------------------------------------
# Fast formula (derived from the g.f. in OEIS)
#
#   G.f.: Sum_{i>=0,j>=1} x^((i+1)j) (1 - Prod_{k=1..i}(1 - x^(ij+k))) / (x;x)_i,
#   where (x;x)_i = Prod_{k=1..i}(1-x^k).  Write Q_i = 1/(x;x)_i,
#   R_m = Prod_{k>=m} 1/(1-x^k) (partitions with all parts >= m).
#
#   (1) q-binomial theorem: Prod_{k=1..i}(1 - z x^k) = Sum_s (-1)^s x^(s(s+1)/2) [i,s] z^s.
#       With z = x^(ij):  1 - Prod = Sum_{s>=1} (-1)^(s+1) x^(s*ij + s(s+1)/2) [i,s].
#   (2) Q_i [i,s] = Q_s Q_(i-s).
#   (3) Put t = i - s >= 0.  Exponent (i+1)j + s*ij = j(s^2+s+1) + j(s+1)t.
#   (4) Euler: Sum_{t>=0} Q_t y^t = Prod_{k>=0} 1/(1 - y x^k); with y = x^(j(s+1))
#       this is R_(j(s+1)).
#   Hence
#     A(x) = Sum_{s>=1} (-1)^(s+1) x^(s(s+1)/2) Q_s(x) Sum_{j>=1} x^(j(s^2+s+1)) R_(j(s+1))(x).
#
#   R_m is built for m = N, N-1, ..., 2 by R_m = R_(m+1)/(1-x^m) (one array, O(N) per step);
#   when m = j(s+1) the shifted R_m is added to V_s.  Finally V_s is divided by
#   (1-x^k), k=1..s, and added with sign (-1)^(s+1).  Total work O(N^2) big-integer additions.
# ---------------------------------------------------------------------------

def a402485_fast(nmax)
  # pairs[m] = list of [s, shift], shift = s(s+1)/2 + j(s^2+s+1), m = j(s+1)
  pairs = Hash.new { |h, k| h[k] = [] }
  smax = 0
  s = 1
  while s * (s + 1) / 2 + (s * s + s + 1) <= nmax
    smax = s
    j = 1
    loop do
      sh = s * (s + 1) / 2 + j * (s * s + s + 1)
      break if sh > nmax
      pairs[j * (s + 1)] << [s, sh]
      j += 1
    end
    s += 1
  end

  v = Array.new(smax + 1) { Array.new(nmax + 1, 0) }
  r = Array.new(nmax + 1, 0)
  r[0] = 1 # R_(nmax+1) = 1 mod x^(nmax+1)
  mmin = pairs.keys.min || (nmax + 1)
  nmax.downto(mmin) do |m|
    (m..nmax).each { |k| r[k] += r[k - m] } # divide by (1 - x^m)
    next unless pairs.key?(m)
    pairs[m].each do |s2, sh|
      vs = v[s2]
      (0..nmax - sh).each { |k| vs[k + sh] += r[k] }
    end
  end

  a = Array.new(nmax + 1, 0)
  (1..smax).each do |s2|
    vs = v[s2]
    (1..s2).each do |k|
      (k..nmax).each { |n| vs[n] += vs[n - k] } # divide by (1 - x^k)
    end
    if s2.odd?
      (0..nmax).each { |n| a[n] += vs[n] }
    else
      (0..nmax).each { |n| a[n] -= vs[n] }
    end
  end
  a
end

# Original g.f., literally (slow; for checking only).
def a402485_gf(nmax)
  a = Array.new(nmax + 1, 0)
  (1..nmax).each do |i| # i = 0 gives 0
    j = 1
    while (i + 1) * j <= nmax
      sh = (i + 1) * j
      len = nmax - sh
      prod = Array.new(len + 1, 0); prod[0] = 1
      (1..i).each do |k|
        d = i * j + k
        break if d > len
        len.downto(d) { |n| prod[n] -= prod[n - d] }
      end
      f = Array.new(len + 1) { |n| (n == 0 ? 1 : 0) - prod[n] }
      (1..[i, len].min).each { |k| (k..len).each { |n| f[n] += f[n - k] } }
      (0..len).each { |n| a[n + sh] += f[n] }
      j += 1
    end
  end
  a
end

# Definition, by enumerating partitions (for checking only).
def a402485_brute(nmax)
  a = Array.new(nmax + 1, 0)
  gen = lambda do |rest, maxp, parts, &blk|
    if rest == 0
      blk.call(parts)
      return
    end
    [rest, maxp].min.downto(1) do |p|
      parts << p
      gen.call(rest - p, p, parts, &blk)
      parts.pop
    end
  end
  (1..nmax).each do |n|
    cnt = 0
    gen.call(n, n, []) { |pt| cnt += 1 if pt.first > pt.last * pt.size }
    a[n] = cnt
  end
  a
end

DATA_OEIS = [0, 0, 0, 1, 1, 2, 4, 6, 8, 12, 17, 24, 33, 44, 58, 79, 102, 133, 173, 222,
             283, 363, 458, 577, 723, 903, 1123, 1395, 1722, 2121, 2605, 3192, 3892, 4742,
             5753, 6971, 8421, 10153, 12208, 14660, 17555, 20990, 25043, 29828, 35451,
             42080, 49846, 58964, 69627, 82104].freeze

def parse_n(str, default)
  return default if str.nil?
  abort "N must be a positive integer: #{str}" unless str.match?(/\A[1-9][0-9]*\z/)
  str.to_i
end

if ARGV[0] == '--help' || ARGV[0] == '-h'
  puts 'Usage: ruby 402485_01.rb [N]  |  ruby 402485_01.rb --check [N]'
  exit
end

if ARGV[0] == '--check'
  n = parse_n(ARGV[1], 40)
  f = a402485_fast(n)
  g = a402485_gf(n)
  b = a402485_brute(n)
  ok = (1..n).all? { |k| f[k] == g[k] && f[k] == b[k] }
  m = [n, DATA_OEIS.size].min
  ok_data = (1..m).all? { |k| f[k] == DATA_OEIS[k - 1] }
  puts "fast == g.f. == brute for n=1..#{n}: #{ok}"
  puts "fast == OEIS DATA for n=1..#{m}: #{ok_data}"
  exit(ok && ok_data ? 0 : 1)
end

nmax = parse_n(ARGV[0], 10_000)
a = a402485_fast(nmax)
out = 'b402485.txt'
tmp = "#{out}.tmp#{Process.pid}"
File.open(tmp, 'w') do |fh|
  (1..nmax).each { |n| fh.puts "#{n} #{a[n]}" }
  fh.flush
  fh.fsync
end
File.rename(tmp, out)
puts "wrote #{out} (n=1..#{nmax})"
