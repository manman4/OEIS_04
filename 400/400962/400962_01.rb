# Erdős Problem #379: S(n)
# S(n) = すべての 1 <= k < n に対し、ある素数 p (k に依存してよい) で
#        p^S(n) | C(n,k) となるような最大の整数
#      = min_{1<=k<n} max_p v_p(C(n,k))
# n = 2..10000 について計算し b400962_01.txt に "n S(n)" 形式で保存
# （n = 1 は k が存在せず定義されないので n = 2 から）
#
# v_p(C(n,k)) = (s_p(k) + s_p(n-k) - s_p(n)) / (p-1)  (Legendre / Kummer)
# k = 1 から S(n) <= max_p v_p(n)。また C(n,k) > 1 なので S(n) >= 1。
# v_p(C(n,k)) <= floor(log_p n) なので、v >= t を探すには p^t <= n の素数だけ見ればよい。

require 'prime'

N = 10000

def digit_sum(m, p)
  s = 0
  while m > 0
    s += m % p
    m /= p
  end
  s
end

def vp_binom(n, k, p)
  (digit_sum(k, p) + digit_sum(n - k, p) - digit_sum(n, p)) / (p - 1)
end

PRIMES = Prime.each(N).to_a

def big_s(n)
  best = n.prime_division.map(&:last).max # k = 1 での値（上界）
  return best if best <= 1
  (2..n / 2).each do |k|                  # C(n,k) = C(n,n-k)
    # この k で max_p v_p(C(n,k)) >= best かどうかを確かめつつ最大値を求める
    m = 0
    PRIMES.each do |p|
      break if p**(m + 1) > n             # これ以上 m を超える v_p は出ない
      v = vp_binom(n, k, p)
      m = v if v > m
      break if m >= best
    end
    m = 1 if m < 1                        # p > n/2 等でも C(n,k) > 1 なので最低 1
    best = m if m < best
    return best if best <= 1
  end
  best
end

File.open('b400962_01.txt', 'w') do |f|
  (2..N).each { |n| f.puts "#{n} #{big_s(n)}" }
end
