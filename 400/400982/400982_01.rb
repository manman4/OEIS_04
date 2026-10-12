# Erdős Problem #400 (k = 3): a(n) = Sum_{m=0..n} g_3(m)
# g_3(n) = max{ a + b + c - n : a, b, c >= 0 整数, a! b! c! | n! }
# n = 0..10000 について部分和を計算し b400982_01.txt に "n a(n)" 形式で保存
#
# 方針:
#   対称性から c <= b <= a としてよい。n >= 1 では a <= n。
#   a = n - d, b + c = m = d + g (g = a+b+c-n) とおくと
#     n!/a!   = d! * C(n,d)
#     b! c!   = m! / C(m,b)
#   より
#     a! b! c! | n!  <=>  m! | d! C(n,d) C(m,b)
#                    <=>  (d+1)(d+2)...(d+g) | C(n,d) * C(m,b)
#   各 d について、目標 g = best+1 で
#     R = (d+1)...(d+g) / gcd(・, C(n,d))  （素因数指数で保持）
#   を求め、R | C(m,b) となる b ∈ [ceil(m/2), min(m, n-d)] があれば best を更新する。
#   v_p(C(x,y)) は Kummer / Legendre: (s_p(y) + s_p(x-y) - s_p(x)) / (p-1)。
#   v_p(C(m,b)) <= log_p(m) なので p^e > m なら不可能（即座に棄却）。
#   a = n, b = c = 1 により n >= 1 で g_3(n) >= 2。
#   n = 0 は 0! = 1! より a = b = c = 1 が可能で g_3(0) = 3。

N = 10000
M = N + 64

# 最小素因数ふるいと素因数分解
SPF = Array.new(M + 1, 0)
(2..M).each do |i|
  next if SPF[i] != 0
  (i..M).step(i) { |j| SPF[j] = i if SPF[j] == 0 }
end
FACT = Array.new(M + 1) { [] }
(2..M).each do |i|
  m = i
  f = []
  while m > 1
    p = SPF[m]
    e = 0
    while m % p == 0
      m /= p
      e += 1
    end
    f << [p, e]
  end
  FACT[i] = f
end

def digit_sum(x, p)
  s = 0
  while x > 0
    s += x % p
    x /= p
  end
  s
end

# v_p(C(x, y))
def vp_binom(x, y, p)
  (digit_sum(y, p) + digit_sum(x - y, p) - digit_sum(x, p)) / (p - 1)
end

def g3(n)
  return 3 if n == 0
  best = 2
  d = 1
  while true
    g = best + 1
    m = d + g
    bmin = (m + 1) / 2
    bmax = [m, n - d].min
    break if bmin > bmax          # d を増やすと bmin 増・bmax 減なので以降も不可能

    # R = (d+1)...(m) を C(n,d) で割った残りの素因数指数
    need = Hash.new(0)
    (d + 1..m).each { |t| FACT[t].each { |p, e| need[p] += e } }
    r = []
    possible = true
    need.each do |p, e|
      e -= vp_binom(n, d, p)
      next if e <= 0
      if p**e > m                 # C(m,b) は p^e で割れない
        possible = false
        break
      end
      r << [p, e, digit_sum(m, p)]
    end

    found = false
    if possible
      r.sort_by! { |p, e, _| -(p**e) } # 制約の強い（p^e が大きい）ものから調べる
      (bmin..bmax).each do |b|
        # v_p(C(m,b)) >= e  <=>  s_p(b) + s_p(m-b) - s_p(m) >= e(p-1)
        if r.all? { |p, e, sm| (digit_sum(b, p) + digit_sum(m - b, p) - sm) >= e * (p - 1) }
          found = true
          break
        end
      end
    end

    if found
      best = g                    # 同じ d でさらに g を伸ばせるか再試行
    else
      d += 1
    end
  end
  best
end

File.open('b400982_01.txt', 'w') do |f|
  s = 0
  (0..N).each do |n|
    s += g3(n)
    f.puts "#{n} #{s}"
  end
end
