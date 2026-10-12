# Erdős Problem #400 (k = 2): g_2(n)
# g_2(n) = max{ a + b - n : a, b >= 0 整数, a! b! | n! }
# n = 0..10000 について計算し b400979_01.txt に "n g_2(n)" 形式で保存
#
# 方針:
#   a = n - d, b = d + g とおくと
#     a! b! | n!  <=>  (d+g)! | n!/(n-d)! = d! * C(n,d)
#                 <=>  (d+1)(d+2)...(d+g) | C(n,d)
#   よって g_2(n) = max_d { g : (d+1)...(d+g) | C(n,d) }。
#   対称性 (a <-> b) から b <= a、すなわち 2d + g <= n としてよい。
#   a = n, b = 1 (d = 0, g = 1) により g_2(n) >= 1。
#   v_p(C(n,d)) は Kummer / Legendre: (s_p(d) + s_p(n-d) - s_p(n)) / (p-1)。

N = 10000

# 最小素因数ふるい
SPF = Array.new(N + 1, 0)
(2..N).each do |i|
  next if SPF[i] != 0
  (i..N).step(i) { |j| SPF[j] = i if SPF[j] == 0 }
end

# 素因数分解 [[p, e], ...]
FACT = Array.new(N + 1) { [] }
(2..N).each do |i|
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

def digit_sum(m, p)
  s = 0
  while m > 0
    s += m % p
    m /= p
  end
  s
end

def g2(n)
  # n = 0: 0! = 1 なので a, b ∈ {0, 1}、a = b = 1 で 2
  #（n >= 1 では a <= n が必要だが、n = 0 だけは 1! = 0! のため a = 1 > n が可能）
  return 2 if n == 0
  best = 1
  d = 1
  while 2 * d + best + 1 <= n
    # g >= best + 1 となるか調べ、なれば伸ばせるだけ伸ばす
    need = Hash.new(0)   # (d+1)...(d+g) の各素数の指数
    have = {}            # v_p(C(n,d)) のキャッシュ
    g = 0
    while 2 * d + g + 1 <= n
      t = d + g + 1
      ok = true
      FACT[t].each do |p, e|
        need[p] += e
        h = (have[p] ||= (digit_sum(d, p) + digit_sum(n - d, p) - digit_sum(n, p)) / (p - 1))
        if need[p] > h
          ok = false
          break
        end
      end
      break unless ok
      g += 1
    end
    best = g if g > best
    d += 1
  end
  best
end

File.open('b400979_01.txt', 'w') do |f|
  (0..N).each { |n| f.puts "#{n} #{g2(n)}" }
end
