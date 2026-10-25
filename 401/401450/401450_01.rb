# Erdős Problem #437
# a(n) = L(n) = 1 <= a_1 < ... < a_k <= n の部分積 a_1, a_1 a_2, ..., a_1 ... a_k のうち
#        平方数になりうるものの最大個数
# n = 1..10000 について計算し b401450_01.txt に "n a(n)" 形式で保存
#
# 方針:
#   m の平方因子を除いた部分を GF(2) 上のベクトル vec[m]（素数ごとの指数の偶奇）とみなす。
#   部分積が平方数 <=> それまでのベクトルの和が 0。
#   よって選んだ数を、積が平方数になる「順に並んだ互いに重ならないブロック」に分けたときの
#   ブロック数の最大値が L(n)。ブロックが [s,t] 内に取れる <=> vec[s..t] が一次従属。
#   s*(t) = vec[s..t] が一次従属となる最大の s とすると（区間を広げると従属性は保たれる）
#     f(t) = max( f(t-1), f(s*(t)-1) + 1 ),  L(n) = f(n)。

N = 10000

SPF = Array.new(N + 1, 0)
(2..N).each do |i|
  next if SPF[i] != 0
  (i..N).step(i) { |j| SPF[j] = i if SPF[j] == 0 }
end
pidx = {}
(2..N).each { |i| pidx[i] = pidx.size if SPF[i] == i }

# vec[m]: 素数 p の指数が奇数なら bit pidx[p] を立てる（vec[1] = 0）
VEC = Array.new(N + 1, 0)
(2..N).each do |m|
  x = m
  v = 0
  while x > 1
    p = SPF[x]
    e = 0
    while x % p == 0
      x /= p
      e += 1
    end
    v ^= (1 << pidx[p]) if e.odd?
  end
  VEC[m] = v
end

# vec[s..t] が一次従属となる最大の s（なければ nil）
def dep_start(t)
  basis = {}                      # 最上位ビット -> 基底ベクトル
  s = t
  while s >= 1
    v = VEC[s]
    while v != 0
      hb = v.bit_length - 1
      if basis[hb]
        v ^= basis[hb]
      else
        basis[hb] = v
        break
      end
    end
    return s if v == 0
    s -= 1
  end
  nil
end

f = Array.new(N + 1, 0)
File.open('b401450_01.txt', 'w') do |out|
  (1..N).each do |t|
    f[t] = f[t - 1]
    s = dep_start(t)
    f[t] = f[s - 1] + 1 if s && f[s - 1] + 1 > f[t]
    out.puts "#{t} #{f[t]}"
  end
end
