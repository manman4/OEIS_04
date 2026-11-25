# A402703 (Erdős Problem 294)
# a(n) = 1 を相異なる単位分数の和で表すとき、最小の分母が k で最大の分母が n 以下となる
#        表し方が存在しない最小の正の整数 k。
#      = min{k : A294651(k) > n}（証明は 402703_formula_proof.md）。
# n = 1..N を計算し、カンマ区切りで標準出力に書く（ファイルは作らない）。
#
# A294651(k)（k から始まる表し方の最大の分母の最小値）の値は OEIS の A294651 から取った。
# k <= CHECK_K は、Rational による厳密な探索で独立に計算し直して照合する。
#
# 実行: ruby 402703_01.rb [N]   （N の既定値 80、1 <= N <= 143）

# OEIS A294651, n = 1..25
A294651 = [1, 6, 15, 20, 24, 28, 33, 40, 48, 52, 65, 65, 75, 76, 85, 88, 91, 100, 105, 115,
           115, 119, 132, 140, 144].freeze
CHECK_K = 5

N = if ARGV.empty?
      80
    elsif ARGV[0] =~ /\A[1-9]\d*\z/ && ARGV[0].to_i <= A294651.last - 1
      ARGV[0].to_i
    else
      abort "usage: ruby 402703_01.rb [N]   (1 <= N <= #{A294651.last - 1})"
    end

# 1 - 1/k を、k より大きく m 以下の相異なる分母の単位分数の和で表せるか
def representable?(k, m)
  suff = Array.new(m + 2, 0r)                    # suff[d] = 1/d + ... + 1/m
  m.downto(k + 1) { |d| suff[d] = suff[d + 1] + Rational(1, d) }
  dfs = lambda do |rem, d|
    return true if rem.zero?
    return false if d > m || suff[d] < rem         # 残りの分母をすべて使っても届かない
    return true if Rational(1, d) <= rem && dfs.call(rem - Rational(1, d), d + 1)
    dfs.call(rem, d + 1)
  end
  dfs.call(1 - Rational(1, k), k + 1)
end

# A294651(k) を定義どおり計算する（最大の分母 m を k から順に増やす）
def min_largest(k)
  return 1 if k == 1                             # 1 = 1/1
  m = k
  m += 1 until representable?(k, m)
  m
end

(1..CHECK_K).each do |k|
  v = min_largest(k)
  abort "check failed: A294651(#{k}) = #{A294651[k - 1]}, computed #{v}" if v != A294651[k - 1]
end

# a(n) = min{k : A294651(k) > n}。A294651(k) >= k なので k <= n+1 の範囲に必ずある。
values = (1..N).map { |n| (1..A294651.size).find { |k| A294651[k - 1] > n } }
abort "A294651 data too short" if values.include?(nil)
puts values.join(", ")
