# Erdős Problem 607
# F(n) = 平面上の n 点が決める直線それぞれの上の点の個数の集合
#        A = {|l ∩ P| : l は P の 2 点以上を通る直線} として現れうる集合の種類数。
# n = 1..N を計算し、b400000.txt に "n F(n)" 形式で保存する。
#
# 出力は推測・上界・下界ではなく F(n) の確定値である。各サイズ集合について、
# 必要な点数の下界と、ちょうどその点数で実現する構成（下の (2)）を示しているので
# 最小点数が確定し、F(n) はその最小点数が n 以下のサイズ集合をちょうど数える。
# Szemerédi-Trotter などの問題 607 に関する結果は使わない。
#
# 証明の出どころ:
#   ・Sylvester-Gallai の定理（古典的な定理）。
#   ・最小点数の式 L とその証明（下の (2): 下界と、①②③を満たす構成）は、
#     文献の結果ではなく独自に導いたもの（Seiichi Manyama による。Claude と検証）。
#     調べた範囲（問題 607 のページ、Lean による形式化、Web 検索）では、
#     この式も F(n) の具体的な値も文献に見当たらなかった。
#   ・(3)〜(5) は本ファイル内で証明している初等的な事実。
#   Szemerédi-Trotter の定理は上界 F(n) <= exp(O(sqrt(n)))（問題 607 の解決）を与えるだけで、
#   F(n) の正確な値には使っていない。
#
# 使う事実（証明つき）:
#  (1) Sylvester-Gallai の定理より、全点が一直線上にない限りちょうど 2 点の直線がある。
#      よって A は {n}（全点が共線）、または 2 を含む集合 {2} ∪ S（S は 3 以上の整数の有限集合、
#      全点が共線でない配置）。
#      n = 1 では直線がなく A = ∅ なので F(1) = 1。n = 2 では A = {2}（= {n}、共線）のみで F(2) = 1。
#      n >= 3 では {n} は 2 を含まないので、{2} ∪ S の形の集合とは重ならない。
#  (2) 全点が共線でない配置で {2} ∪ S を実現する最小点数 M(S):
#        S = ∅ なら 3、S = {s} なら s + 1（s 点の直線と外の 1 点）、
#        S = {s_1 < ... < s_r}（r >= 2）なら L = Sum_{i=1..r} max(0, s_i + i - r)。
#      下界: 大きい直線から順に数えると、l_i は後ろの r-i 本とそれぞれ高々 1 点しか
#      共有しないので、新しい点は max(0, s_i - (r-i)) 個以上。合計 L 個以上。
#      上界（構成）: 汎用的に選んだ r 本の直線 l_1, ..., l_r（l_i が s_i に対応）で、
#      i < j かつ j > r - s_i のときだけ交点 l_i ∩ l_j を点として入れ、各直線の点数が
#      s_i になるまで汎用的な点を補う。
#        ① 各直線の交点の数 c_i は s_i を超えない:
#           後ろの直線との交点は min(r-i, s_i) 個、前の直線 l_j（j < i）との交点は
#           s_j > r - i となる j の個数。
#           s_i <= r-i なら前の交点は 0 個（s_j < s_i <= r-i）で c_i = s_i。
#           s_i > r-i なら前の交点の s_j は区間 (r-i, s_i) の相異なる整数で
#           高々 s_i - (r-i) - 1 個、よって c_i <= s_i - 1。
#        ② 合計点数: 交点の数を I とすると各交点は 2 本に乗るので Sum c_i = 2I、
#           合計は I + Sum (s_i - c_i) = Sum s_i - I、I = Sum_i min(r-i, s_i) より
#           合計 = Sum_i max(0, s_i - (r-i)) = L。
#        ③ 余分な 3 点以上の直線はない: 直線を汎用的に選べば、同じ l_k に乗らない 3 交点は
#           共線にならない（ある交点にしか現れない直線だけを動かせば、共線になる位置は
#           高々 1 つ）。補う点も、既存の 2 点を結ぶ有限個の直線と他の l_j を避けて置く。
#      よって最小点数はちょうど L（S = ∅, {s} も同様に確定）。
#  (3) 全点が共線でない配置に汎用的な点を足すと、増えるのは 2 点の直線だけなので
#      A は変わらない。よって {2} ∪ S は M(S) <= n のとき、かつそのときに限り n 点で実現できる。
#  (4) M(S) <= n なら S ⊆ {3..n-1} は自動的に成り立つ（r = 1 なら s + 1 <= n、
#      r >= 2 なら最大の項 s_r と 2 番目の項 s_{r-1} - 1 >= 2 から s_r <= n - 2）。
#  以上から、n >= 3 で F(n) = 1 + Sum_{m <= n} G(m)、G(m) = #{S : M(S) = m}。
#
#  (5) G の閉じた数え方（r >= 2）: S を大きい順に s_(0) > s_(1) > ... > s_(r-1) とし、
#      t_k = s_(k) - k とおくと L = Sum_k max(0, t_k)。s_(k+1) <= s_(k) - 1 より
#      t_(k+1) <= t_k - 2 なので、正の t_k は最初の m 個で、
#      λ_k = t_k（k < m）は「差が 2 以上の相異なる正の整数」の列、L = |λ|。
#      ・μ_k = λ_k - 2(m-1-k) とおくと、μ は m 個の正の部分からなる分割で
#        |μ| = L - m(m-1)（λ と μ は一対一に対応）。μ_(m-1) = λ_(m-1)。
#      ・s_(k) >= 3 の条件: m >= 3 なら λ_k >= 1 + 2(m-1-k) から自動的に成り立つ。
#        m = 2 なら λ_1 >= 2（つまり μ_1 >= 2）が必要で、λ_0 >= λ_1 + 2 >= 3 は自動。
#      ・残りの要素（k >= m、t_k <= 0）は、s_(m) <= m かつ s_(m) < s_(m-1) = λ_(m-1)+m-1 を
#        満たせばよく（以後は t がさらに小さい）、{3..c} の任意の部分集合でよい。
#        c = m（λ_(m-1) >= 2 のとき）、c = m-1（λ_(m-1) = 1 のとき）。個数は 2^max(0, c-2)。
#      ・m = 1 なら c <= 1 で残りは空、r = 1 になるので除く。よって m >= 2。
#      P(X, m) = X を m 個の正の部分に分ける分割の数とすると、μ の最小部分が 2 以上のものは
#      P(X-m, m) 個、ちょうど 1 のものは P(X, m) - P(X-m, m) 個（X = L - m(m-1)）。
#      よって r >= 2 の部分は
#        G_2(L) = P(X-2, 2)  (m = 2)
#               + Sum_{m >= 3} [ P(X-m, m)*2^(m-2) + (P(X,m) - P(X-m,m))*2^(m-3) ]。
#      さらに S = ∅ が G(3) に 1、S = {s} が G(s+1) に 1 を加える。
#
# 計算はすべて整数（Ruby の多倍長整数）。P は P(X,m) = P(X-1,m-1) + P(X-m,m) で求める。
#
# 検算（保存前に自動で行う）:
#   n <= CHECK_ENUM_N  : S をすべて列挙して M(S) <= n を数える方法と照合。
#   n <= CHECK_DP_N    : (5) を使わず、s_(k) を 1 つずつ選ぶ動的計画法と照合。
#
# 実行: ruby 400000_01.rb [N]   （N の既定値 1000、上限 20000）
# N = 10000 で約 2 秒。上限はメモリ（P の表は約 sqrt(N) * N 個の多倍長整数）で決めている。

N = if ARGV.empty?
      1000
    elsif ARGV[0] =~ /\A[1-9]\d*\z/ && ARGV[0].to_i <= 20_000
      ARGV[0].to_i
    else
      abort "usage: ruby 400000_01.rb [N]   (1 <= N <= 20000)"
    end

FNAME = "b401948.txt"
CHECK_ENUM_N = 20
CHECK_DP_N = 300

if File.symlink?(FNAME) || (File.exist?(FNAME) && !File.file?(FNAME))
  abort "#{FNAME} is not a regular file; refusing to overwrite"
end

def prefix_to_f(g, nmax)
  vals = []
  acc = 0
  (1..nmax).each do |n|
    acc += g[n]
    vals << (n <= 2 ? 1 : 1 + acc)
  end
  vals
end

# ---------- 本計算: (5) の分割による数え方 ----------
def f_partition(nmax)
  mmax = 1
  mmax += 1 while (mmax + 1) * mmax <= nmax     # m(m-1) <= nmax となる最大の m
  # p[m][x] = x を m 個の正の部分に分ける分割の数（x <= nmax）
  p = Array.new(mmax + 1) { Array.new(nmax + 1, 0) }
  p[0][0] = 1
  (1..mmax).each do |m|
    prev = p[m - 1]
    row = p[m]
    (m..nmax).each { |x| row[x] = prev[x - 1] + row[x - m] }
  end
  g = Array.new(nmax + 1, 0)
  g[3] += 1 if nmax >= 3                         # S = ∅
  (4..nmax).each { |l| g[l] += 1 }               # S = {s}、l = s + 1
  (2..mmax).each do |m|
    base = m * (m - 1)
    row = p[m]
    w_ge2 = m >= 3 ? (1 << (m - 2)) : 1
    w_eq1 = m >= 3 ? (1 << (m - 3)) : 0          # m = 2 では μ_1 = 1 は不可
    (base..nmax).each do |l|
      x = l - base
      ge2 = x >= m ? row[x - m] : 0
      eq1 = row[x] - ge2
      g[l] += ge2 * w_ge2 + eq1 * w_eq1
    end
  end
  prefix_to_f(g, nmax)
end

# ---------- 検算 1: (5) を使わない動的計画法 ----------
# cur[s][t] = s_(k) = s（> k）、項の和 t の個数。次の要素 s2 < s を選ぶ。
def f_dp(nmax)
  g = Array.new(nmax + 1, 0)
  g[3] += 1 if nmax >= 3
  (3..nmax).each { |s| g[s + 1] += 1 if s + 1 <= nmax }
  cur = Array.new(nmax + 1)
  (3..nmax).each do |s|
    row = Array.new(nmax + 1, 0)
    row[s] = 1
    cur[s] = row
  end
  k = 0
  loop do
    (3..nmax).each do |s|
      row = cur[s]
      next unless row
      m = [s - 1, k + 1].min                     # s2 <= k+1 なら項は 0（以後すべて 0）
      factor = (k >= 1 ? 1 : 0) + (m >= 3 ? (1 << (m - 2)) - 1 : 0)
      next if factor == 0
      row.each_with_index { |w, t| g[t] += w * factor if w != 0 }
    end
    nxt = Array.new(nmax + 1)
    any = false
    running = Array.new(nmax + 1, 0)             # Sum_{s > s2} cur[s][t]
    (nmax - 1).downto(k + 2) do |s2|
      src = cur[s2 + 1]
      src&.each_with_index { |w, t| running[t] += w if w != 0 }
      term = s2 - (k + 1)
      row = nil
      (term..nmax).each do |t2|
        w = running[t2 - term]
        next if w == 0
        row ||= Array.new(nmax + 1, 0)
        row[t2] = w
      end
      if row
        nxt[s2] = row
        any = true
      end
    end
    break unless any
    cur = nxt
    k += 1
  end
  prefix_to_f(g, nmax)
end

# ---------- 検算 2: 全列挙 ----------
def min_points(sset)
  r = sset.size
  return 3 if r == 0
  return sset[0] + 1 if r == 1
  (1..r).sum { |i| [0, sset[i - 1] + i - r].max }
end

def f_enum(n)
  return 1 if n <= 2
  c = 1                                          # {n}
  vals = (3..n - 1).to_a
  (0..vals.size).each do |r|
    vals.combination(r) { |sset| c += 1 if min_points(sset) <= n }
  end
  c
end

values = f_partition(N)

dp_n = [CHECK_DP_N, N].min
dp_vals = f_dp(dp_n)
(0...dp_n).each do |i|
  abort "check failed at n=#{i + 1}: partition=#{values[i]}, dp=#{dp_vals[i]}" if values[i] != dp_vals[i]
end
(1..[CHECK_ENUM_N, N].min).each do |n|
  e = f_enum(n)
  abort "check failed at n=#{n}: partition=#{values[n - 1]}, enumeration=#{e}" if e != values[n - 1]
end

# 一時ファイルに全体を書いてから置き換える（途中で止まっても元のファイルは残る）
tmp = "#{FNAME}.tmp.#{Process.pid}"
begin
  File.open(tmp, File::WRONLY | File::CREAT | File::EXCL, 0o644) do |f|
    values.each_with_index { |v, i| f.write("#{i + 1} #{v}\n") }
    f.flush
    f.fsync
  end
  File.rename(tmp, FNAME)
rescue StandardError => e
  File.delete(tmp) if File.exist?(tmp)
  abort "write failed: #{e.message}"
end

puts "wrote n = 1..#{N} to #{FNAME} (checked n <= #{dp_n} by DP, n <= #{[CHECK_ENUM_N, N].min} by enumeration)"
