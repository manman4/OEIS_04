# A401757 (Erdős Problem 675, question 3)
# a(n) = least t >= 1 such that, for all 1 <= x <= n,
#        x is squarefree if and only if x + t is squarefree.
# n = 1..N を計算し、b401757_01.txt に "n a(n)" 形式で保存する。
#
# 数学的な事実（どれも証明つき）:
#   (1) a(n) は存在する（Erdős Problem 675 のページにあるとおり、初等的な篩で
#       squarefree 数は平行移動性をもつ）。よって探索は必ず止まる。
#   (2) a(n-1) <= a(n)。t が n で条件を満たせば、x <= n-1 でも満たすから。
#       よって a(n) の探索は t = a(n-1) から始めてよく、t が n で条件を満たせば
#       その t は n+1, n+2, ... でも試すだけでよい。
#
# 方法:
#   x = 1..n の squarefree 判定を 0/1 の列 pat にする。数直線を区間に分け、
#   区間ごとに p^2 の倍数を消す篩で squarefree 判定の列 buf を作る。
#   「x+t (x = 1..n) の判定列 = pat」となる最小の t を、String#index（C で実装された
#   部分文字列探索）で探す。位置 i が数 base+i に対応する。
#
# 実行: ruby 401757_01.rb [N]   （N の既定値 200、上限 1000）
# n = 200 で a(200) = 3609452700 なので、約 3.6*10^9 までの篩が必要になる。

N = if ARGV.empty?
      200
    elsif ARGV[0] =~ /\A[1-9]\d*\z/ && ARGV[0].to_i <= 1000
      ARGV[0].to_i
    else
      abort "usage: ruby 401757_01.rb [N]   (1 <= N <= 1000)"
    end

FNAME = "b401757_01.txt"
SEG = 1 << 24                  # 1 区間で調べる t の個数

if File.symlink?(FNAME) || (File.exist?(FNAME) && !File.file?(FNAME))
  abort "#{FNAME} is not a regular file; refusing to overwrite"
end

def squarefree?(x)
  d = 2
  while d * d <= x
    return false if x % (d * d) == 0
    d += 1
  end
  true
end

# pat[x-1] = x が squarefree なら "\x01"、そうでなければ "\x00"（x = 1..N）
pat = (1..N).map { |x| squarefree?(x) ? "\x01" : "\x00" }.join.b

# 篩に使う素数（必要に応じて増やす）
$primes = []
$plimit = 1
def ensure_primes(limit)
  return if limit <= $plimit
  newlimit = [limit, $plimit * 2].max
  is = Array.new(newlimit + 1, true)
  is[0] = is[1] = false
  i = 2
  while i * i <= newlimit
    if is[i]
      (i * i).step(newlimit, i) { |j| is[j] = false }
    end
    i += 1
  end
  $primes = (2..newlimit).select { |x| is[x] }
  $plimit = newlimit
end

results = []                   # [n, a(n)]
n = 1
t = 1                          # 次に試す t（a(n-1) 以上）
base = 1                       # buf[i] は数 base+i の判定
len = SEG + N                  # t = base-1 .. base-2+SEG の窓 x+t (x<=N) を含む長さ
ones = ("\x01" * len).b

while n <= N
  hi = base + len - 1
  ensure_primes(Integer.sqrt(hi) + 1)
  buf = ones.dup
  $primes.each do |p|
    q = p * p
    break if q > hi
    j = ((base + q - 1) / q) * q - base
    while j < len
      buf.setbyte(j, 0)
      j += q
    end
  end

  # 窓の先頭（数 t+1）の位置 = t+1-base。t は base-1 .. base-2+SEG を担当する
  last_t = base - 2 + SEG
  while n <= N && t <= last_t
    pos = buf.index(pat[0, n], t + 1 - base)
    break if pos.nil? || pos + base - 1 > last_t
    t = pos + base - 1
    # t は n で条件を満たす。続く n でも満たす限り同じ t が最小値（事実 (2)）
    while n <= N && buf.getbyte(t + n - base) == pat.getbyte(n - 1)
      results << [n, t]
      $stdout.puts "#{n} #{t}"
      $stdout.flush
      n += 1
    end
    t += 1
  end
  t = [t, last_t + 1].max
  base += SEG
end

# 検算: 求めた各 a(n) が実際に条件を満たすことを、篩とは別の直接の判定
# （素数 p について p^2 で割れるかを調べる）で確かめる。
# 同じ t が続く n では最大の n だけ調べれば足りる。
def squarefree_by_primes?(x)
  $primes.each do |p|
    q = p * p
    break if q > x
    return false if x % q == 0
  end
  true
end
results.group_by { |_, tt| tt }.each do |tt, rows|
  nn = rows.map(&:first).max
  ensure_primes(Integer.sqrt(nn + tt) + 1)
  (1..nn).each do |x|
    if squarefree?(x) != squarefree_by_primes?(x + tt)
      abort "verification failed at n=#{nn}, t=#{tt}, x=#{x}"
    end
  end
end

# 一時ファイルに全体を書いてから置き換える（途中で止まっても元のファイルは残る）
tmp = "#{FNAME}.tmp.#{Process.pid}"
begin
  File.open(tmp, File::WRONLY | File::CREAT | File::EXCL, 0o644) do |f|
    results.each { |nn, tt| f.write("#{nn} #{tt}\n") }
    f.flush
    f.fsync
  end
  File.rename(tmp, FNAME)
rescue StandardError => e
  File.delete(tmp) if File.exist?(tmp)
  abort "write failed: #{e.message}"
end
