# A401886 (Erdős Problem 844)
# a(n) = max |A|, A ⊆ {1..n}, such that a*b is not squarefree for all a, b in A
#        (a = b を含む)。
# Erdős Problem 844 の解決（Weisenberg; Alexeev-Mixon-Sawin、Chvátal の結果を使う）により、
# 最大値は「偶数すべて」と「squarefree でない奇数すべて」の集合で達成される。よって
#   a(n) = #{k <= n : k は偶数、または squarefree でない}
#        = n - #{k <= n : k は奇数かつ squarefree}.
# n = 1..N を計算し、b401886_01.txt に "n a(n)" 形式で保存する。
#
# 検算: n <= CHECK_N では、定義どおり全部分集合を調べる総当たりと照合してから保存する。
#
# 実行: ruby 401886_01.rb [N]   （N の既定値 10000、上限 10^7）

N = if ARGV.empty?
      10_000
    elsif ARGV[0] =~ /\A[1-9]\d*\z/ && ARGV[0].to_i <= 10_000_000
      ARGV[0].to_i
    else
      abort "usage: ruby 401886_01.rb [N]   (1 <= N <= 10000000)"
    end

FNAME = "b401886_01.txt"
CHECK_N = 14

if File.symlink?(FNAME) || (File.exist?(FNAME) && !File.file?(FNAME))
  abort "#{FNAME} is not a regular file; refusing to overwrite"
end

# 篩: squarefree[k] = k が squarefree か（k = 0..LIM）
LIM = [N, CHECK_N * CHECK_N].max
squarefree = Array.new(LIM + 1, true)
p = 2
while p * p <= LIM
  (p * p).step(LIM, p * p) { |j| squarefree[j] = false }
  p += 1
end

# a(n) を公式で計算
a = Array.new(N + 1, 0)
(1..N).each do |k|
  a[k] = a[k - 1] + ((k.even? || !squarefree[k]) ? 1 : 0)
end

# 総当たりとの照合（定義そのもの: すべての a, b ∈ A（a = b を含む）で a*b が squarefree でない）
(1..[CHECK_N, N].min).each do |n|
  best = 0
  (0...(1 << n)).each do |mask|
    elems = (1..n).select { |x| mask[x - 1] == 1 }
    next if elems.size <= best
    ok = elems.all? { |x| elems.all? { |y| !squarefree[x * y] } }
    best = elems.size if ok
  end
  abort "check failed at n=#{n}: brute=#{best}, formula=#{a[n]}" if best != a[n]
end

# 一時ファイルに全体を書いてから置き換える（途中で止まっても元のファイルは残る）
tmp = "#{FNAME}.tmp.#{Process.pid}"
begin
  File.open(tmp, File::WRONLY | File::CREAT | File::EXCL, 0o644) do |f|
    (1..N).each { |n| f.write("#{n} #{a[n]}\n") }
    f.flush
    f.fsync
  end
  File.rename(tmp, FNAME)
rescue StandardError => e
  File.delete(tmp) if File.exist?(tmp)
  abort "write failed: #{e.message}"
end

puts "wrote n = 1..#{N} to #{FNAME} (checked n <= #{[CHECK_N, N].min} by brute force)"
