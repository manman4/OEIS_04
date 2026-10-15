# Erdős Problem #387
# Triangle read by rows:
#   T(n,k) = max{ d : 1 <= d <= n, d | binomial(n,k) },  n >= 2, 1 <= k < n
# n = 2..N 行を b401107_01.txt に "i T" 形式（i は通し番号, OFFSET 2 に合わせて 2 から）で保存
# （N = 141 で 9870 項、N = 142 で 10011 項）
#
# 行の最小値は A401108。

N = 141

File.open('b401107_01.txt', 'w') do |f|
  i = 1                           # OFFSET 2 に合わせて通し番号は 2 から
  (2..N).each do |n|
    c = 1                         # binomial(n,k)（整数のまま計算）
    row = []
    (1...n).each do |k|
      c = c * (n - k + 1) / k
      if 2 * k <= n
        d = n
        d -= 1 while c % d != 0   # n 以下で最大の約数
        row << d
      else
        row << row[n - k - 1]     # 対称性 T(n,k) = T(n,n-k)
      end
    end
    row.each do |v|
      i += 1
      f.puts "#{i} #{v}"
    end
  end
end
