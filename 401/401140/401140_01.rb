# Erdős Problem #443
# Triangle read by rows:
#   T(n,k) = #( {j*(n-j): 1 <= j <= floor(n/2)} ∩ {j*(k-j): 1 <= j <= floor(k/2)} ),
#   n >= 2, 1 <= k < n
# n = 2..N 行を b401140_01.txt に "i T" 形式（i は通し番号, OFFSET 2 に合わせて 2 から）で保存
# （N = 141 で 9870 項、N = 142 で 10011 項）

require 'set'

N = 141

S = Array.new(N + 1) { |m| (1..m / 2).map { |j| j * (m - j) }.to_set }

File.open('b401140_01.txt', 'w') do |f|
  i = 1                           # OFFSET 2 に合わせて通し番号は 2 から
  (2..N).each do |n|
    (1...n).each do |k|
      i += 1
      f.puts "#{i} #{(S[n] & S[k]).size}"
    end
  end
end
