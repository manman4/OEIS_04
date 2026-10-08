# A400867: Numbers k such that k and k+2 are both Ulam numbers.
# Writes b400867.txt with n = 1..10000.

N = 10000

# Ulam numbers up to limit, using a byte array of representation counts (capped at 2).
def ulam_flags(limit)
  cnt = "\0".b * (limit + 1)
  is_u = "\0".b * (limit + 1)
  ulams = []
  [1, 2].each { |u| is_u.setbyte(u, 1) }
  ulams << 1 << 2
  cnt.setbyte(3, 1)
  x = 3
  while x <= limit
    if cnt.getbyte(x) == 1
      is_u.setbyte(x, 1)
      ulams.each do |v|
        s = x + v
        break if s > limit
        c = cnt.getbyte(s)
        cnt.setbyte(s, c + 1) if c < 2
      end
      ulams << x
    end
    x += 1
  end
  is_u
end

limit = 1 << 16
loop do
  is_u = ulam_flags(limit)
  ary = []
  (1..limit - 2).each do |k|
    if is_u.getbyte(k) == 1 && is_u.getbyte(k + 2) == 1
      ary << k
      break if ary.size == N
    end
  end
  if ary.size == N
    File.open('b400867.txt', 'w') do |f|
      ary.each_with_index { |k, i| f.puts "#{i + 1} #{k}" }
    end
    break
  end
  limit *= 2
end
