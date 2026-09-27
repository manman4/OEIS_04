# A(x) = (1 + x*A(x^2))^3.
#
# Put C(x) = 1 + x*A(x^2), so that A(x) = C(x)^3.  Logarithmic
# differentiation gives
#
#   C(x)*A'(x) = 3*A(x)*C'(x).
#
# Since c(0) = 1, c(2*j+1) = a(j), and all other positive c(n) vanish,
# coefficient comparison gives the single-sum recurrence
#
#   n*a(n) = Sum_{2*j+1<=n} (4*(2*j+1)-n)*a(j)*a(n-2*j-1).
#
# This computes the same sequence without the double and triple convolution
# sums in the direct recurrence.

def coefficients(maximum_n)
  values = Array.new(maximum_n + 1, 0)
  values[0] = 1

  n = 1
  while n <= maximum_n
    sum = 0
    j = 0
    k = 1

    while k <= n
      sum += (4 * k - n) * values[j] * values[n - k]
      j += 1
      k += 2
    end

    quotient, remainder = sum.divmod(n)
    raise "nonintegral coefficient at n=#{n}" unless remainder.zero?

    values[n] = quotient
    n += 1
  end

  values
end

maximum_n = 10_000
values = coefficients(maximum_n)

values.each_with_index do |value, n|
  break if value.to_s.size > 1_000

  puts "#{n} #{value}"
end
