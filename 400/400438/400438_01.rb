#!/usr/bin/env ruby
# frozen_string_literal: true

# OEIS A400438
#
# Compute the coefficients of the unique formal power series A(x), A(0)=1,
# satisfying
#
#   A(x) = (1 + x*A(x^k))^2,  k >= 2.
#
# Expanding the square gives
#
#   A(x) = 1 + 2*x*A(x^k) + x^2*A(x^k)^2.
#
# Hence, for n >= 0,
#
#   a(k*n + 1) = 2*a(n),
#   a(k*n + 2) = sum(j=0..n, a(j)*a(n-j)),
#
# and every other positive-index coefficient is zero.  For k=2 the second
# family is a(2*n+2); the same implementation covers it without a special
# case.  The restriction k >= 2 is necessary because the two target-index
# families overlap when k=1.
#
# Usage:
#   ruby 400438_01.rb                 # k=2, n=0..30
#   ruby 400438_01.rb K               # given k, n=0..30
#   ruby 400438_01.rb K MAX_N         # given k, n=0..MAX_N
#   ruby 400438_01.rb --term K N      # print a(N)
#   ruby 400438_01.rb --check         # run independent checks
#
# Ordinary output uses the two-column OEIS b-file format "n a(n)".

module A400438
  DEFAULT_K = 2
  DEFAULT_MAX_N = 30

  KNOWN_PREFIXES = {
    2 => [1, 2, 1, 4, 4, 2, 6, 8, 12, 8, 25],
    3 => [1, 2, 1, 0, 4, 4, 0, 2, 6, 0, 0, 4, 0, 8, 9],
    4 => [1, 2, 1, 0, 0, 4, 4, 0, 0, 2, 6, 0, 0, 0, 4, 0],
    5 => [1, 2, 1, 0, 0, 0, 4, 4, 0, 0, 0, 2, 6, 0, 0, 0, 0, 4]
  }.freeze

  class InputError < StandardError; end
  class CalculationError < StandardError; end

  module_function

  def parse_integer(text, label, minimum)
    value = Integer(text, 10)
    if value < minimum
      raise InputError, "#{label} must be at least #{minimum}: #{text}"
    end

    value
  rescue ArgumentError
    raise InputError, "#{label} must be an integer: #{text}"
  end

  # Generate a(0),...,a(maximum_n) from the coefficient recurrence.
  def terms(k, maximum_n)
    unless k.is_a?(Integer) && k >= 2
      raise InputError, "K must be an integer at least 2: #{k.inspect}"
    end
    unless maximum_n.is_a?(Integer) && maximum_n >= 0
      raise InputError,
            "MAX_N must be a nonnegative integer: #{maximum_n.inspect}"
    end

    values = Array.new(maximum_n + 1, 0)
    values[0] = 1

    source_index = 0
    loop do
      linear_target = k * source_index + 1
      break if linear_target > maximum_n

      values[linear_target] = 2 * values[source_index]

      convolution_target = linear_target + 1
      if convolution_target <= maximum_n
        convolution = 0
        0.upto(source_index) do |left_index|
          convolution +=
            values[left_index] * values[source_index - left_index]
        end
        values[convolution_target] = convolution
      end

      source_index += 1
    end

    values
  end

  # Independent truncated-series fixed-point iteration of
  # A(x) = 1 + 2*x*A(x^k) + x^2*A(x^k)^2.
  # This is used only by --check and does not use the coefficient recurrence
  # implemented in terms.
  def fixed_point_terms(k, maximum_n)
    current = Array.new(maximum_n + 1, 0)
    current[0] = 1

    (maximum_n + 1).times do
      following = Array.new(maximum_n + 1, 0)
      following[0] = 1

      current.each_with_index do |coefficient, index|
        target = k * index + 1
        break if target > maximum_n

        following[target] += 2 * coefficient
      end

      current.each_with_index do |left, left_index|
        break if k * left_index + 2 > maximum_n
        next if left.zero?

        current.each_with_index do |right, right_index|
          target = k * (left_index + right_index) + 2
          break if target > maximum_n
          next if right.zero?

          following[target] += left * right
        end
      end

      current = following
    end

    current
  end

  def check
    KNOWN_PREFIXES.each do |k, expected|
      actual = terms(k, expected.length - 1)
      next if actual == expected

      raise CalculationError,
            "known-prefix check failed for k=#{k}:\n" \
            "expected #{expected.inspect}\n" \
            "     got #{actual.inspect}"
    end

    2.upto(8) do |k|
      maximum_n = 60
      recurrence = terms(k, maximum_n)
      fixed_point = fixed_point_terms(k, maximum_n)
      next if recurrence == fixed_point

      raise CalculationError,
            "fixed-point check failed for k=#{k}:\n" \
            "recurrence #{recurrence.inspect}\n" \
            "fixed point #{fixed_point.inspect}"
    end

    warn 'ok: known prefixes and fixed-point checks agree for k=2..8'
  end

  def usage(program)
    <<~USAGE
      usage: #{program}
             #{program} K
             #{program} K MAX_N
             #{program} --term K N
             #{program} --check

      Compute coefficients of A(x) = (1 + x*A(x^K))^2 for K >= 2.
      Ordinary output is in two-column "n a(n)" format.
      Defaults: K=#{DEFAULT_K}, MAX_N=#{DEFAULT_MAX_N}.
    USAGE
  end

  def run(arguments, program)
    if arguments == ['--help'] || arguments == ['-h']
      puts usage(program)
      return
    end

    if arguments == ['--check']
      check
      return
    end

    if arguments.first == '--term'
      raise InputError, usage(program) unless arguments.length == 3

      k = parse_integer(arguments[1], 'K', 2)
      n = parse_integer(arguments[2], 'N', 0)
      puts terms(k, n)[n]
      return
    end

    k, maximum_n =
      case arguments.length
      when 0
        [DEFAULT_K, DEFAULT_MAX_N]
      when 1
        [parse_integer(arguments[0], 'K', 2), DEFAULT_MAX_N]
      when 2
        [
          parse_integer(arguments[0], 'K', 2),
          parse_integer(arguments[1], 'MAX_N', 0)
        ]
      else
        raise InputError, usage(program)
      end

    terms(k, maximum_n).each_with_index do |value, index|
      puts "#{index} #{value}"
    end
  end
end

if __FILE__ == $PROGRAM_NAME
  begin
    A400438.run(ARGV, $PROGRAM_NAME)
  rescue A400438::InputError, A400438::CalculationError => e
    warn e.message
    exit 1
  end
end
