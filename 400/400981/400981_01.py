"""Compute A400981 for n=0..10000 using only Python's standard library.

a(n) = max(r+s+t-n : r,s,t >= 1 and r!*s!*t! divides n!).
All arithmetic is exact. No C++, compiler, external packages, or input files
are required. Run: python3 400981_01.py
"""

import argparse
from pathlib import Path
from time import perf_counter


def primes_up_to(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, limit + 1):
        if sieve[p]:
            yield p
            if p * p <= limit:
                sieve[p * p::p] = b"\x00" * ((limit - p * p) // p + 1)


def valuation_factorial(n, p):
    result = 0
    while n:
        n //= p
        result += n
    return result


# Binary choices for (r,s,t), grouped by incoming carry and target digit.
# Higher carry choices are visited first. Entries are (next carry, rbit,
# sbit, tbit); all compatible choices are included.
TRANSITIONS = {
    (carry, digit): tuple(
        ((mask.bit_count() + carry) // 2, mask & 1,
         (mask >> 1) & 1, (mask >> 2) & 1)
        for mask in range(7, -1, -1)
        if (mask.bit_count() + carry) % 2 == digit
    )
    for carry in range(3) for digit in range(2)
}


def has_triple(n, excess, primes, small):
    total = n + excess
    bits = total.bit_length()
    # Legendre: v_2((n+E)!/n!) = E-s_2(n+E)+s_2(n).
    needed = excess - total.bit_count() + n.bit_count()
    transitions = [tuple(TRANSITIONS[c, (total >> pos) & 1]
                         for c in range(3)) for pos in range(bits)]
    remaining = [[-1000] * 3 for _ in range(bits + 1)]
    remaining[bits][0] = 0
    for pos in range(bits - 1, -1, -1):
        for carry in range(3):
            remaining[pos][carry] = max(
                nxt + remaining[pos + 1][nxt]
                for nxt, *_ in transitions[pos][carry]
            )
    if remaining[0][0] < needed:
        return False

    targets = [v[n] for v in small]
    rest = primes[len(small):]
    rest_targets = [valuation_factorial(n, p) for p in rest]

    def divides(r, s, t):
        if r < 1 or r > s or s > t:
            return False
        for v, target in zip(small, targets):
            if v[r] + v[s] + v[t] > target:
                return False
        for p, target in zip(rest, rest_targets):
            if (valuation_factorial(r, p) + valuation_factorial(s, p)
                    + valuation_factorial(t, p) > target):
                return False
        return True

    def visit(pos, carry, mass, r, s, t):
        if r > n or s > n or t > n:
            return False
        if mass + remaining[pos][carry] < needed:
            return False
        if pos == bits:
            return carry == 0 and divides(r, s, t)
        weight = 1 << pos
        for nxt, rb, sb, tb in transitions[pos][carry]:
            if visit(pos + 1, nxt, mass + nxt,
                     r + rb * weight, s + sb * weight, t + tb * weight):
                return True
        return False

    # Kummer's theorem identifies binary carry mass with the valuation
    # of total!/(r!s!t!). The recursion visits every possible bit triple
    # except branches excluded by necessary index or valuation bounds.
    return visit(0, 0, 0, 0, 0, 0)


def compute(limit, progress=False):
    """Return a(0), ..., a(limit) using exact exhaustive search."""
    if not 0 <= limit <= 10000:
        raise ValueError("limit must be between 0 and 10000")
    primes = list(primes_up_to(limit))
    small = [[valuation_factorial(n, p) for n in range(limit + 1)]
             for p in primes[:12]]
    # At n=0, r=s=t=1 is the only positive triple; the value is 3.
    values = [3]
    prime_count = 0
    for n in range(1, limit + 1):
        while prime_count < len(primes) and primes[prime_count] <= n:
            prime_count += 1
        active_primes = primes[:prime_count]
        active_small = small[:min(12, prime_count)]
        # For n>=1, each index is <=n, and (n,1,1) always gives 2.
        # Legendre at p=2 gives E <= 3*bit_length(n)-popcount(n).
        upper = min(2 * n, 3 * n.bit_length() - n.bit_count())
        best = 2
        for excess in range(upper, 2, -1):
            if has_triple(n, excess, active_primes, active_small):
                best = excess
                break
        values.append(best)
        if progress and n % 1000 == 0:
            print(f"n={n}, a(n)={best}", flush=True)
    return values


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=10000)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("b400981.txt"))
    args = parser.parse_args()
    if not 0 <= args.limit <= 10000:
        parser.error("--limit must be between 0 and 10000")
    start = perf_counter()
    values = compute(args.limit, progress=True)
    args.output.write_text(
        "".join(f"{n} {value}\n" for n, value in enumerate(values)),
        encoding="ascii",
    )
    print(f"Wrote {len(values)} terms to {args.output}; "
          f"{perf_counter() - start:.2f} seconds")


if __name__ == "__main__":
    main()
