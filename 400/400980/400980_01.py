"""Compute A400980 for 0 <= n <= 10000 using exact integer arithmetic.

a(n) = Sum_{j=0..n} A400979(j), where
A400979(j) = max(r + s - j : r,s >= 1 and r!*s! divides j!).
Computes A400979 internally: no input files or other sequence scripts needed.
Requires NumPy. Run: python3 400980_01.py
The output defaults to b400980.txt beside this script.
"""

import argparse
from itertools import accumulate
from math import isqrt
from pathlib import Path
from time import perf_counter

import numpy as np


def primes_up_to(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p::p] = b"\x00" * ((limit - p * p) // p + 1)
    return [p for p in range(2, limit + 1) if sieve[p]]


def compute_a400979(limit):
    """Return A400979(0), ..., A400979(limit), with A400979(0)=2."""
    if not 0 <= limit <= 10000:
        raise ValueError("limit must be between 0 and 10000")
    if limit == 0:
        return [2]
    primes = primes_up_to(limit)
    indices = np.arange(limit + 1, dtype=np.int32)
    # valuations[m,j] = v_p(m!). All entries and sums fit in int32:
    # v_p(m!) <= m <= 10000, and two such entries sum to <= 20000.
    valuations = np.zeros((limit + 1, len(primes)), dtype=np.int32)
    for j, p in enumerate(primes):
        quotient = indices.copy()
        while True:
            quotient //= p
            if not quotient.any():
                break
            valuations[:, j] += quotient

    # At j=0, the only positive pair is (r,s)=(1,1), giving 2.
    values = [2]
    for n in range(1, limit + 1):
        # (n,1) is admissible, so a(n) >= 1. Each index is <= n.
        # If E = r+s-n > 0, (n+1)...(n+E) divides C(n+E,r).
        # Its 2-adic valuation is >= v_2(E!) = E-popcount(E), whereas
        # Kummer's theorem gives v_2(C(n+E,r)) <= floor(log2(2*n)).
        # Also E <= 2*floor(log2(n))+1 by Legendre's digit-sum formula.
        binary_length = (2 * n).bit_length() - 1
        rough_bound = min(n, 2 * (n.bit_length() - 1) + 1)
        upper = max(e for e in range(1, rough_bound + 1)
                    if e - e.bit_count() <= binary_length)
        count = int(np.searchsorted(primes, n, side="right"))
        target = valuations[n, :count]
        best = 1
        for excess in range(upper, 1, -1):
            total = n + excess
            # Symmetry permits r <= s; s <= n implies r >= excess.
            candidates = np.arange(excess, total // 2 + 1, dtype=np.int32)
            # Necessary small-prime tests remove most pairs cheaply.
            for j in range(min(12, count)):
                candidates = candidates[
                    valuations[candidates, j]
                    + valuations[total - candidates, j] <= target[j]
                ]
                if not candidates.size:
                    break
            if not candidates.size:
                continue
            # Every survivor must pass ALL prime valuations. Checking p <= n
            # suffices because r,s <= n. Bound temporary allocations in batches.
            found = False
            for start in range(0, len(candidates), 128):
                r = candidates[start:start + 128]
                ok = np.all(
                    valuations[r, :count] + valuations[total - r, :count]
                    <= target, axis=1
                )
                if ok.any():
                    found = True
                    break
            if found:
                best = excess
                break
        values.append(best)
    return values


def compute(limit):
    """Return A400980(0), ..., A400980(limit) without reading any b-file."""
    return list(accumulate(compute_a400979(limit)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=10000)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("b400980.txt"))
    args = parser.parse_args()
    started = perf_counter()
    values = compute(args.limit)
    args.output.write_text(
        "".join(f"{n} {value}\n" for n, value in enumerate(values)),
        encoding="ascii",
    )
    print(f"Wrote {len(values)} terms to {args.output}; "
          f"a({args.limit}) = {values[-1]}; "
          f"{perf_counter() - started:.2f} seconds")


if __name__ == "__main__":
    main()
