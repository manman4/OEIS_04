"""Write the first N downward antidiagonals of A401328 to b401328.txt.

A(n,k) counts distinct values of s_k(n+1), ..., s_k(n+k), where s_k(m)
is the largest divisor of m with all prime factors strictly less than k.
The square array has n >= 0 and k >= 1.
In particular, s_1(m) = s_2(m) = 1, and s_k(1) = 1.

Order: A(0,1), A(0,2), A(1,1), A(0,3), A(1,2), A(2,1), ...
Antidiagonal d has n+k=d and contains d terms (n = 0..d-1).
The b-file has flattened indices 0..N*(N+1)//2-1.

Usage: python3 401328_01.py [N]  (default N = 100).
The output file is saved beside this script.
Only the Python standard library and exact integer arithmetic are used.
Complete antidiagonals are streamed using O(N) working memory.
"""

import argparse
from collections.abc import Iterator
from math import isqrt
from pathlib import Path


N = 100
OUTPUT = Path(__file__).resolve().with_name("b401328.txt")


def prime_flags(limit: int) -> list[bool]:
    """Return primality flags for integers 0..limit (limit >= 2)."""
    flags = [True] * (limit + 1)
    flags[0] = flags[1] = False
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            for multiple in range(p * p, limit + 1, p):
                flags[multiple] = False
    return flags


def antidiagonals(limit: int) -> Iterator[list[int]]:
    """Yield antidiagonals 1..limit, with n increasing within each."""
    if limit < 1:
        raise ValueError("N must be at least 1")

    is_prime = prime_flags(limit + 1)
    for total in range(1, limit + 1):
        # For n+k=total, the interval is [total-k+1, total].
        # Start with s_1(m)=1, and increase k while extending this interval.
        components = [1] * (total + 1)
        frequencies: dict[int, int] = {}
        diagonal = []

        for k in range(1, total + 1):
            # Raising the strict cutoff from k-1 to k introduces exactly
            # the prime p=k-1, if prime. Include its full power in each
            # multiple m, updating frequencies only for the old interval.
            p = k - 1
            if p >= 2 and is_prime[p]:
                old_lower = total - k + 2
                for m in range(p, total + 1, p):
                    remainder, power = m, 1
                    while remainder % p == 0:
                        remainder //= p
                        power *= p
                    old = components[m]
                    new = old * power
                    components[m] = new
                    if m >= old_lower:
                        frequencies[old] -= 1
                        if frequencies[old] == 0:
                            del frequencies[old]
                        frequencies[new] = frequencies.get(new, 0) + 1

            # Add the new left endpoint using its updated component.
            value = components[total - k + 1]
            frequencies[value] = frequencies.get(value, 0) + 1
            diagonal.append(len(frequencies))

        # Increasing k was convenient for computation; downward
        # antidiagonal order instead has n increasing and k decreasing.
        diagonal.reverse()
        yield diagonal


def write_bfile(limit: int, output: Path = OUTPUT) -> int:
    """Write N complete antidiagonals with flattened indices starting at 0."""
    if limit < 1:
        raise ValueError("N must be at least 1")
    index = 0
    with output.open("w", encoding="utf-8") as stream:
        for diagonal in antidiagonals(limit):
            for value in diagonal:
                stream.write(f"{index} {value}\n")
                index += 1
    return index


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", nargs="?", type=int, default=N,
                        help=f"number of antidiagonals (default: {N})")
    args = parser.parse_args()
    if args.N < 1:
        parser.error("N must be at least 1")
    count = write_bfile(args.N)
    print(f"Saved {count} terms to {OUTPUT}")


if __name__ == "__main__":
    main()
