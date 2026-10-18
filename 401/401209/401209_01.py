"""Write the first N downward antidiagonals of A401209 to b401209.txt.

A(n,k) counts integers j with n < j <= n+k and greatest prime factor > k.
Order: A(1,1), A(1,2), A(2,1), A(1,3), A(2,2), A(3,1), ...
Antidiagonal d has n+k=d+1 and contains d terms.
The b-file has indices 1..N*(N+1)//2.

Usage: python3 401209_01.py [N]  (default N = 100).
Only the Python standard library and exact integer arithmetic are used.
Time is O(N^2), and working memory is O(N), excluding the output file.
"""

import argparse
from collections.abc import Iterator
from pathlib import Path


N = 100
OUTPUT = Path(__file__).resolve().with_name("b401209.txt")


def greatest_prime_factors(limit: int) -> list[int]:
    """Return the greatest prime factor of each integer 2..limit."""
    factors = [0] * (limit + 1)
    for p in range(2, limit + 1):
        if factors[p] == 0:
            for multiple in range(p, limit + 1, p):
                factors[multiple] = p
    return factors


def antidiagonals(limit: int) -> Iterator[list[int]]:
    """Yield downward antidiagonals 1..limit, with n increasing in each."""
    if limit < 1:
        raise ValueError("N must be at least 1")
    factors = greatest_prime_factors(limit + 1)
    for total in range(2, limit + 2):
        frequencies = [0] * (total + 1)
        diagonal = []
        count = 0
        for k in range(1, total):
            # Old interval: [total-k+2, total]. Raising the threshold
            # from k-1 to k removes precisely the entries with GPF = k.
            count -= frequencies[k]
            # Extend the interval to [total-k+1, total]. Its lower
            # endpoint is n+1, where n=total-k.
            p = factors[total - k + 1]
            frequencies[p] += 1
            if p > k:
                count += 1
            diagonal.append(count)
        # We computed increasing k; downward order requires increasing n.
        diagonal.reverse()
        yield diagonal


def write_bfile(limit: int, output: Path = OUTPUT) -> int:
    """Write N complete antidiagonals, with flattened indices starting at 1."""
    if limit < 1:
        raise ValueError("N must be at least 1")
    index = 1
    with output.open("w", encoding="utf-8") as stream:
        for diagonal in antidiagonals(limit):
            for value in diagonal:
                stream.write(f"{index} {value}\n")
                index += 1
    return index - 1


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
