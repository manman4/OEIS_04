"""Write A401252 for n = 1..N to b401252.txt.

a(n) counts pairs of coprime positive integers i < j < n with
sigma(i) = sigma(j), where sigma is the sum-of-divisors function.

Usage: python3 401252_01.py [N]  (default N = 10000).
The output file is saved beside this script, with indices starting at 1.
Only Python's standard library and exact integer arithmetic are used.
"""

import argparse
from math import gcd
from pathlib import Path


N = 10000
OUTPUT = Path(__file__).resolve().with_name("b401252.txt")


def sequence(limit: int) -> list[int]:
    """Return [a(1), ..., a(limit)], counting each unordered pair once."""
    if limit < 1:
        raise ValueError("N must be at least 1")

    # Only j < limit is needed. Compute sigma(j) by summing divisors.
    sigma = [0] * limit
    for divisor in range(1, limit):
        for multiple in range(divisor, limit, divisor):
            sigma[multiple] += divisor

    groups: dict[int, list[int]] = {}
    values = [0] * limit
    count = 0
    for j in range(1, limit):
        earlier = groups.setdefault(sigma[j], [])
        # Each i in this group has i < j and sigma(i) = sigma(j).
        count += sum(gcd(i, j) == 1 for i in earlier)
        earlier.append(j)
        # The new pairs have larger member j, hence first appear at n=j+1.
        values[j] = count
    return values


def write_bfile(limit: int, output: Path = OUTPUT) -> int:
    """Write indices 1..limit and return the number of terms written."""
    values = sequence(limit)
    with output.open("w", encoding="utf-8") as stream:
        for n, value in enumerate(values, start=1):
            stream.write(f"{n} {value}\n")
    return len(values)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", nargs="?", type=int, default=N,
                        help=f"last index to write (default: {N})")
    args = parser.parse_args()
    if args.N < 1:
        parser.error("N must be at least 1")
    count = write_bfile(args.N)
    print(f"Saved {count} terms to {OUTPUT}")


if __name__ == "__main__":
    main()
