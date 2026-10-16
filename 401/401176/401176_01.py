"""Write A401176 for n = 2..10000 to b401176.txt.

a(n) = n - min_{k > n, k composite} (k - spf(k)).
Usage: python3 401176_01.py [limit]   (default limit = 10000).

For n >= 2 the next even integer gives a minimum <= n. For composite
k > 2*n, k - spf(k) >= k/2 > n. Thus k <= 2*n suffices.
For all n <= limit, a single backwards scan through k <= 2*limit
computes the required minima. All arithmetic is exact; standard library only.
"""

import argparse
from math import isqrt
from pathlib import Path


LIMIT = 10000
OUTPUT = Path(__file__).resolve().with_name("b401176.txt")


def sequence(limit: int) -> list[int]:
    """Return a(2), ..., a(limit), with no entries for n = 0 or 1."""
    if limit < 2:
        raise ValueError("limit must be at least 2")
    bound = 2 * limit
    spf = list(range(bound + 1))
    for p in range(2, isqrt(bound) + 1):
        if spf[p] == p:
            for k in range(p * p, bound + 1, p):
                if spf[k] == k:
                    spf[k] = p

    values = [0] * (limit - 1)
    best = bound
    for k in range(bound, 2, -1):
        if spf[k] < k:  # Composite; skip primes.
            best = min(best, k - spf[k])
        n = k - 1  # best now covers composite integers strictly greater than n.
        if 2 <= n <= limit:
            values[n - 2] = n - best
    return values


def write_bfile(limit: int = LIMIT, output: Path = OUTPUT) -> int:
    values = sequence(limit)
    with output.open("w", encoding="utf-8") as stream:
        for n, value in enumerate(values, 2):
            stream.write(f"{n} {value}\n")
    return len(values)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("limit", nargs="?", type=int, default=LIMIT,
                        help=f"largest n (default: {LIMIT})")
    args = parser.parse_args()
    if args.limit < 2:
        parser.error("limit must be at least 2")
    count = write_bfile(args.limit)
    print(f"Saved {count} terms (n = 2..{args.limit}) to {OUTPUT}")


if __name__ == "__main__":
    main()
