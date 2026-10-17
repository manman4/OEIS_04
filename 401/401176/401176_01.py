"""Write A401176 for n = 0..10000 to b401176.txt.

a(n) = n - min_{k > n, k composite} (k - spf(k)).
Usage: python3 401176_01.py [limit]   (default limit = 10000).

For n >= 2 the next even integer gives a minimum <= n. For composite
k > 2*n, k - spf(k) >= k/2 > n. Thus k <= 2*n suffices.
For n = 0 or 1 the minimum is 2, attained at k = 4.
A single backwards scan through k <= max(4, 2*limit) computes all
required minima. All arithmetic is exact; standard library only.
"""

import argparse
from math import isqrt
from pathlib import Path


LIMIT = 10000
OUTPUT = Path(__file__).resolve().with_name("b401176.txt")


def sequence(limit: int) -> list[int]:
    """Return a(0), ..., a(limit), including a(0) = -2 and a(1) = -1."""
    if limit < 0:
        raise ValueError("limit must be nonnegative")
    bound = max(4, 2 * limit)
    spf = list(range(bound + 1))
    for p in range(2, isqrt(bound) + 1):
        if spf[p] == p:
            for k in range(p * p, bound + 1, p):
                if spf[k] == k:
                    spf[k] = p

    values = [0] * (limit + 1)
    best = bound
    for k in range(bound, 0, -1):
        if spf[k] < k:  # Composite; skip primes.
            best = min(best, k - spf[k])
        n = k - 1  # best now covers composite integers strictly greater than n.
        if 0 <= n <= limit:
            values[n] = n - best
    return values


def write_bfile(limit: int = LIMIT, output: Path = OUTPUT) -> int:
    values = sequence(limit)
    with output.open("w", encoding="utf-8") as stream:
        for n, value in enumerate(values):
            stream.write(f"{n} {value}\n")
    return len(values)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("limit", nargs="?", type=int, default=LIMIT,
                        help=f"largest n (default: {LIMIT})")
    args = parser.parse_args()
    if args.limit < 0:
        parser.error("limit must be nonnegative")
    count = write_bfile(args.limit)
    print(f"Saved {count} terms (n = 0..{args.limit}) to {OUTPUT}")


if __name__ == "__main__":
    main()
