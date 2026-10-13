"""Compute A401013 for n = 1..10000 and write b401013.txt.

a(n) is the maximum number of distinct prime divisors of n+k greater
than k, over all integers k >= 0.

For k >= n there is at most one such prime divisor, and the value 1
is always attainable. Thus only n <= n+k < 2*n needs to be considered.
All calculations use exact Python integers and the standard library only.
"""

from heapq import heappop, heappush
from pathlib import Path


LIMIT = 10000
OUTPUT = Path(__file__).resolve().with_name("b401013.txt")


def sequence(limit: int) -> list[int]:
    """Return a(1), ..., a(limit) using prime-divisor intervals."""
    if limit < 1:
        raise ValueError("limit must be at least 1")

    bound = 2 * limit - 1
    prime_divisors: list[list[int]] = [[] for _ in range(bound + 1)]
    for p in range(2, bound + 1):
        if not prime_divisors[p]:
            for m in range(p, bound + 1, p):
                prime_divisors[m].append(p)

    # Fix m = n+k and let p be its j-th largest distinct prime divisor.
    # At least j prime divisors exceed k iff m-p+1 <= n <= m.
    # Record these intervals for j >= 2; the baseline value is 1.
    starts: list[list[tuple[int, int]]] = [[] for _ in range(limit + 1)]
    for m in range(2, bound + 1):
        right = min(m, limit)
        for j, p in enumerate(reversed(prime_divisors[m]), 1):
            if j < 2:
                continue
            left = max(1, m - p + 1)
            if left <= right:
                starts[left].append((-j, right))

    # Negative counts make the smallest heap entry the largest count.
    active: list[tuple[int, int]] = []
    values = []
    for n in range(1, limit + 1):
        for interval in starts[n]:
            heappush(active, interval)
        while active and active[0][1] < n:
            heappop(active)
        values.append(-active[0][0] if active else 1)
    return values


def main() -> None:
    values = sequence(LIMIT)
    OUTPUT.write_text(
        "".join(f"{n} {value}\n" for n, value in enumerate(values, 1)),
        encoding="utf-8",
    )
    print(f"Wrote {len(values)} terms (n = 1..{LIMIT}) to {OUTPUT}")


if __name__ == "__main__":
    main()
