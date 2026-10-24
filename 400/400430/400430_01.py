"""Compute A400430 for n = 2..10000 and write b400430.txt.

a(n) = max_{1 <= k < n} (k + omega(k)) - n,
where omega(k) is the number of distinct prime divisors of k.
All calculations use exact Python integers and the standard library only.
"""

from pathlib import Path


LIMIT = 10000
OUTPUT = Path(__file__).resolve().with_name("b400430.txt")


def sequence(limit: int) -> list[int]:
    """Return a(2), ..., a(limit) using a distinct-prime-factor sieve."""
    if limit < 2:
        raise ValueError("limit must be at least 2")

    # Only k < limit is needed to compute a(limit).
    omega = [0] * limit
    for p in range(2, limit):
        if omega[p] == 0:
            # Each prime contributes once, regardless of its multiplicity.
            for multiple in range(p, limit, p):
                omega[multiple] += 1

    values = []
    maximum = 0
    for n in range(2, limit + 1):
        k = n - 1
        maximum = max(maximum, k + omega[k])
        values.append(maximum - n)
    return values


def main() -> None:
    values = sequence(LIMIT)
    OUTPUT.write_text(
        "".join(f"{n} {value}\n" for n, value in enumerate(values, 2)),
        encoding="utf-8",
    )
    print(f"Wrote {len(values)} terms (n = 2..{LIMIT}) to {OUTPUT}")


if __name__ == "__main__":
    main()
