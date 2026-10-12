"""Compute A400986 for n = 2..10000 and write b400986.txt.

a(n) = max_{1 <= k < n} (k + tau(k)) - n,
where tau(k) is the number of positive divisors of k.
All calculations use exact Python integers and the standard library only.
"""

from pathlib import Path


LIMIT = 10000
OUTPUT = Path(__file__).resolve().with_name("b400986.txt")


def sequence(limit: int) -> list[int]:
    """Return a(2), ..., a(limit) using a divisor-count sieve."""
    if limit < 2:
        raise ValueError("limit must be at least 2")

    # Only k < limit is needed to compute a(limit).
    tau = [0] * limit
    for divisor in range(1, limit):
        for multiple in range(divisor, limit, divisor):
            tau[multiple] += 1

    values = []
    maximum = 0
    for n in range(2, limit + 1):
        k = n - 1
        maximum = max(maximum, k + tau[k])
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
