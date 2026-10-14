"""Compute A401022 for n = 1..10000 and write b401022.txt.

a(n) is the largest 3-smooth divisor of n*(n+1).
All calculations use exact Python integers and the standard library only.
"""

from pathlib import Path


LIMIT = 10000
OUTPUT = Path(__file__).resolve().with_name("b401022.txt")


def term(n: int) -> int:
    """Extract all factors of 2 and 3 from n*(n+1)."""
    if n < 1:
        raise ValueError("n must be at least 1")
    remaining = n * (n + 1)
    result = 1
    for prime in (2, 3):
        while remaining % prime == 0:
            remaining //= prime
            result *= prime
    return result


def sequence(limit: int) -> list[int]:
    """Return a(1), ..., a(limit)."""
    if limit < 1:
        raise ValueError("limit must be at least 1")
    return [term(n) for n in range(1, limit + 1)]


def main() -> None:
    values = sequence(LIMIT)
    OUTPUT.write_text(
        "".join(f"{n} {value}\n" for n, value in enumerate(values, 1)),
        encoding="utf-8",
    )
    print(f"Wrote {len(values)} terms (n = 1..{LIMIT}) to {OUTPUT}")


if __name__ == "__main__":
    main()
