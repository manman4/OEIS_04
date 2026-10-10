"""Compute A400930 for n = 1..10000 and write b400930.txt.

The length counts distinct prime divisors. The empty sequence gives a(1) = 0.
All calculations use exact Python integer arithmetic.
"""

from pathlib import Path


LIMIT = 10000
OUTPUT = Path(__file__).resolve().with_name("b400930.txt")


def sequence(limit: int) -> list[int]:
    """Return a(1), ..., a(limit) using longest-path dynamic programming."""
    prime_divisors: list[list[int]] = [[] for _ in range(limit + 1)]
    for p in range(2, limit + 1):
        if prime_divisors[p]:
            continue  # A smaller prime divides p, so p is composite.
        for n in range(p, limit + 1, p):
            prime_divisors[n].append(p)

    values = []
    for n in range(1, limit + 1):
        ps = prime_divisors[n]  # Distinct primes, in increasing order.
        lengths = [1] * len(ps)
        for j, p in enumerate(ps):
            for i in range(j):
                if (p - 1) % ps[i] == 0:
                    lengths[j] = max(lengths[j], lengths[i] + 1)
        values.append(max(lengths, default=0))
    return values


def main() -> None:
    values = sequence(LIMIT)
    OUTPUT.write_text(
        "".join(f"{n} {value}\n" for n, value in enumerate(values, 1)),
        encoding="ascii",
    )
    print(f"Saved {len(values)} terms to {OUTPUT.name}")


if __name__ == "__main__":
    main()
