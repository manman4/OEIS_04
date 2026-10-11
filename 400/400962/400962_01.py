"""Compute A400962 for n = 2..10000 and write b400962.txt.

a(n) = min_{1 <= k < n} max_{p prime} v_p(binomial(n, k)).
All calculations use exact Python integers and the standard library only.
"""

from math import isqrt
from pathlib import Path


LIMIT = 10000
OUTPUT = Path(__file__).resolve().with_name("b400962.txt")


def factorizations(limit: int) -> list[tuple[tuple[int, int], ...]]:
    """Precompute the prime factorizations of all integers up to limit."""
    spf = list(range(limit + 1))
    for p in range(2, isqrt(limit) + 1):
        if spf[p] == p:
            for m in range(p * p, limit + 1, p):
                if spf[m] == m:
                    spf[m] = p
    result: list[tuple[tuple[int, int], ...]] = [()] * (limit + 1)
    for n in range(2, limit + 1):
        factors = []
        m = n
        while m > 1:
            p = spf[m]
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            factors.append((p, e))
        result[n] = tuple(factors)
    return result


def term(n: int, factors: list[tuple[tuple[int, int], ...]]) -> int:
    """Track the prime exponents of successive binomial coefficients."""
    exponents = dict(factors[n])  # binomial(n, 1) = n.
    best = max(exponents.values())
    if best == 1:
        return 1  # Every internal binomial coefficient is an integer > 1.

    # histogram[e] counts primes currently having the positive exponent e.
    histogram: dict[int, int] = {}
    for e in exponents.values():
        histogram[e] = histogram.get(e, 0) + 1

    def update(m: int, sign: int) -> None:
        for p, e in factors[m]:
            old = exponents.get(p, 0)
            new = old + sign * e
            assert new >= 0
            if old:
                histogram[old] -= 1
                if histogram[old] == 0:
                    del histogram[old]
            if new:
                exponents[p] = new
                histogram[new] = histogram.get(new, 0) + 1
            else:
                exponents.pop(p, None)

    # Symmetry binomial(n,k) = binomial(n,n-k) halves the search.
    for k in range(2, n // 2 + 1):
        # binomial(n,k) = binomial(n,k-1) * (n-k+1) / k.
        update(n - k + 1, 1)
        update(k, -1)
        best = min(best, max(histogram))
        if best == 1:
            break
    return best


def sequence(limit: int) -> list[int]:
    """Return a(2), ..., a(limit)."""
    factors = factorizations(limit)
    return [term(n, factors) for n in range(2, limit + 1)]


def main() -> None:
    values = sequence(LIMIT)
    OUTPUT.write_text(
        "".join(f"{n} {value}\n" for n, value in enumerate(values, 2)),
        encoding="ascii",
    )
    print(f"Saved {len(values)} terms to {OUTPUT.name}")


if __name__ == "__main__":
    main()
