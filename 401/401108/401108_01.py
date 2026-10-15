"""Compute A401108 for n = 2..10000 and write b401108.txt.

a(n) = min_{1 <= k < n} max{d : 1 <= d <= n and d | binomial(n,k)}.

Symmetry permits restricting k to 1..floor(n/2). Prime exponents of
successive binomial coefficients are updated exactly. Integer bit masks
and an OR segment tree track which potential divisors are excluded.
Only the Python standard library is required; no floating point is used.
"""

from collections.abc import Iterator
from pathlib import Path


LIMIT = 10000
OUTPUT = Path(__file__).resolve().with_name("b401108.txt")


def prepare(limit: int):
    """Precompute factorizations and masks for prime-power multiples."""
    spf = list(range(limit + 1))
    primes = []
    for p in range(2, limit + 1):
        if spf[p] == p:
            primes.append(p)
            for m in range(p * p, limit + 1, p):
                if spf[m] == m:
                    spf[m] = p

    factors: list[list[tuple[int, int]]] = [[] for _ in range(limit + 1)]
    for m in range(2, limit + 1):
        remainder = m
        while remainder > 1:
            p = spf[remainder]
            exponent = 0
            while remainder % p == 0:
                remainder //= p
                exponent += 1
            factors[m].append((p, exponent))

    # masks[p][e] marks d divisible by p^(e+1). Such a d cannot divide
    # a binomial coefficient whose p-adic valuation is e.
    masks: dict[int, list[int]] = {}
    for p in primes:
        powers = []
        power = p
        while power <= limit:
            mask = 0
            for d in range(power, limit + 1, power):
                mask |= 1 << d
            powers.append(mask)
            power *= p
        masks[p] = powers

    size = 1
    while size < len(primes):
        size *= 2
    base_tree = [0] * (2 * size)
    leaves = [0] * (limit + 1)
    for i, p in enumerate(primes):
        leaves[p] = size + i
        base_tree[size + i] = masks[p][0]
    for i in range(size - 1, 0, -1):
        base_tree[i] = base_tree[2 * i] | base_tree[2 * i + 1]
    return spf, factors, masks, base_tree, leaves


def update(tree: list[int], leaf: int, mask: int) -> None:
    """Replace a leaf and update its ancestors until their OR is unchanged."""
    if tree[leaf] == mask:
        return
    tree[leaf] = mask
    i = leaf // 2
    while i:
        merged = tree[2 * i] | tree[2 * i + 1]
        if tree[i] == merged:
            break
        tree[i] = merged
        i //= 2


def terms(limit: int) -> Iterator[tuple[int, int]]:
    """Yield (n, a(n)) for n = 2..limit."""
    if limit < 2:
        raise ValueError("limit must be at least 2")
    spf, factors, masks, base_tree, leaves = prepare(limit)

    for n in range(2, limit + 1):
        # All internal binomial coefficients for prime n are divisible by n.
        if spf[n] == n:
            yield n, n
            continue

        tree = base_tree.copy()
        exponents = [0] * (limit + 1)
        for p, e in factors[n]:  # binomial(n,1) = n.
            exponents[p] = e
            blocked = masks[p][e] if e < len(masks[p]) else 0
            update(tree, leaves[p], blocked)

        # Bit d represents the candidate divisor d. Bit 0 is excluded.
        candidates = (1 << (n + 1)) - 2
        best = n
        for k in range(2, n // 2 + 1):
            # binomial(n,k) = binomial(n,k-1) * (n-k+1) / k.
            changes = dict(factors[n - k + 1])
            for p, e in factors[k]:
                changes[p] = changes.get(p, 0) - e
            for p, delta in changes.items():
                if delta == 0:
                    continue
                e = exponents[p] + delta
                assert e >= 0
                exponents[p] = e
                blocked = masks[p][e] if e < len(masks[p]) else 0
                update(tree, leaves[p], blocked)

            # The root marks exactly those d that fail some prime condition.
            allowed = candidates & ~tree[1]
            largest_divisor = allowed.bit_length() - 1
            best = min(best, largest_divisor)
        yield n, best


def sequence(limit: int) -> list[int]:
    """Return a(2), ..., a(limit)."""
    return [value for _, value in terms(limit)]


def main() -> None:
    with OUTPUT.open("w", encoding="utf-8") as output:
        for n, value in terms(LIMIT):
            output.write(f"{n} {value}\n")
            if n % 100 == 0 or n == LIMIT:
                output.flush()
                print(f"n = {n}: a(n) = {value}", flush=True)
    print(f"Wrote {LIMIT - 1} terms (n = 2..{LIMIT}) to {OUTPUT}")


if __name__ == "__main__":
    main()
