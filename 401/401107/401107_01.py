"""Write rows n = 2..N of A401107 to b401107.txt, read by rows.

T(n,k) = max{d : 1 <= d <= n and d | binomial(n,k)}, 1 <= k < n.
Usage: python3 401107_01.py [N]   (default N = 100).
The b-file index starts at 1, with index (n-2)*(n-1)//2 + k for T(n,k).
There are N*(N-1)//2 terms through row N.

This standalone script uses exact integer arithmetic and the standard
library only. Symmetry halves the calculation within each row.
"""

import argparse
from collections.abc import Iterator
from pathlib import Path


N = 100
OUTPUT = Path(__file__).resolve().with_name("b401107.txt")


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


def rows(limit: int) -> Iterator[tuple[int, list[int]]]:
    """Yield (n, [T(n,1), ..., T(n,n-1)]) for n = 2..limit."""
    if limit < 2:
        raise ValueError("limit must be at least 2")
    spf, factors, masks, base_tree, leaves = prepare(limit)

    for n in range(2, limit + 1):
        if spf[n] == n:
            yield n, [n] * (n - 1)
            continue

        tree = base_tree.copy()
        exponents = [0] * (limit + 1)
        for p, e in factors[n]:  # binomial(n,1) = n.
            exponents[p] = e
            blocked = masks[p][e] if e < len(masks[p]) else 0
            update(tree, leaves[p], blocked)

        candidates = (1 << (n + 1)) - 2  # Bits 1 through n.
        half = [n]
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
            allowed = candidates & ~tree[1]
            half.append(allowed.bit_length() - 1)

        # For even n, the middle entry k=n/2 occurs only once.
        row = half + (half[::-1] if n % 2 else half[:-1][::-1])
        yield n, row


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", type=int, nargs="?", default=N,
                        help=f"last row n to compute (default: {N})")
    args = parser.parse_args()
    if args.N < 2:
        parser.error("N must be at least 2")

    index = 0
    with OUTPUT.open("w", encoding="utf-8") as output:
        for n, row in rows(args.N):
            for value in row:
                index += 1
                output.write(f"{index} {value}\n")
            if n % 100 == 0 or n == args.N:
                output.flush()
                print(f"Completed row n = {n} ({index} terms)", flush=True)
    assert index == args.N * (args.N - 1) // 2
    print(f"Wrote {index} terms (rows n = 2..{args.N}) to {OUTPUT}")


if __name__ == "__main__":
    main()
