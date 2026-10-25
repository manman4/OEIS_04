"""Compute A401450 for n = 1..10000 and write b401450.txt.

Maximum number of square partial products of a strictly increasing
sequence of positive integers not exceeding n.

The empty product is not counted. The factor 1 is allowed, so a(1) = 1.
Only the Python standard library and exact integer arithmetic are used.
The output file is saved beside this script.
"""

from math import isqrt
from pathlib import Path


LIMIT = 10000
OUTPUT = Path(__file__).resolve().with_name("b401450.txt")


def sequence(limit: int) -> list[int]:
    """Return a(1), ..., a(limit) using prime-exponent parity vectors.

    Between consecutive square partial products, the selected factors have
    square product. Scan until the first nonempty subset with square product
    exists, then start a new block. Any competing first block ends no earlier,
    so replacing it by this earliest block leaves all later blocks available.
    Repeating this exchange proves that the greedy count is maximal.

    A subset has square product exactly when its parity vectors XOR to zero.
    A binary linear basis detects this without enumerating subsets.
    """
    if limit < 1:
        raise ValueError("limit must be at least 1")

    # Sieve the smallest prime factor of every integer up to limit.
    spf = list(range(limit + 1))
    for p in range(2, isqrt(limit) + 1):
        if spf[p] == p:
            for multiple in range(p * p, limit + 1, p):
                if spf[multiple] == multiple:
                    spf[multiple] = p

    # One bit per prime; a set bit means that its exponent is odd.
    primes = (p for p in range(2, limit + 1) if spf[p] == p)
    prime_bits = {p: 1 << i for i, p in enumerate(primes)}
    masks = [0] * (limit + 1)

    basis: dict[int, int] = {}
    values = []
    count = 0
    for n in range(1, limit + 1):
        if n > 1:
            p = spf[n]
            masks[n] = masks[n // p] ^ prime_bits[p]
        vector = masks[n]

        # Reduce against the basis for the interval since the last cut.
        while vector:
            pivot = vector.bit_length() - 1
            previous = basis.get(pivot)
            if previous is None:
                basis[pivot] = vector
                break
            vector ^= previous

        if vector == 0:
            # A square-product subset is available: finish this block.
            count += 1
            basis.clear()
        values.append(count)

    return values


def write_bfile(limit: int, output: Path = OUTPUT) -> int:
    """Write a(n) with consecutive indices n = 1..limit."""
    values = sequence(limit)
    with output.open("w", encoding="utf-8") as stream:
        stream.writelines(
            f"{n} {value}\n" for n, value in enumerate(values, 1)
        )
    return len(values)


def main() -> None:
    count = write_bfile(LIMIT)
    print(f"Wrote {count} terms (n = 1..{LIMIT}) to {OUTPUT}")


if __name__ == "__main__":
    main()
