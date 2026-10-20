"""Write A401291 for n = 1..N to b401291.txt.

a(n) is the maximum possible smallest part in a partition of n into
3-smooth positive integers, no part dividing another. A one-part
partition is allowed.

Usage: python3 401291_01.py [N]  (default N = 10000).
The output file is saved beside this script, with indices starting at 1.
Only Python's standard library and exact integer arithmetic are used.
"""

import argparse
from pathlib import Path


N = 10000
OUTPUT = Path(__file__).resolve().with_name("b401291.txt")


def sequence(limit: int) -> list[int]:
    """Return [a(1), ..., a(limit)] by enumerating admissible partitions."""
    if limit < 1:
        raise ValueError("N must be at least 1")

    powers_of_three = []
    power = 1
    while power <= limit:
        powers_of_three.append(power)
        power *= 3

    best = [0] * (limit + 1)

    def visit(min_a: int, max_b: int, total: int, smallest: int) -> None:
        # Write each part as 2^a * 3^b. No part divides another exactly
        # when, after sorting by a, the a's strictly increase and the b's
        # strictly decrease. Thus each admissible partition is visited once.
        remaining = limit - total
        a = min_a
        power_of_two = 1 << a
        while power_of_two <= remaining:
            for b in range(max_b + 1):
                part = power_of_two * powers_of_three[b]
                if part > remaining:
                    break
                new_total = total + part
                new_smallest = min(smallest, part)
                if new_smallest > best[new_total]:
                    best[new_total] = new_smallest
                # There is no smaller nonnegative exponent after b = 0.
                if b > 0:
                    visit(a + 1, b - 1, new_total, new_smallest)
            a += 1
            power_of_two <<= 1

    visit(0, len(powers_of_three) - 1, 0, limit)
    return best[1:]


def write_bfile(limit: int, output: Path = OUTPUT) -> int:
    """Write indices 1..limit and return the number of terms written."""
    values = sequence(limit)
    with output.open("w", encoding="utf-8") as stream:
        for n, value in enumerate(values, start=1):
            stream.write(f"{n} {value}\n")
    return len(values)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", nargs="?", type=int, default=N,
                        help=f"last index to write (default: {N})")
    args = parser.parse_args()
    if args.N < 1:
        parser.error("N must be at least 1")
    count = write_bfile(args.N)
    print(f"Saved {count} terms to {OUTPUT}")


if __name__ == "__main__":
    main()
