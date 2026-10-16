"""Write rows n = 2..N of A401140 to b401140.txt.

S(n) = {j*(n-j): 1 <= j <= floor(n/2)}.
T(n,k) = len(S(n) intersect S(k)), for 1 <= k < n.

Usage: python3 401140_01.py [N]   (default N = 100).
Rows are flattened in increasing n, then increasing k.
The b-file index starts at 2, as in the earlier triangle A401107:
index(T(n,k)) = 1 + (n-2)*(n-1)//2 + k.
There are N*(N-1)//2 terms through row N.

Only Python's standard library and exact integer arithmetic are used.
Sets from earlier rows are retained to avoid recomputing them.
"""

import argparse
from collections.abc import Iterator
from pathlib import Path


N = 100
OUTPUT = Path(__file__).resolve().with_name("b401140.txt")


def rows(limit: int) -> Iterator[tuple[int, list[int]]]:
    """Yield (n, [T(n,1), ..., T(n,n-1)]) for n = 2..limit."""
    if limit < 2:
        raise ValueError("N must be at least 2")
    sets: list[set[int]] = [set(), set()]
    for n in range(2, limit + 1):
        current = {j * (n - j) for j in range(1, n // 2 + 1)}
        row = [len(current.intersection(sets[k])) for k in range(1, n)]
        sets.append(current)
        yield n, row


def write_bfile(limit: int, output: Path = OUTPUT) -> int:
    """Write the flattened triangle and return the number of terms."""
    index = 2
    with output.open("w", encoding="utf-8") as stream:
        for n, row in rows(limit):
            for value in row:
                stream.write(f"{index} {value}\n")
                index += 1
            if n % 100 == 0 or n == limit:
                print(f"Completed row {n}: {index - 2} terms", flush=True)
    return index - 2


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", nargs="?", type=int, default=N,
                        help=f"last row to write (default: {N})")
    args = parser.parse_args()
    if args.N < 2:
        parser.error("N must be at least 2")
    count = write_bfile(args.N)
    print(f"Saved {count} terms to {OUTPUT}")


if __name__ == "__main__":
    main()
