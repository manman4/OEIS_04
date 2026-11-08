#!/usr/bin/env python3
"""Compute A401886 for n = 1..N (default N=10000).

Definition: maximize |S| for S subset of {1,...,n} such that x*y is
not squarefree for every x,y in S, including x=y. The empty set is allowed.

The affirmative result in https://www.erdosproblems.com/844 gives an
extremal set: all even numbers and all odd non-squarefree numbers <= n.
Thus a(n) = n - #{odd squarefree numbers <= n}. This independently written
implementation marks odd multiples of odd squares using integer arithmetic.

Output is published atomically without overwriting any existing path.
There is no checkpoint, resume mode, persistent lock, or external dependency.
"""

import argparse
from math import isqrt
import os
from pathlib import Path
import sys
import tempfile


MAX_N = 10_000


def terms(limit: int) -> list[int]:
    """Return the exact maximum sizes for 1 <= n <= limit."""
    if type(limit) is not int or not 1 <= limit <= MAX_N:
        raise ValueError(f"N must be an integer in 1..{MAX_N}")
    odd_nonsquarefree = bytearray(limit + 1)
    # Every non-squarefree odd integer has an odd square divisor d*d, d>=3.
    for d in range(3, isqrt(limit) + 1, 2):
        square = d * d
        for multiple in range(square, limit + 1, 2 * square):
            odd_nonsquarefree[multiple] = 1
    result = []
    size = 0
    for n in range(1, limit + 1):
        if n % 2 == 0 or odd_nonsquarefree[n]:
            size += 1
        result.append(size)
    return result


def write_b_file(output: Path, values: list[int]) -> None:
    """Publish a complete file, failing if output already exists (also a link)."""
    output = Path(output)
    fd, temporary_name = tempfile.mkstemp(
        prefix=f".{output.name}.", suffix=".tmp", dir=output.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(fd, "w", encoding="ascii", newline="\n") as stream:
            for n, value in enumerate(values, 1):
                stream.write(f"{n} {value}\n")
            stream.flush()
            os.fsync(stream.fileno())
        # Same-directory hard-link publication is atomic and never replaces
        # an existing file or symlink. Concurrent writers cannot overwrite.
        os.link(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", nargs="?", type=int, default=MAX_N,
                        help=f"last n, 1..{MAX_N} (default: {MAX_N})")
    parser.add_argument("-o", "--output", type=Path,
                        default=Path(__file__).with_name("b401886.txt"),
                        help="output path (default: b401886.txt beside this script)")
    args = parser.parse_args()
    try:
        values = terms(args.N)
        write_b_file(args.output, values)
    except FileExistsError:
        parser.error("output already exists; choose a new --output path; nothing was overwritten")
    except (OSError, ValueError) as error:
        parser.error(str(error))
    print(f"Saved n=1..{args.N} to {args.output}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
