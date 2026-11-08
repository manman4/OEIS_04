#!/usr/bin/env python3
"""Compute A401886 by testing integers individually (default N=10000).

Count positive integers k <= n that are even or not squarefree. By the
affirmative result in https://www.erdosproblems.com/844, this count equals
the maximum size in A401886's extremal definition, including x=y.

Unlike 401886_01.py, this calculation uses no sieve or saved sequence data.
Each odd integer is factored by trial division, stopping as soon as a
repeated prime factor is found. It does not directly search all subsets.

Output is published atomically without overwriting any existing path.
Only the Python standard library is required.
"""

import argparse
import os
from pathlib import Path
import sys
import tempfile


MAX_N = 10_000


def _odd_has_square_factor(n: int) -> bool:
    """Test a positive odd integer by trial division and factor removal."""
    remaining = n
    divisor = 3
    while divisor * divisor <= remaining:
        if remaining % divisor == 0:
            remaining //= divisor
            # If the same factor divides again, its square divides n.
            if remaining % divisor == 0:
                return True
        divisor += 2
    # Any remaining factor is prime and occurs once.
    return False


def terms(limit: int) -> list[int]:
    """Return cumulative counts for 1 <= n <= limit, without a sieve."""
    if type(limit) is not int or not 1 <= limit <= MAX_N:
        raise ValueError(f"N must be an integer in 1..{MAX_N}")
    result = []
    total = 0
    for n in range(1, limit + 1):
        if n % 2 == 0 or _odd_has_square_factor(n):
            total += 1
        result.append(total)
    return result


def write_b_file(output: Path, values: list[int]) -> None:
    """Publish a complete file without replacing an existing file or link."""
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
        # Atomic publication at a new name; concurrent writers cannot replace.
        os.link(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", nargs="?", type=int, default=MAX_N,
                        help=f"last n, 1..{MAX_N} (default: {MAX_N})")
    parser.add_argument("-o", "--output", type=Path,
                        default=Path(__file__).with_name("b401886_02.txt"),
                        help="output path (default: b401886_02.txt beside this script)")
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
