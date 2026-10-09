#!/usr/bin/env python3
"""Write k with k and k+2 in U(1,2), in increasing order (A400867).

Run from the desired output directory:
    python3 400867_01.py

Only the Python standard library is required. The default output contains
indices 1 through 10000. Existing output is recomputed and checked before
replacement; interrupted runs leave the previous output intact.

Exact representation counting: at candidate x, bit j of forward indicates
j in U, and bit j of reflected indicates x-j in U. Hence the population
count of their intersection counts ordered representations x=u+v. Remove
the diagonal u=v (if present), then exactly two ordered representations
means exactly one unordered representation with distinct summands.
Advancing x shifts reflected left by one; accepting x adds bit x to
forward and bit 0 to reflected. No conjectural pruning is used.
"""

import argparse
import fcntl
import os
from pathlib import Path
import sys
import tempfile


def terms(count):
    """Yield the first count lower members, including 1 and 2."""
    forward = (1 << 1) | (1 << 2)
    reflected = (1 << 2) | (1 << 1)  # Reflected about candidate x=3.
    members = {1, 2}
    found = 0
    x = 3
    while found < count:
        representations = (forward & reflected).bit_count()
        diagonal = x % 2 == 0 and x // 2 in members
        if representations - int(diagonal) == 2:
            forward |= 1 << x
            reflected |= 1
            members.add(x)
            # All possible smaller lower members have already been decided.
            if x - 2 in members:
                found += 1
                yield x - 2
        reflected <<= 1
        x += 1


def read_existing(path):
    """Validate consecutive indices and strictly increasing positive terms."""
    if not path.exists():
        return []
    values = []
    for line_number, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        fields = line.split()
        if len(fields) != 2:
            raise ValueError(f"{path}:{line_number}: expected index and value")
        index, value = map(int, fields)
        if index != len(values) + 1 or value <= (values[-1] if values else 0):
            raise ValueError(f"{path}:{line_number}: invalid index or order")
        values.append(value)
    return values


def write_bfile(path, count):
    existing = read_existing(path)
    if len(existing) > count:
        raise ValueError("Existing output has more terms than requested; use another output path")
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", encoding="ascii", dir=path.parent,
            prefix=path.name + ".", suffix=".tmp", delete=False,
        ) as stream:
            temporary = Path(stream.name)
            for index, value in enumerate(terms(count), 1):
                if index <= len(existing) and value != existing[index - 1]:
                    raise ValueError(f"Existing output disagrees at index {index}")
                stream.write(f"{index} {value}\n")
                if index % 1000 == 0 or index == count:
                    print(f"n={index}, a(n)={value}", file=sys.stderr)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        temporary = None
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--terms", type=int, default=10000)
    parser.add_argument("--output", type=Path, default=Path("b400867_01.txt"))
    args = parser.parse_args()
    if args.terms < 1:
        parser.error("--terms must be positive")
    try:
        # Serialize invocations of this script, including atomic replacement.
        # Locking the source avoids persistent auxiliary lock files.
        with Path(__file__).open("rb") as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                raise ValueError("Another invocation of this script is running") from None
            write_bfile(args.output, args.terms)
        print(f"Wrote {args.terms} terms to {args.output}", file=sys.stderr)
    except (OSError, ValueError) as error:
        print(f"Error: {error}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("Interrupted; previous output preserved.", file=sys.stderr)
        return 130
    return 0


if __name__ == "__main__":
    sys.exit(main())
