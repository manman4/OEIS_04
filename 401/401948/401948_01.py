"""Count line-size sets of planar point configurations and save a b-file."""

import argparse
import fcntl
from math import isqrt
import os
from pathlib import Path
from tempfile import NamedTemporaryFile


def profile_counts(limit):
    """Return the counts for point-set sizes 1 through limit."""
    first_possible = [0] * (limit + 1)
    partitions = [1] + [0] * limit

    # m counts the positive contributions to the minimum point count.
    for m in range(1, isqrt(limit) + 1):
        base = m * m
        # Count partitions of the excess into parts at most m.
        for excess in range(m, limit - base + 1):
            partitions[excess] += partitions[excess - m]
        if m == 1:
            continue

        weight = 1 << max(0, m - 3)
        if m >= 3:
            for cost in range(base, limit + 1):
                first_possible[cost] += weight * partitions[cost - base]
        # Raising all m entries by one gives the additional completions.
        shifted = base + m
        for cost in range(shifted, limit + 1):
            first_possible[cost] += weight * partitions[cost - shifted]

    total = 0
    result = []
    for n in range(1, limit + 1):
        total += first_possible[n]
        # All collinear, plus {2} and {2,k} (3 <= k < n) when n >= 3.
        result.append(max(1, n - 1) + total)
    return result


def save_bfile(path, values):
    """Atomically save the results, preserving any longer matching file."""
    # The directory is a stable lock target even when the output is replaced.
    directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        fcntl.flock(directory, fcntl.LOCK_EX)
        if path.is_symlink() or (path.exists() and not path.is_file()):
            raise ValueError(f"{path.name} must be a regular file")

        saved = 0
        if path.exists():
            with path.open(encoding="ascii") as existing:
                for saved, line in enumerate(existing, 1):
                    if saved > len(values):
                        return False
                    if line.split() != [str(saved), str(values[saved - 1])]:
                        raise ValueError(f"{path.name} differs at line {saved}")
        if saved == len(values):
            return False

        temporary = None
        try:
            with NamedTemporaryFile(
                mode="w", encoding="ascii", newline="\n", dir=path.parent,
                prefix=f".{path.stem}-", suffix=".txt", delete=False,
            ) as stream:
                temporary = Path(stream.name)
                for index, value in enumerate(values, 1):
                    stream.write(f"{index} {value}\n")
                stream.flush()
                os.fsync(stream.fileno())
            temporary.replace(path)
        finally:
            if temporary is not None:
                temporary.unlink(missing_ok=True)
        return True
    finally:
        os.close(directory)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", nargs="?", type=int, default=100, help="last index (default: 100)")
    args = parser.parse_args()
    if args.n < 1:
        parser.error("n must be positive")

    path = Path(__file__).resolve().with_name("b401948_01.txt")
    values = profile_counts(args.n)
    try:
        written = save_bfile(path, values)
    except (OSError, ValueError) as error:
        parser.exit(1, f"Error: {error}\n")
    if written:
        print(f"Saved n=1..{args.n} to {path.name}")
    else:
        print(f"Kept existing {path.name} (already covers n=1..{args.n})")


if __name__ == "__main__":
    main()
