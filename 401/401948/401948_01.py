"""Count line-size sets of planar point configurations and save a b-file."""

import argparse
import fcntl
from itertools import count
import os
from pathlib import Path
from tempfile import NamedTemporaryFile


def profile_counts(limit):
    """Return the counts for point-set sizes 1 through limit."""
    first_possible = [0] * (limit + 1)

    # At least two distinct line sizes of at least 3.
    for length in count(2):
        if sum(max(0, 2*i + 2 - length) for i in range(1, length + 1)) > limit:
            break

        # ending[size][cost] counts prefixes with the indicated last size.
        ending = [[0] * (limit + 1) for _ in range(limit + 1)]
        ending[2][0] = 1
        for i in range(1, length + 1):
            next_ending = [[0] * (limit + 1) for _ in range(limit + 1)]
            smaller = [0] * (limit + 1)
            for size in range(3, limit + 1):
                for cost, number in enumerate(ending[size - 1]):
                    smaller[cost] += number
                extra = max(0, size + i - length)
                for cost in range(limit + 1 - extra):
                    next_ending[size][cost + extra] = smaller[cost]
            ending = next_ending

        for row in ending:
            for cost, number in enumerate(row):
                first_possible[cost] += number

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
