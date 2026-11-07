"""A401834: largest subset with at most two representations per product.

Representations use two distinct elements x < y. Python 3.10+ on POSIX is required.
Each completed optimum is saved to b401834.txt beside this program, unless
--output is supplied. Existing rows are recomputed and checked on each run.
Only Python's standard library is used. No published values are search bounds.
"""

import argparse
from collections import defaultdict
from contextlib import contextmanager
import fcntl
from functools import lru_cache
from itertools import combinations
import os
from pathlib import Path
import stat
import sys
import tempfile
import time

MAX_N = 200
CACHE_SIZE = 20000


def add_conflicts(n, representations, conflicts):
    """Add each forbidden union of three equal-product pairs exactly once."""
    for a in range(1, n):
        pair = (1 << (a - 1)) | (1 << (n - 1))
        ways = representations[a * n]
        for first, second in combinations(ways, 2):
            mask = pair | first | second
            if mask.bit_count() != 6:
                raise ValueError("Equal-product pairs must be disjoint")
            conflicts.add(mask)
        ways.append(pair)


def minimum_deletions(n, conflicts, previous):
    """previous is a proved minimum deletion set for {1,...,n-1}.

    Deletion minima cannot decrease on extending the universe, and deleting
    the new vertex as well is always sufficient. Thus only the old optimum
    budget needs to be tested. Each conflict must lose at least one vertex.
    """
    if previous < 0 or previous >> (n - 1):
        raise ValueError("Invalid previous deletion set")
    edges = sorted(conflicts)
    vertices = []
    incident = [0] * n
    for index, edge in enumerate(edges):
        remaining = edge
        row = []
        while remaining:
            bit = remaining & -remaining
            vertex = bit.bit_length() - 1
            row.append(vertex)
            incident[vertex] |= 1 << index
            remaining ^= bit
        vertices.append(row)

    active = (1 << len(edges)) - 1
    uncovered = active
    remaining = previous
    while remaining:
        bit = remaining & -remaining
        uncovered &= ~incident[bit.bit_length() - 1]
        remaining ^= bit
    if not uncovered:
        return previous

    @lru_cache(maxsize=CACHE_SIZE)
    def cover(pending, budget):
        if not pending:
            return 0
        if not budget:
            return None
        first = (pending & -pending).bit_length() - 1
        choices = sorted(
            ((pending & incident[v], v) for v in vertices[first]),
            key=lambda item: (-item[0].bit_count(), item[1]),
        )
        undominated = []
        for covered, vertex in choices:
            if covered == pending:
                return 1 << vertex
            # If another vertex covers a superset, it can replace this one.
            if not any(covered & ~other == 0 for other, _ in undominated):
                undominated.append((covered, vertex))
        if budget == 1:
            return None

        # Pairwise vertex-disjoint conflicts need different deleted vertices.
        packing = pending
        packed = 0
        while packing:
            index = (packing & -packing).bit_length() - 1
            packed += 1
            if packed > budget:
                return None
            touching = 0
            for vertex in vertices[index]:
                touching |= incident[vertex]
            packing &= ~touching

        for covered, vertex in undominated:
            rest = cover(pending & ~covered, budget - 1)
            if rest is not None:
                return rest | (1 << vertex)
        return None

    try:
        answer = cover(active, previous.bit_count())
    finally:
        cover.cache_clear()
    if answer is None:
        answer = previous | (1 << (n - 1))
    if answer.bit_count() not in (previous.bit_count(), previous.bit_count() + 1):
        raise ValueError("Invalid deletion optimum")
    if any(not edge & answer for edge in edges):
        raise ValueError("Deletion witness leaves a forbidden product")
    return answer


def check_witness(n, deleted):
    """Recount products independently of the conflict and incidence model."""
    if deleted < 0 or deleted >> n:
        raise ValueError("Invalid deletion witness")
    selected = [a for a in range(1, n + 1) if not deleted & (1 << (a - 1))]
    counts = defaultdict(int)
    for a, b in combinations(selected, 2):
        counts[a * b] += 1
        if counts[a * b] > 2:
            raise ValueError("Witness has three representations of one product")
    return len(selected)


@contextmanager
def output_lock(path):
    fd = os.open(str(path) + ".lock", os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW | os.O_NONBLOCK, 0o600)
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
            raise ValueError("Output lock must be a regular file with one link")
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise RuntimeError("Another process is using the output file") from error
        yield
    finally:
        os.close(fd)


def load_values(path):
    try:
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    except FileNotFoundError:
        return []
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
            raise ValueError("Output must be a regular file with one link")
        stream = os.fdopen(fd, "r", encoding="ascii", newline="")
        fd = -1
        values = []
        with stream:
            while True:
                line = stream.readline(128)
                if not line:
                    break
                index = len(values) + 1
                fields = line.split()
                if index > MAX_N or not line.endswith("\n") or len(fields) != 2:
                    raise ValueError("Malformed or incomplete saved row")
                if not all(field.isascii() and field.isdecimal() for field in fields):
                    raise ValueError("Saved rows must contain decimal integers")
                row, value = map(int, fields)
                previous = values[-1] if values else 0
                if row != index or not 1 <= value <= index or not previous <= value <= previous + 1:
                    raise ValueError("Invalid saved index or value")
                values.append(value)
        return values
    finally:
        if fd >= 0:
            os.close(fd)


def save_values(path, values):
    try:
        info = path.lstat()
    except FileNotFoundError:
        pass
    else:
        if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
            raise ValueError("Refusing to replace a linked or nonregular output")
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="ascii", newline="\n") as stream:
            for n, value in enumerate(values, 1):
                stream.write(f"{n} {value}\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        Path(temporary).unlink(missing_ok=True)


def positive_limit(text):
    if not text.isascii() or not text.isdecimal() or len(text) > 3:
        raise argparse.ArgumentTypeError(f"n must be an integer from 1 to {MAX_N}")
    value = int(text)
    if not 1 <= value <= MAX_N:
        raise argparse.ArgumentTypeError(f"n must be an integer from 1 to {MAX_N}")
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=positive_limit, help=f"compute n=1..N, up to {MAX_N}")
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().with_name("b401834.txt"))
    args = parser.parse_args()
    try:
        if not args.output.name or args.output.name in (".", ".."):
            raise ValueError("Output must name a file")
        path = args.output.parent.resolve(strict=True) / args.output.name
        with output_lock(path):
            saved = load_values(path)
            if saved:
                print(f"Rechecking saved n=1..{min(args.n, len(saved))}...", flush=True)
            representations = defaultdict(list)
            conflicts = set()
            previous = 0
            values = []
            for n in range(1, args.n + 1):
                started = time.monotonic()
                add_conflicts(n, representations, conflicts)
                previous = minimum_deletions(n, conflicts, previous)
                value = check_witness(n, previous)
                if n <= len(saved) and value != saved[n - 1]:
                    raise ValueError(f"Saved value at n={n} is incorrect")
                values.append(value)
                if n > len(saved):
                    save_values(path, values)
                    print(f"{n} {value} ({time.monotonic() - started:.3f}s)", flush=True)
    except KeyboardInterrupt:
        print("Interrupted; completed rows remain saved.", file=sys.stderr)
        return 130
    except (OSError, ValueError, RuntimeError, MemoryError) as error:
        print(f"Stopped: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
