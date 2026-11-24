#!/usr/bin/env python3
"""A402485: partitions with greatest part > least part * number of parts.

Usage (Python 3, standard library only; macOS/Linux):
    python3 402485_01.py
    python3 402485_01.py --max-n 100 --output /tmp/b402485_test.txt
    python3 402485_01.py --self-test

The default output is b402485_01.txt beside this script, for 1 <= n <= 10000.
Input definition, generating function and 50 reference terms: supplied by the
user. No OEIS connection is made.

Derivation (formal power series, so all coefficient sums are finite):
Write D_s = product_{k=1..s}(1-x^k), D_0 = 1, and P = 1/D_infinity.
In the supplied generating function, expand the numerator product by subsets
of size r. The sum of x^(sum of the selected indices) for r indices in 1..i
is x^(r(r+1)/2) D_i/(D_r D_{i-r}). To see this, subtract 1,...,r from
the increasing selected indices: the result is a partition in an r by (i-r)
rectangle. Its generating polynomial is D_i/(D_r D_{i-r}); this identity
also follows inductively by including/excluding the last selected index.
Consequently, putting t = i-r, the original generating function becomes

  F = sum_{r,j>=1} (-1)^(r+1) x^A / D_r
                      * sum_{t>=0} x^(j(r+1)t) / D_t,
  A = j*(r*(r+1)+1) + r*(r+1)//2.

For every d>=1, sum_{t>=0} x^(dt)/D_t = product_{k>=d}(1-x^k)^(-1):
the left counts partitions with exactly t parts >=d (subtract d from each
part), and the right counts the same partitions by part multiplicities.
With d=j(r+1), this proves the finite-product form used here:

  F = P * H,
  H = sum_{r,j>=1} (-1)^(r+1) x^A
                         * product_{k=r+1..j(r+1)-1}(1-x^k).

The product is empty for j=1. All its exponents are nonnegative. Therefore
only A<=N contributes through degree N, and each product needs degrees at
most N-A. For fixed r, A increases with j, so discarding higher degrees
cannot affect any later summand. Factors with k>N-A cannot affect it either.
Finally Euler's identity D_infinity = 1 + sum_{k>=1} (-1)^k
(x^(k(3k-1)/2)+x^(k(3k+1)/2)) gives F from H in O(N sqrt(N)) additions.
No floating point, probabilistic arithmetic, or partition enumeration is
used for the main calculation. Memory use is O(N) arbitrary-size integers.

Saving: lock the canonical output path before reading, recompute the complete
range, compare every existing row, then atomically replace the output. A
longer existing prefix is retained, including when --max-n is smaller.
An interrupted computation leaves the previous b-file intact; rerun to
recompute. There is no checkpoint. The stable empty .lock file is retained.
Progress/diagnostics go to stderr; stdout is unused.
"""

from __future__ import annotations

import argparse
import fcntl
import os
from pathlib import Path
import sys
import tempfile
import time
from contextlib import contextmanager


REFERENCE = (
    0, 0, 0, 1, 1, 2, 4, 6, 8, 12, 17, 24, 33, 44, 58, 79, 102, 133,
    173, 222, 283, 363, 458, 577, 723, 903, 1123, 1395, 1722, 2121,
    2605, 3192, 3892, 4742, 5753, 6971, 8421, 10153, 12208, 14660,
    17555, 20990, 25043, 29828, 35451, 42080, 49846, 58964, 69627, 82104,
)


def compute(max_n: int, *, progress: bool = False) -> list[int]:
    """Return exact a(0)..a(max_n); a(0)=0 is an internal convention."""
    if type(max_n) is not int or max_n < 0:
        raise ValueError("max_n must be a nonnegative integer")
    h = [0] * (max_n + 1)
    r = 1
    last_report = time.monotonic()
    while True:
        twice_tri = r * (r + 1)
        tri = twice_tri // 2
        step = twice_tri + 1
        j_max = (max_n - tri) // step
        if j_max < 1:
            break
        sign = 1 if r % 2 else -1
        coeff = [1] + [0] * (max_n - step - tri)
        old_end = r
        for j in range(1, j_max + 1):
            shift = j * step + tri
            limit = max_n - shift
            del coeff[limit + 1:]
            end = j * (r + 1) - 1
            for k in range(old_end + 1, min(end, limit) + 1):
                for n in range(limit, k - 1, -1):
                    coeff[n] -= coeff[n - k]
            old_end = end
            if sign == 1:
                for n, value in enumerate(coeff):
                    h[shift + n] += value
            else:
                for n, value in enumerate(coeff):
                    h[shift + n] -= value
            now = time.monotonic()
            if progress and now - last_report >= 5:
                print(f"finite products: r={r}, j={j}/{j_max}",
                      file=sys.stderr, flush=True)
                last_report = now
        r += 1

    pentagonal = []
    k = 1
    while k * (3 * k - 1) // 2 <= max_n:
        recurrence_sign = 1 if k % 2 else -1
        for g in (k * (3 * k - 1) // 2, k * (3 * k + 1) // 2):
            if g <= max_n:
                pentagonal.append((g, recurrence_sign))
        k += 1
    a = [0] * (max_n + 1)
    for n in range(max_n + 1):
        value = h[n]
        for g, recurrence_sign in pentagonal:
            if g > n:
                break
            value += recurrence_sign * a[n - g]
        if value < 0:
            raise ArithmeticError(f"negative coefficient at n={n}")
        a[n] = value
    count = min(max_n, len(REFERENCE))
    if tuple(a[1:count + 1]) != REFERENCE[:count]:
        raise ArithmeticError("reference terms do not match")
    return a


def direct_count(n: int) -> int:
    """Independent small oracle: enumerate every partition, without pruning."""
    def visit(remaining: int, lower: int, least: int, greatest: int,
              length: int) -> int:
        if remaining == 0:
            return int(length > 0 and greatest > least * length)
        total = 0
        for part in range(lower, remaining + 1):
            total += visit(remaining - part, part, least or part, part,
                           length + 1)
        return total

    return visit(n, 1, 0, 0, 0)


def self_test() -> None:
    a = compute(50)
    for n in range(36):
        expected = direct_count(n)
        if a[n] != expected:
            raise ArithmeticError(f"direct enumeration mismatch at n={n}")
    print("Self-test passed: direct enumeration n=0..35; supplied terms n=1..50.",
          file=sys.stderr)


@contextmanager
def output_lock(path: Path):
    with path.with_name(path.name + ".lock").open("a", encoding="ascii") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise RuntimeError("another process holds the output lock") from exc
        try:
            yield
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


def read_existing(path: Path) -> list[int]:
    if not path.exists():
        return []
    values = []
    with path.open(encoding="ascii") as source:
        for line_number, line in enumerate(source, 1):
            fields = line.split()
            if len(fields) != 2 or any(not field.isdecimal() for field in fields):
                raise ValueError(f"invalid b-file row at line {line_number}")
            n, value = map(int, fields)
            if n != len(values) + 1:
                raise ValueError(f"out-of-order b-file row at line {line_number}")
            values.append(value)
    return values


def atomic_write(path: Path, values: list[int]) -> None:
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", encoding="ascii", newline="\n", dir=path.parent,
            prefix=path.name + ".", suffix=".tmp", delete=False,
        ) as target:
            temporary = Path(target.name)
            for n in range(1, len(values)):
                target.write(f"{n} {values[n]}\n")
            target.flush()
            os.fsync(target.fileno())
        os.replace(temporary, path)
        temporary = None
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def save(max_n: int, output: Path) -> None:
    if type(max_n) is not int or max_n < 1:
        raise ValueError("max_n must be a positive integer")
    output = output.resolve()
    started = time.monotonic()
    with output_lock(output):
        existing = read_existing(output)
        limit = max(max_n, len(existing))
        print(f"Computing A402485 for n=1..{limit}.", file=sys.stderr, flush=True)
        values = compute(limit, progress=True)
        if values[1:len(existing) + 1] != existing:
            raise ValueError("existing b-file differs; output left unchanged")
        atomic_write(output, values)
    print(f"Saved {limit} rows to {output.name} "
          f"({time.monotonic() - started:.2f} s).", file=sys.stderr)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-n", type=int, default=10000)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("b402485_01.txt"))
    parser.add_argument("--self-test", action="store_true",
                        help="run small independent checks without writing a b-file")
    args = parser.parse_args()
    try:
        if args.self_test:
            self_test()
        else:
            save(args.max_n, args.output)
    except (OSError, ValueError, ArithmeticError, RuntimeError) as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("Interrupted; no partial b-file was written.", file=sys.stderr)
        return 130
    return 0


if __name__ == "__main__":
    sys.exit(main())
