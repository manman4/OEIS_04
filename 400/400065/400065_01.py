#!/usr/bin/env python3
"""Compute A400065, the function f(n) in Erdős Problem 360.

f(n) is the least number of classes partitioning {1, ..., n-1} so that n
is not a sum of distinct elements from any one class.  f(1) = 0 uses the
empty partition convention.

Usage: python3 -B 400065_01.py N1 N2 [LIMIT_SECONDS]
Prints n f(n) on stdout; progress and diagnostics go to stderr.
Also writes b400065.txt next to this script, committing each completed
term atomically. Existing output files are never overwritten. Select a
different file with --output FILE, or disable saving with --no-bfile.
This is a fresh computation, not a checkpoint/resume implementation.
A stable .lock file is used for exclusion on macOS/Linux and may remain
after a run; its presence alone does not mean a process is running.
Requires CaDiCaL (cadical on PATH) and the formally verified LRAT proof
checker cake_lpr (CAKE_LPR, PATH, or ~/.local/bin/cake_lpr).
LIMIT_SECONDS defaults to 60 per solver or proof-checker invocation.
A timeout stops with exit status 2; unresolved terms are not printed.
Temporary CNF and proof files are removed automatically.

The CNF gives each element at least one colour and excludes, in each
colour, every set of distinct elements whose sum is n.  A solution with
several colours assigned to one element can be reduced to one colour
without violating a clause.  Fixing element 1 to colour 0 loses no
colouring because colours may be renamed.  Partitions are enumerated
exactly; the test p*(p+1)//2 < rem skips only branches whose remaining
possible distinct parts cannot reach rem.

The minimum k is found by testing 1, 2, ... independently for every n.
No saved values or monotonicity assumption are used.  SAT colourings are
checked from their subset sums.  UNSAT answers require a verified LRAT
proof for the exact CNF used by the solver.

Execution copy of the existing independent implementation of Erdős
Problem 360; no solver or checker source
code is bundled here.
"""
import argparse
import fcntl
import math
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path


def distinct_partitions(n):
    """Sets of distinct parts in [1, n-1] with sum n, as increasing tuples."""
    out = []

    def go(rem, mx, cur):
        if rem == 0:
            out.append(tuple(reversed(cur)))
            return
        for p in range(min(rem, mx), 0, -1):
            if p * (p + 1) // 2 < rem:
                break   # parts < = p distinct cannot reach rem
            cur.append(p)
            go(rem - p, p - 1, cur)
            cur.pop()
    go(n, n - 1, [])
    return out


def colouring_ok(n, col, k):
    for c in range(k):
        sums = 1
        for i in range(1, n):
            if col[i] == c:
                sums |= sums << i
        if sums >> n & 1:
            return False
    return True


def build(n, k):
    """The CNF for (n, k): (number of variables, clauses, var)."""
    var = lambda i, c: (i - 1) * k + c + 1
    clauses = [[var(i, c) for c in range(k)] for i in range(1, n)]
    clauses.append([var(1, 0)])
    for P in distinct_partitions(n):
        for c in range(k):
            clauses.append([-var(i, c) for i in P])
    return (n - 1) * k, clauses, var


def decide(n, k, d, limit):
    _, clauses, var = build(n, k)
    path, prf = os.path.join(d, 'f.cnf'), os.path.join(d, 'f.lrat')
    with open(path, 'w') as f:
        f.write(f'p cnf {(n - 1) * k} {len(clauses)}\n')
        f.writelines(' '.join(map(str, c)) + ' 0\n' for c in clauses)
    try:
        res = subprocess.run(['cadical', '-q', '--lrat', '--binary=false', path, prf],
                             capture_output=True, text=True, timeout=limit)
    except subprocess.TimeoutExpired:
        return None
    if res.returncode == 10:
        model = {int(x) for line in res.stdout.splitlines() if line.startswith('v')
                 for x in line.split()[1:] if int(x) > 0}
        col = [None] + [min(c for c in range(k) if var(i, c) in model) for i in range(1, n)]
        if not colouring_ok(n, col, k):
            sys.exit(f'n={n}, k={k}: invalid colouring; stopped')
        return True
    if res.returncode == 20:
        checker = os.environ.get('CAKE_LPR') or shutil.which('cake_lpr') or os.path.expanduser('~/.local/bin/cake_lpr')
        try:
            checked = subprocess.run([checker, path, prf], capture_output=True,
                                     text=True, timeout=limit)
        except subprocess.TimeoutExpired:
            return None
        except OSError:
            sys.exit('cake_lpr is required (set CAKE_LPR or add it to PATH)')
        if checked.returncode != 0 or 's VERIFIED UNSAT' not in checked.stdout.splitlines():
            sys.exit(f'n={n}, k={k}: LRAT proof rejected by cake_lpr')
        return False
    sys.exit(f'cadical exit {res.returncode}')



class BFileWriter:
    """Write a new, consecutive b-file; keep the previous version on failure."""

    def __init__(self, path, start):
        self.path = path
        self.start = start
        self.rows = []
        self.lock = None

    def __enter__(self):
        if self.path is None:
            return self
        if not self.path.parent.is_dir():
            raise ValueError('the output directory does not exist')
        lock_path = self.path.with_name(self.path.name + '.lock')
        flags = os.O_CREAT | os.O_RDWR | getattr(os, 'O_NOFOLLOW', 0)
        self.lock = os.fdopen(os.open(lock_path, flags, 0o600), 'a+')
        try:
            fcntl.flock(self.lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            self.lock.close()
            self.lock = None
            raise ValueError('another process is using this output file') from None
        if self.path.exists() or self.path.is_symlink():
            self.lock.close()
            self.lock = None
            raise ValueError('the b-file already exists; choose --output FILE or --no-bfile')
        return self

    def __exit__(self, *_):
        if self.lock is not None:
            self.lock.close()
            self.lock = None

    def append(self, n, value):
        if self.path is None:
            return
        if self.lock is None:
            raise RuntimeError('the output lock is not held')
        if n != self.start + len(self.rows):
            raise ValueError('b-file indices must be consecutive and increasing')
        if (n == 1 and value != 0) or (n >= 2 and not 1 <= value <= n - 1):
            raise ValueError('value outside the range allowed by the definition')
        next_rows = self.rows + [(n, value)]
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(
                mode='w', encoding='ascii', newline='\n',
                prefix='.' + self.path.name + '.', suffix='.tmp',
                dir=self.path.parent, delete=False,
            ) as f:
                temporary = Path(f.name)
                for index, term in next_rows:
                    f.write(f'{index} {term}\n')
                f.flush()
                os.fsync(f.fileno())
            os.replace(temporary, self.path)
            self.rows = next_rows
        finally:
            if temporary is not None:
                temporary.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n1', type=int)
    parser.add_argument('n2', type=int)
    parser.add_argument('limit', nargs='?', type=float, default=60.0,
                        metavar='LIMIT_SECONDS')
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--output', type=Path, metavar='FILE')
    group.add_argument('--no-bfile', action='store_true')
    args = parser.parse_args()
    n1, n2, limit = args.n1, args.n2, args.limit
    if not 1 <= n1 <= n2 or not math.isfinite(limit) or limit <= 0:
        parser.error('need 1 <= N1 <= N2 and a finite positive LIMIT_SECONDS')
    output = None if args.no_bfile else (
        args.output.absolute() if args.output is not None
        else Path(__file__).resolve().with_name('b400065.txt'))
    with BFileWriter(output, n1) as writer:
        if n1 == 1:
            writer.append(1, 0)
            print('1 0', flush=True)
        if n2 == 1:
            return
        if shutil.which('cadical') is None:
            sys.exit('cadical is required on PATH')
        with tempfile.TemporaryDirectory() as d:
            for n in range(max(n1, 2), n2 + 1):
                start = time.time()
                k = 1
                while True:
                    result = decide(n, k, d, limit)
                    if result is None:
                        print(f'n={n} k={k}: solver or proof check timed out after {limit}s, stopped',
                              file=sys.stderr, flush=True)
                        sys.exit(2)
                    if result:
                        break
                    k += 1
                writer.append(n, k)
                print(n, k, flush=True)
                print(f'n={n} f={k} {time.time() - start:.1f}s', file=sys.stderr, flush=True)


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        print('Interrupted; completed b-file terms are preserved.', file=sys.stderr)
        sys.exit(130)
    except (OSError, ValueError) as error:
        print(f'Error: {error}', file=sys.stderr)
        sys.exit(1)
