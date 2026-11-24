#!/usr/bin/env python3
"""Compute A400065, the function f(n) in Erdős Problem 360.

f(n) is the least number of classes partitioning {1, ..., n-1} so that n
is not a sum of distinct elements from any one class.  f(1) = 0 uses the
empty partition convention.

Usage: python3 -B 400065_01.py N1 N2 [LIMIT_SECONDS]
Prints n f(n) on stdout; progress and diagnostics go to stderr.
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
import math
import os
import shutil
import subprocess
import sys
import tempfile
import time


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


def main():
    if len(sys.argv) not in (3, 4):
        sys.exit('usage: 400065_01.py N1 N2 [LIMIT_SECONDS]')
    try:
        n1, n2 = int(sys.argv[1]), int(sys.argv[2])
        limit = float(sys.argv[3]) if len(sys.argv) == 4 else 60.0
    except ValueError:
        sys.exit('N1 and N2 must be integers; LIMIT_SECONDS must be a positive number')
    if not 1 <= n1 <= n2 or not math.isfinite(limit) or limit <= 0:
        sys.exit('need 1 <= N1 <= N2 and a finite positive LIMIT_SECONDS')
    if n1 == 1:
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
                r = decide(n, k, d, limit)
                if r is None:
                    print(f'n={n} k={k}: solver or proof check timed out after {limit}s, stopped', file=sys.stderr)
                    sys.exit(2)
                if r:
                    break
                k += 1
            print(n, k, flush=True)
            print(f'n={n} f={k} {time.time() - start:.1f}s', file=sys.stderr, flush=True)


if __name__ == '__main__':
    main()
