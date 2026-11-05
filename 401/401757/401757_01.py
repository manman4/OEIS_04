#!/usr/bin/env python3
"""Compute the first positive shift of each initial squarefree pattern."""

import argparse
from math import isqrt
import os
from pathlib import Path
import sys
import tempfile


BLOCK_SIZE = 10_000_000


def squarefree_flags(lo, hi, primes):
    """Return one byte per integer in the inclusive interval [lo, hi]."""
    size = hi - lo + 1
    flags = bytearray(b'\x01') * size
    for p in primes:
        square = p * p
        if square > hi:
            break
        offset = (-lo) % square
        if offset < size:
            flags[offset::square] = bytes((size - 1 - offset) // square + 1)
    return flags


def compute(count, max_shift, block_size=BLOCK_SIZE):
    """Return all requested terms, or the exact prefix found within max_shift."""
    if min(count, max_shift, block_size) < 1:
        raise ValueError('count, max_shift and block_size must be positive')
    limit = isqrt(max_shift + count)
    sieve = bytearray(b'\x01') * (limit + 1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((limit - p*p) // p + 1)
    primes = [p for p in range(2, limit + 1) if sieve[p]]
    pattern = squarefree_flags(1, count, primes)
    terms = []
    for first in range(1, max_shift + 1, block_size):
        size = min(block_size, max_shift - first + 1)
        # Include enough integers after the last start to compare a full pattern.
        flags = squarefree_flags(first + 1, first + size + count - 1, primes)
        pos = 0
        while len(terms) < count:
            n = len(terms) + 1
            pos = flags.find(pattern[:n], pos)
            if pos < 0 or pos >= size:
                break
            terms.append(first + pos)
            # A longer match must also match the shorter prefix, so the
            # next search can start at the same shift.
        if len(terms) == count:
            break
    return terms


def save_new(path, terms):
    """Publish a complete file atomically, or accept an identical file."""
    data = ''.join(f'{n} {t}\n' for n, t in enumerate(terms, 1)).encode('ascii')
    fd, name = tempfile.mkstemp(dir=path.parent, prefix=f'.{path.name}.', suffix='.tmp')
    temporary = Path(name)
    try:
        with os.fdopen(fd, 'wb') as out:
            out.write(data)
            out.flush()
            os.fsync(out.fileno())
        try:
            os.link(temporary, path)
        except FileExistsError:
            if (path.is_symlink() or not path.is_file()
                    or path.stat().st_size != len(data) or path.read_bytes() != data):
                raise ValueError(f'{path.name} already exists with different contents') from None
    finally:
        temporary.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int, nargs='?', default=200)
    parser.add_argument('--max-shift', type=int, default=4_000_000_000)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('b401757.txt'))
    args = parser.parse_args()
    if args.n < 1 or args.max_shift < 1:
        parser.error('n and --max-shift must be positive')
    try:
        terms = compute(args.n, args.max_shift)
        if len(terms) != args.n:
            print(f'Within t <= {args.max_shift}, reached n={len(terms)} of {args.n}.',
                  file=sys.stderr)
            return 1
        save_new(args.output, terms)
    except (OSError, ValueError) as error:
        print(error, file=sys.stderr)
        return 1
    print(f'{args.output.name}: n=1..{len(terms)}, last term {terms[-1]}', file=sys.stderr)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
