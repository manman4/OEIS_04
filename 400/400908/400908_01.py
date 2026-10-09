"""Generate A400908 for n=4..10000 in b400908_01.txt.

Requires NumPy; uses exact prime valuations and the bound gcd >= 2**i.
AI-assisted research code: understand and verify before submission.
"""
import argparse
from functools import lru_cache
from math import comb, gcd, isqrt
from pathlib import Path
import hashlib
import json
import time
import numpy as np


class Calculator:
    def __init__(self, limit):
        self.limit = limit
        self.spf = list(range(limit + 1))
        for p in range(2, isqrt(limit) + 1):
            if self.spf[p] == p:
                for k in range(p * p, limit + 1, p):
                    if self.spf[k] == k:
                        self.spf[k] = p
        self.indices = np.arange(limit + 1, dtype=np.int32)

    def change_factors(self, factors, k, sign):
        while k > 1:
            p = self.spf[k]
            factors[p] = factors.get(p, 0) + sign
            k //= p

    @lru_cache(maxsize=None)
    def factorial_valuations(self, p):
        values = np.zeros(self.limit + 1, dtype=np.int32)
        power = p
        while power <= self.limit:
            values += self.indices // power
            power *= p
        return values

    def term(self, n):
        factors = {}
        self.change_factors(factors, n, 1)
        best = comb(n, 2)
        witness = (2, 2)
        for i in range(2, n // 2 + 1):
            if (1 << i) >= best:
                break
            self.change_factors(factors, n - i + 1, 1)
            self.change_factors(factors, i, -1)
            factors = {p: e for p, e in factors.items() if e}
            assert all(e > 0 for e in factors.values())
            candidates = np.ones(n // 2 - i + 1, dtype=np.int64)
            for p, e in factors.items():
                f = self.factorial_valuations(p)
                # j=i..floor(n/2); the reversed slice supplies n-j.
                exponents = f[n] - f[i:n // 2 + 1] - f[n - n // 2:n - i + 1][::-1]
                powers = np.array([min(p ** k, best) for k in range(e + 1)], dtype=np.int64)
                multipliers = powers[np.minimum(exponents, e)]
                # Capping preserves every gcd below best. Both operands
                # <= best <= n(n-1)/2, hence product < 2.5e15 for n<=10000.
                np.minimum(candidates * multipliers, best, out=candidates)
            at = int(np.argmin(candidates))
            value = int(candidates[at])
            if value < best:
                best = value
                witness = (i, i + at)
        return best, witness


def integer_check(n, bounded=False):
    coefficients = [1]
    for k in range(1, n // 2 + 1):
        coefficients.append(coefficients[-1] * (n - k + 1) // k)
    best = coefficients[2]
    for i in range(2, n // 2 + 1):
        if bounded and (1 << i) >= best:
            break
        for j in range(i, n // 2 + 1):
            best = min(best, gcd(coefficients[i], coefficients[j]))
    return best


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, default=10000)
    args = parser.parse_args()
    if not 4 <= args.limit <= 10000:
        parser.error('--limit must be in 4..10000 (the int64 safety range)')
    base = Path(__file__).resolve().parent
    output = base / 'b400908_01.txt'
    calculator = Calculator(args.limit)
    reference = {}
    if (base / 'verification.json').exists():
        reference = {r['n']: r['a'] for r in json.loads((base / 'verification.json').read_text())['rows']}
    started = time.perf_counter()
    samples = {511, 512, 1000, 2048, 4096, 5000, 8192, 10000}
    digest = hashlib.sha256()
    with output.open('w') as stream:
        for n in range(4, args.limit + 1):
            value, (i, j) = calculator.term(n)
            if n in reference:
                assert value == reference[n], (n, value, reference[n])
            if n <= 100 or n in samples:
                assert value == integer_check(n, bounded=n > 100), n
            assert 2 <= i <= j <= n // 2
            assert gcd(comb(n, i), comb(n, j)) == value, (n, i, j)
            line = f'{n} {value}\n'
            stream.write(line)
            digest.update(line.encode())
            if n % 1000 == 0:
                stream.flush()
                print(f'n={n}: a(n)={value}, {time.perf_counter()-started:.1f}s', flush=True)
    print(f'Created {output.name}: {args.limit - 3} rows, n=4..{args.limit}')
    print(f'SHA-256: {digest.hexdigest()}')


if __name__ == '__main__':
    main()
