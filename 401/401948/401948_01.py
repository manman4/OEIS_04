"""Count line-size sets of planar point configurations."""

from itertools import count
import sys


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


if __name__ == "__main__":
    if len(sys.argv) > 2:
        raise SystemExit("Usage: count-profiles.py [positive limit]")
    limit = int(sys.argv[1]) if len(sys.argv) == 2 else 100
    if limit < 1:
        raise SystemExit("The limit must be positive.")
    print(", ".join(map(str, profile_counts(limit))))
