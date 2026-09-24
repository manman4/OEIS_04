#!/usr/bin/env python3
"""Compute A400112 with Graphillion.

A400112 counts self-avoiding lattice paths from (0, 0) to (n, n) in
the n by n square whose consecutive maximal straight segments have
different lengths.

The Graphillion universe is the undirected square grid.  GraphSet.paths()
constructs all simple paths between the two corners.  We then exclude every
path containing a forbidden pattern: two perpendicular length-k arms meeting
at a bend, with each outer endpoint either a terminal or forced to be another
bend.  Since every internal vertex of a simple terminal-to-terminal path has
degree two, these forced outer bends make both arms maximal straight segments.

Examples (after activating an environment containing Graphillion):

    python3 400112_01.py 6
    python3 400112_01.py --start 5 7
    python3 400112_01.py --self-test

Normal results are written to stdout in b-file format.  Progress and
self-test diagnostics are written to stderr.
"""

from __future__ import annotations

import argparse
import sys
from collections.abc import Iterable, Iterator, Sequence
from typing import Any


Vertex = tuple[int, int]
Edge = tuple[Vertex, Vertex]
Pattern = frozenset[Edge]

START: Vertex = (0, 0)
HORIZONTAL_DIRECTIONS: tuple[Vertex, ...] = ((-1, 0), (1, 0))
VERTICAL_DIRECTIONS: tuple[Vertex, ...] = ((0, -1), (0, 1))
ALL_DIRECTIONS: tuple[Vertex, ...] = (
    (1, 0),
    (0, 1),
    (-1, 0),
    (0, -1),
)

# Used only by --self-test, never by the counting algorithm.
KNOWN_PREFIX = (1, 0, 4, 20, 266, 6080, 343354)


def add(vertex: Vertex, direction: Vertex, scale: int = 1) -> Vertex:
    """Translate ``vertex`` by ``scale * direction``."""

    return (
        vertex[0] + scale * direction[0],
        vertex[1] + scale * direction[1],
    )


def inside(vertex: Vertex, n: int) -> bool:
    """Return whether ``vertex`` lies in the (n+1) by (n+1) vertex grid."""

    x, y = vertex
    return 0 <= x <= n and 0 <= y <= n


def edge(first: Vertex, second: Vertex) -> Edge:
    """Return a canonical representation of an undirected edge."""

    if first == second:
        raise ValueError("a grid edge cannot be a loop")
    return (first, second) if first < second else (second, first)


def grid_universe(n: int) -> list[Edge]:
    """Return all nearest-neighbor edges of the n by n square grid.

    The as-is order has a small row frontier and is available through
    ``--traversal as-is``.  Graphillion's default greedy traversal may reorder
    these edges further.
    """

    universe: list[Edge] = []
    for y in range(n + 1):
        for x in range(n + 1):
            here = (x, y)
            if x < n:
                universe.append(edge(here, (x + 1, y)))
            if y < n:
                universe.append(edge(here, (x, y + 1)))
    return universe


def arm_edges(bend: Vertex, direction: Vertex, length: int) -> list[Edge]:
    """Return the edges from ``bend`` for ``length`` steps in ``direction``."""

    result: list[Edge] = []
    here = bend
    for _ in range(length):
        there = add(here, direction)
        result.append(edge(here, there))
        here = there
    return result


def outer_turn_options(
    endpoint: Vertex,
    arm_is_horizontal: bool,
    n: int,
    terminals: frozenset[Vertex],
) -> list[tuple[Edge, ...]]:
    """Return edge choices that make an arm endpoint maximal.

    A terminal needs no extra edge.  At any other endpoint, one perpendicular
    incident edge is required.  In a simple s-t path this edge and the arm edge
    exhaust degree two, so the path must turn at the endpoint.
    """

    if endpoint in terminals:
        return [()]

    perpendicular = (
        VERTICAL_DIRECTIONS if arm_is_horizontal else HORIZONTAL_DIRECTIONS
    )
    options = []
    for direction in perpendicular:
        neighbor = add(endpoint, direction)
        if inside(neighbor, n):
            options.append((edge(endpoint, neighbor),))
    return options


def forbidden_patterns(n: int) -> list[Pattern]:
    """Construct all subgraphs witnessing equal consecutive segment lengths.

    Each geometric L is generated once by choosing one horizontal and one
    vertical arm.  The path may traverse the L in either direction; Graphillion
    stores undirected edge sets, and equality of the two lengths is symmetric.
    """

    if n < 0:
        raise ValueError("n must be nonnegative")
    if n == 0:
        return []

    goal = (n, n)
    terminals = frozenset((START, goal))
    patterns: set[Pattern] = set()

    for y in range(n + 1):
        for x in range(n + 1):
            bend = (x, y)
            for horizontal in HORIZONTAL_DIRECTIONS:
                for vertical in VERTICAL_DIRECTIONS:
                    for length in range(1, n + 1):
                        horizontal_end = add(bend, horizontal, length)
                        vertical_end = add(bend, vertical, length)
                        if not (
                            inside(horizontal_end, n)
                            and inside(vertical_end, n)
                        ):
                            continue

                        arms = arm_edges(bend, horizontal, length)
                        arms.extend(arm_edges(bend, vertical, length))
                        horizontal_outer = outer_turn_options(
                            horizontal_end,
                            arm_is_horizontal=True,
                            n=n,
                            terminals=terminals,
                        )
                        vertical_outer = outer_turn_options(
                            vertical_end,
                            arm_is_horizontal=False,
                            n=n,
                            terminals=terminals,
                        )
                        for first in horizontal_outer:
                            for second in vertical_outer:
                                patterns.add(frozenset((*arms, *first, *second)))

    return sorted(patterns, key=lambda pattern: (len(pattern), sorted(pattern)))


def load_graphillion() -> tuple[Any, Any]:
    """Import Graphillion lazily so --self-test works without the package."""

    try:
        from graphillion import GraphSet, Universe
    except ImportError as error:
        raise RuntimeError(
            "Graphillion is required for counting. Activate the Anaconda "
            "environment containing it, or run: pip install graphillion"
        ) from error
    return GraphSet, Universe


def count_graphillion(
    n: int,
    *,
    traversal: str = "greedy",
    progress: bool = True,
) -> int:
    """Return a(n) using Graphillion's ZDD representation."""

    if n < 0:
        raise ValueError("n must be nonnegative")
    if n == 0:
        return 1

    GraphSet, Universe = load_graphillion()
    goal = (n, n)
    universe = grid_universe(n)
    patterns = forbidden_patterns(n)

    if progress:
        print(
            f"n={n}: {len(universe)} grid edges, "
            f"{len(patterns)} forbidden patterns",
            file=sys.stderr,
            flush=True,
        )

    Universe.set_universe(
        universe,
        traversal=traversal,
        source=START if traversal != "as-is" else None,
    )
    if progress:
        print(f"n={n}: constructing all simple paths", file=sys.stderr, flush=True)
    paths = GraphSet.paths(START, goal)

    # GraphSet.excluding(GraphSet) keeps graphs containing none of the operand's
    # graphs.  Thus all forbidden patterns are filtered in one ZDD operation;
    # no individual self-avoiding path is enumerated in Python.
    forbidden = GraphSet([sorted(pattern) for pattern in patterns])
    if progress:
        print(f"n={n}: excluding forbidden patterns", file=sys.stderr, flush=True)
    valid_paths = paths.excluding(forbidden)
    return valid_paths.len()


def path_edges(path: Sequence[Vertex]) -> Pattern:
    """Convert a vertex path to its undirected edge set."""

    return frozenset(edge(first, second) for first, second in zip(path, path[1:]))


def valid_by_definition(path: Sequence[Vertex]) -> bool:
    """Test the segment-length condition directly from an ordered path."""

    if len(path) <= 1:
        return True

    previous_length: int | None = None
    current_direction = (
        path[1][0] - path[0][0],
        path[1][1] - path[0][1],
    )
    current_length = 1

    for first, second in zip(path[1:], path[2:]):
        direction = (second[0] - first[0], second[1] - first[1])
        if direction == current_direction:
            current_length += 1
            continue
        if previous_length == current_length:
            return False
        previous_length = current_length
        current_direction = direction
        current_length = 1

    return previous_length != current_length


def simple_paths(n: int) -> Iterator[tuple[Vertex, ...]]:
    """Enumerate all simple corner-to-corner paths for small-test use only."""

    if n < 0:
        raise ValueError("n must be nonnegative")
    goal = (n, n)
    path = [START]
    visited = {START}

    def visit(here: Vertex) -> Iterator[tuple[Vertex, ...]]:
        if here == goal:
            yield tuple(path)
            return
        for direction in ALL_DIRECTIONS:
            neighbor = add(here, direction)
            if not inside(neighbor, n) or neighbor in visited:
                continue
            visited.add(neighbor)
            path.append(neighbor)
            yield from visit(neighbor)
            path.pop()
            visited.remove(neighbor)

    yield from visit(START)


def count_bruteforce_and_check_patterns(n: int) -> tuple[int, int]:
    """Count directly and compare every path with forbidden-pattern matching."""

    patterns = forbidden_patterns(n)
    total = 0
    valid = 0
    for path in simple_paths(n):
        total += 1
        direct = valid_by_definition(path)
        edges = path_edges(path)
        by_patterns = not any(pattern <= edges for pattern in patterns)
        if direct != by_patterns:
            raise AssertionError(
                f"n={n}: pattern mismatch for path {path}; "
                f"direct={direct}, patterns={by_patterns}"
            )
        valid += int(direct)
    return total, valid


def run_self_test(max_n: int) -> None:
    """Run an independent, definition-level exhaustive test for small n."""

    if max_n < 0:
        raise ValueError("self-test maximum must be nonnegative")
    for n in range(max_n + 1):
        total, valid = count_bruteforce_and_check_patterns(n)
        if n < len(KNOWN_PREFIX) and valid != KNOWN_PREFIX[n]:
            raise AssertionError(
                f"n={n}: direct count {valid} != known value {KNOWN_PREFIX[n]}"
            )
        print(
            f"self-test n={n}: {total} simple paths, {valid} valid",
            file=sys.stderr,
            flush=True,
        )


def nonnegative(value: str) -> int:
    """argparse type for nonnegative integers."""

    number = int(value)
    if number < 0:
        raise argparse.ArgumentTypeError("must be nonnegative")
    return number


def parse_args(argv: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compute A400112 using Graphillion.",
    )
    parser.add_argument(
        "max_n",
        nargs="?",
        type=nonnegative,
        help="compute terms through this index (inclusive)",
    )
    parser.add_argument(
        "--start",
        type=nonnegative,
        default=0,
        help="first index to compute (default: 0)",
    )
    parser.add_argument(
        "--traversal",
        choices=("greedy", "bfs", "dfs", "as-is"),
        default="greedy",
        help="Graphillion universe edge traversal (default: greedy)",
    )
    parser.add_argument(
        "--self-test",
        nargs="?",
        const=4,
        type=nonnegative,
        metavar="N",
        help="brute-force-check all paths through N (default: 4)",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="suppress progress messages on stderr",
    )
    return parser.parse_args(argv)


def main(argv: Iterable[str] | None = None) -> int:
    args = parse_args(argv)

    if args.self_test is not None:
        run_self_test(args.self_test)
        if args.max_n is None:
            return 0

    if args.max_n is None:
        print("error: max_n is required unless --self-test is used", file=sys.stderr)
        return 2
    if args.start > args.max_n:
        print("error: --start must not exceed max_n", file=sys.stderr)
        return 2

    try:
        for n in range(args.start, args.max_n + 1):
            value = count_graphillion(
                n,
                traversal=args.traversal,
                progress=not args.quiet,
            )
            print(n, value, flush=True)
    except RuntimeError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
