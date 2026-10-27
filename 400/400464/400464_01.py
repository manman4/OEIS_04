"""Compute A400464 (Erdos Problem 425), saving each proved term to b400464.txt.

Maximum size of a subset of {1, ..., n} whose products of two distinct
members are all distinct. Includes 1; only two-element subsets are compared.
Dependency: z3-solver. No published values or b-files are used as bounds.
"""

import argparse
from collections import defaultdict
from contextlib import ExitStack, contextmanager
import fcntl
from itertools import combinations
import json
import os
from pathlib import Path
import shlex
import sys
from tempfile import NamedTemporaryFile
import time

try:
    import z3
except ImportError as error:
    directory = Path(__file__).resolve().parent
    local_python = directory/".venv/bin/python"
    if local_python.exists():
        hint = "Run with the local environment:\n"+shlex.join(
            [str(local_python), "-B", str(Path(__file__).resolve()), *sys.argv[1:]])
    else:
        hint = ("From the script directory run:\n"
                "python3 -m venv .venv\n"
                ".venv/bin/python -m pip install -r requirements.txt")
    raise SystemExit("z3-solver is not available to this Python.\n"+hint) from error


class IncompleteCheck(RuntimeError):
    pass


class OutputLocked(RuntimeError):
    pass


def atomic_write(path, text):
    """Readers see the old complete file or the new complete file."""
    path = Path(path)
    temporary = None
    try:
        with NamedTemporaryFile(mode="w", encoding="utf-8", newline="\n",
                                dir=path.parent, prefix=f".{path.name}.",
                                suffix=".tmp", delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


@contextmanager
def output_locks(paths):
    """Reject concurrent writers sharing any checkpoint or output path."""
    with ExitStack() as stack:
        for path in sorted({Path(p).resolve() for p in paths}):
            path.parent.mkdir(parents=True, exist_ok=True)
            lock = stack.enter_context(open(str(path)+".lock", "a", encoding="utf-8"))
            try:
                fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as error:
                raise OutputLocked(f"Another process is using {path}") from error
        yield


def collision_edges(limit):
    """All forbidden four-element supports, grouped by their largest member."""
    ways = defaultdict(list)
    for a, b in combinations(range(1, limit+1), 2):
        ways[a*b].append((a, b))
    edges = set()
    for pairs in ways.values():
        for left, right in combinations(pairs, 2):
            # Equal products of positive, different pairs cannot share a member.
            assert set(left).isdisjoint(right)
            edges.add(tuple(sorted(left+right)))
    by_maximum = defaultdict(list)
    for edge in sorted(edges):
        by_maximum[edge[-1]].append(edge)
    return by_maximum


class UpperModel:
    def __init__(self, limit, timeout_ms):
        self.variables = {a: z3.Bool(f"select_{a}") for a in range(1, limit+1)}
        self.edges = collision_edges(limit)
        self.solver = z3.Solver()
        self.solver.set(timeout=timeout_ms)
        self.active = 0

    def advance(self, n):
        if n != self.active+1:
            raise ValueError("Prefixes must be activated consecutively")
        for edge in self.edges[n]:
            self.solver.add(z3.Or([z3.Not(self.variables[a]) for a in edge]))
        self.active = n

    def probe(self, n, target):
        """Return a valid set of size at least target, or None for UNSAT."""
        if n != self.active:
            raise ValueError("Wrong active prefix")
        self.solver.push()
        try:
            self.solver.add(z3.PbGe([(self.variables[a], 1)
                                    for a in range(1, n+1)], target))
            status = self.solver.check()
            if status == z3.unsat:
                return None
            if status != z3.sat:
                reason = self.solver.reason_unknown()
                if "interrupt" in reason.lower():
                    raise KeyboardInterrupt
                raise IncompleteCheck(reason)
            model = self.solver.model()
            return [a for a in range(1, n+1)
                    if z3.is_true(model.eval(self.variables[a], model_completion=True))]
        finally:
            self.solver.pop()


def validate_witness(n, value, witness):
    if type(value) is not int or not 0 <= value <= n:
        raise ValueError(f"Invalid value at n={n}")
    if (not isinstance(witness, list) or len(witness) != value or
            any(type(a) is not int or not 1 <= a <= n for a in witness) or
            len(set(witness)) != value):
        raise ValueError(f"Invalid witness at n={n}")
    # Direct integer products, independent of the model's conflict supports.
    products = [a*b for a, b in combinations(witness, 2)]
    if len(products) != len(set(products)):
        raise ValueError(f"Colliding pair products at n={n}")


def load_state(path):
    if not path.exists():
        return {"format_version": 1, "sequence": "A400464", "erdos_problem": 425,
                "limit_completed": 0, "values": [], "witnesses": [],
                "statistics": [], "search_seconds": 0.0}
    state = json.loads(path.read_text(encoding="utf-8"))
    if (state.get("format_version") != 1 or state.get("sequence") != "A400464" or
            state.get("erdos_problem") != 425):
        raise ValueError("Checkpoint belongs to a different sequence or format")
    completed = state["limit_completed"]
    if type(completed) is not int or not 0 <= completed <= 100:
        raise ValueError("Invalid completed range")
    if (len(state["values"]) != completed or len(state["witnesses"]) != completed or
            len(state["statistics"]) != completed):
        raise ValueError("Checkpoint lengths disagree")
    previous = 0
    for n, (value, witness) in enumerate(zip(state["values"], state["witnesses"]), 1):
        validate_witness(n, value, witness)
        if value-previous not in (0, 1):
            raise ValueError(f"Invalid increment at n={n}")
        previous = value
    return state


def verify_state(state, model):
    """Prove the saved prefix by induction; never trust saved upper bounds."""
    previous = 0
    for n, value in enumerate(state["values"], 1):
        model.advance(n)
        # On an increase, the witness and F(n)<=F(n-1)+1 already prove equality.
        # On a plateau, explicitly exclude a set with one more member.
        if value == previous and model.probe(n, value+1) is not None:
            raise ValueError(f"Saved value is not maximal at n={n}")
        previous = value


def compute(limit, checkpoint, output, bfile, timeout_ms=0, verify_only=False):
    state = load_state(checkpoint)
    model = UpperModel(max(limit, state["limit_completed"]), timeout_ms)
    print(f"Checking saved n=1..{state['limit_completed']}...", file=sys.stderr, flush=True)
    verify_state(state, model)
    print("Saved completed range verified.", file=sys.stderr, flush=True)
    if verify_only:
        return state["values"][:limit]

    def write_bfile():
        # Preserve the entire proved prefix even if this invocation requests less.
        atomic_write(bfile, "".join(f"{n} {value}\n"
                                   for n, value in enumerate(state["values"], 1)))

    write_bfile()
    started = time.monotonic()
    prior_seconds = state["search_seconds"]

    def save():
        state["search_seconds"] = prior_seconds+time.monotonic()-started
        state["z3_version"] = z3.get_version_string()
        atomic_write(checkpoint, json.dumps(state, indent=2)+"\n")
        write_bfile()

    try:
        for n in range(state["limit_completed"]+1, limit+1):
            model.advance(n)
            previous = state["values"][-1] if state["values"] else 0
            print(f"n={n}, testing size={previous+1}...", file=sys.stderr, flush=True)
            term_started = time.monotonic()
            witness = model.probe(n, previous+1)
            if witness is None:
                value = previous
                witness = state["witnesses"][-1].copy() if previous else []
                status = "unsat"
            else:
                value = previous+1
                status = "sat"
            validate_witness(n, value, witness)
            # One assignment commits the complete new in-memory term.
            state = {**state, "limit_completed": n,
                     "values": state["values"]+[value],
                     "witnesses": state["witnesses"]+[witness],
                     "statistics": state["statistics"]+[
                         {"n": n, "test_at_previous_plus_one": status,
                          "seconds": time.monotonic()-term_started}]}
            save()
            print(f"n={n}: {value} (optimal)", file=sys.stderr, flush=True)
    except (KeyboardInterrupt, IncompleteCheck):
        save()
        print(f"Paused. Only n=1..{state['limit_completed']} are proved.",
              file=sys.stderr, flush=True)
        raise

    text = ", ".join(map(str, state["values"][:limit]))
    atomic_write(output, text+"\n")
    print(text)
    print(f"Saved proved prefix n=1..{state['limit_completed']} to {bfile}",
          file=sys.stderr, flush=True)
    return state["values"][:limit]


def validate_paths(paths):
    resolved = [Path(path).resolve() for path in paths]
    if len(set(resolved)) != len(resolved):
        raise ValueError("Script, checkpoint, b-file and one-line output must differ")
    for left, right in combinations(resolved, 2):
        if left.exists() and right.exists() and left.samefile(right):
            raise ValueError("Paths refer to the same file")
    locks = {Path(str(path)+".lock") for path in resolved[1:]}
    if locks.intersection(resolved):
        raise ValueError("Output path conflicts with a lock file")
    return resolved


def main(argv=None):
    directory = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", nargs="?", type=int, default=100)
    parser.add_argument("--checkpoint", type=Path, default=directory/"problem425_checkpoint.json")
    parser.add_argument("--bfile", type=Path, default=directory/"b400464.txt")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--timeout-ms", type=int, default=0, help="per query; 0 means no timeout")
    parser.add_argument("--verify-only", action="store_true", help="check saved terms without updating results")
    args = parser.parse_args(argv)
    if not 1 <= args.N <= 100 or args.timeout_ms < 0:
        parser.error("N must be in 1..100; timeout must be nonnegative")
    output = args.output or directory/f"terms_1_to_{args.N}.txt"
    try:
        _, checkpoint, bfile, output = validate_paths([Path(__file__), args.checkpoint, args.bfile, output])
        lock_paths = [checkpoint] if args.verify_only else [checkpoint, bfile, output]
        with output_locks(lock_paths):
            compute(args.N, checkpoint, output, bfile,
                    args.timeout_ms, args.verify_only)
    except KeyboardInterrupt:
        return 130
    except IncompleteCheck as error:
        print(f"Incomplete solver query: {error}. No unproved value was appended.", file=sys.stderr)
        return 2
    except (OSError, ValueError, KeyError, TypeError, OutputLocked) as error:
        print(f"Error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
