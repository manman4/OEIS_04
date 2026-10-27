"""Compute A401472 (Erdos Problem 795) using integer/Boolean constraints.

Maximum size of a subset of {1, ..., n} whose subset products are all distinct.

Dependency: z3-solver. No published sequence values are used as bounds.
A checkpoint is verified and resumed automatically. Each proved term is saved
to b401472.txt as an n a(n) row. A one-line list is also printed and saved after
the requested range has been proved.
"""

import argparse
from collections import defaultdict
from contextlib import ExitStack, contextmanager
import fcntl
from itertools import combinations
import json
from math import isfinite, prod
import os
from pathlib import Path
import sys
import time

try:
    import z3
except ImportError as error:
    raise SystemExit("z3-solver is required; install the version in requirements.txt") from error


MAX_N = 100
MAX_TIMEOUT_MS = (1 << 32)-1


class OutputLocked(RuntimeError):
    pass


class IncompleteCheck(RuntimeError):
    pass


def checked(solver, *assumptions):
    answer = solver.check(*assumptions)
    if answer == z3.unknown:
        reason = solver.reason_unknown()
        if "interrupt" in reason.lower():
            raise KeyboardInterrupt
        raise IncompleteCheck(reason)
    return answer



def factors(n):
    result = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0)+1
            n //= p
        p += 1
    if n > 1:
        result[n] = 1
    return result


def pure_prime_construction(n):
    result = []
    for p in range(2, n+1):
        if factors(p) != {p: 1}:
            continue
        value = p
        while value <= n:
            result.append(value)
            value *= value
    return sorted(result)


def initial_relations(limit):
    representations = defaultdict(list)
    for a in range(2, limit+1):
        representations[a].append((a,))
    for a, b in combinations(range(2, limit+1), 2):
        representations[a*b].append((a, b))
    cuts = {}
    for ways in representations.values():
        for a, b in combinations(ways, 2):
            left, right = sorted(set(a)-set(b)), sorted(set(b)-set(a))
            if not left or not right:
                continue
            if prod(left) != prod(right):
                raise ValueError("Invalid generated product relation")
            key = tuple(sorted(left+right))
            cuts[key] = {"left": left, "right": right}
    return cuts


def find_relation(selected, factorizations, timeout_ms=0):
    # A prime occurring in only one remaining element forces that element's
    # coefficient to be zero in any relation with coefficients -1,0,1.
    remaining = set(selected)
    while remaining:
        incidence = defaultdict(list)
        for a in remaining:
            for p in factorizations[a]:
                incidence[p].append(a)
        forced = {items[0] for items in incidence.values() if len(items) == 1}
        if not forced:
            break
        remaining -= forced
    if not remaining:
        return None
    items = sorted(remaining)
    positive = {a: z3.Bool(f"plus_{a}") for a in items}
    negative = {a: z3.Bool(f"minus_{a}") for a in items}
    checker = z3.Solver()
    checker.set(timeout=timeout_ms)
    for a in items:
        checker.add(z3.Or(z3.Not(positive[a]), z3.Not(negative[a])))
    checker.add(z3.Or([positive[a] for a in items]))
    primes = sorted({p for a in items for p in factorizations[a]})
    for p in primes:
        checker.add(z3.Sum([
            factorizations[a].get(p, 0) *
            (z3.If(positive[a], 1, 0)-z3.If(negative[a], 1, 0))
            for a in items
        ]) == 0)
    answer = checked(checker)
    if answer == z3.unsat:
        return None
    if answer != z3.sat:
        raise IncompleteCheck("Relation check incomplete: " + checker.reason_unknown())
    model = checker.model()
    active = {a for a in items if z3.is_true(model.eval(positive[a], model_completion=True)) or
              z3.is_true(model.eval(negative[a], model_completion=True))}
    for a in set(items)-active:
        checker.add(z3.Not(positive[a]), z3.Not(negative[a]))
    # Shrink a valid collision's support without allowing new elements.
    for a in sorted(active):
        checker.push()
        checker.add(z3.Not(positive[a]), z3.Not(negative[a]))
        try:
            answer = checked(checker)
        finally:
            checker.pop()
        if answer == z3.sat:
            checker.add(z3.Not(positive[a]), z3.Not(negative[a]))
    # This call is required even under python -O, after the last add/pop.
    if checked(checker) != z3.sat:
        raise ValueError("Relation reduction lost a satisfying assignment")
    model = checker.model()
    left = [a for a in items if z3.is_true(model.eval(positive[a], model_completion=True))]
    right = [a for a in items if z3.is_true(model.eval(negative[a], model_completion=True))]
    if not left or not right or set(left)&set(right) or prod(left) != prod(right):
        raise ValueError("Invalid product relation returned by the solver")
    return {"left": left, "right": right}


def atomic_write(path, text):
    from tempfile import NamedTemporaryFile
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


def write_bfile(path, values):
    """Replace the b-file with the complete proved prefix, avoiding duplicate rows."""
    atomic_write(path, "".join(f"{n} {value}\n"
                               for n, value in enumerate(values, 1)))


def checked_integer(value, name, minimum, maximum):
    if type(value) is not int or not minimum <= value <= maximum:
        raise ValueError(f"Invalid {name}: expected an integer in {minimum}..{maximum}")
    return value


def validate_witness_shape(n, value, witness):
    checked_integer(value, f"optimum at n={n}", 0, n-1)
    if not isinstance(witness, list) or len(witness) != value:
        raise ValueError(f"Invalid witness size at n={n}")
    if any(type(a) is not int or not 2 <= a <= n for a in witness):
        raise ValueError(f"Invalid witness member at n={n}")
    if len(set(witness)) != value:
        raise ValueError(f"Repeated witness member at n={n}")


def load_state(path):
    if not path.exists():
        return {"limit_completed": 0, "values": [], "witnesses": [],
                "cuts": [], "statistics": [], "elapsed_seconds": 0.0,
                "pending": None}
    state = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(state, dict):
        raise ValueError("Checkpoint must be an object")
    required = ("limit_completed", "values", "witnesses", "cuts", "statistics")
    if any(key not in state for key in required):
        raise ValueError("Checkpoint is missing required fields")
    completed = checked_integer(state["limit_completed"], "completed range", 0, MAX_N)
    for name in ("values", "witnesses", "cuts", "statistics"):
        if not isinstance(state[name], list):
            raise ValueError(f"Checkpoint {name} must be a list")
    if any(len(state[name]) != completed for name in ("values", "witnesses", "statistics")):
        raise ValueError("Checkpoint lengths disagree")
    for name in ("universe_limit", "target_limit"):
        if name in state:
            checked_integer(state[name], name, 1, MAX_N)
    elapsed = state.get("elapsed_seconds", 0.0)
    if type(elapsed) not in (int, float):
        raise ValueError("Invalid elapsed time")
    try:
        elapsed = float(elapsed)
    except (OverflowError, ValueError) as error:
        raise ValueError("Invalid elapsed time") from error
    if not isfinite(elapsed) or elapsed < 0:
        raise ValueError("Invalid elapsed time")
    state["elapsed_seconds"] = elapsed
    for n, (value, witness) in enumerate(zip(state["values"], state["witnesses"]), 1):
        validate_witness_shape(n, value, witness)
        if n > 1 and value-state["values"][n-2] not in (0, 1):
            raise ValueError(f"Invalid increment at n={n}")
        record = state["statistics"][n-1]
        if not isinstance(record, dict):
            raise ValueError(f"Invalid statistics at n={n}")
        if "n" in record:
            checked_integer(record["n"], "statistics index", n, n)
        if "refinements" in record:
            if type(record["refinements"]) is not int or record["refinements"] < 0:
                raise ValueError(f"Invalid refinement count at n={n}")
    for relation in state["cuts"]:
        if not isinstance(relation, dict) or "left" not in relation or "right" not in relation:
            raise ValueError("Invalid collision cut")
        left, right = relation["left"], relation["right"]
        if not isinstance(left, list) or not isinstance(right, list) or not left or not right:
            raise ValueError("Invalid collision cut")
        if any(type(a) is not int or not 2 <= a <= MAX_N for a in left+right):
            raise ValueError("Invalid factor in collision cut")
        if set(left)&set(right) or len(set(left)) != len(left) or len(set(right)) != len(right):
            raise ValueError("Repeated factor in collision cut")
        if prod(left) != prod(right):
            raise ValueError("False arithmetic identity in collision cut")
    pending = state.get("pending")
    if pending is not None:
        if not isinstance(pending, dict) or any(key not in pending for key in ("n", "lower_bound", "witness")):
            raise ValueError("Invalid pending search")
        n = checked_integer(pending["n"], "pending index", 1, MAX_N)
        validate_witness_shape(n, pending["lower_bound"], pending["witness"])
        if n > completed+1:
            raise ValueError("Pending search skips an index")
        if n <= completed:
            # A legacy interrupt may have saved an already completed pending term.
            pending = None
    state["pending"] = pending
    return state


def build_solver(universe, relations, timeout_ms):
    variables = {a: z3.Bool(f"select_{a}") for a in range(2, universe+1)}
    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    for relation in relations:
        members = relation["left"]+relation["right"]
        solver.add(z3.Or([z3.Not(variables[a]) for a in members]))
    return solver, variables


def upper_probe(solver, variables, n, target):
    if n == 1:
        return None
    solver.push()
    try:
        solver.add(z3.PbGe([(variables[a], 1) for a in range(2, n+1)], target))
        assumptions = [z3.Not(v) for a, v in variables.items() if a > n]
        if checked(solver, assumptions) == z3.unsat:
            return None
        model = solver.model()
        return [a for a in range(2, n+1)
                if z3.is_true(model.eval(variables[a], model_completion=True))]
    finally:
        solver.pop()


def verify_state(state, solver, variables, factorizations, timeout_ms):
    """Recheck every saved lower and upper bound before resuming."""
    for n, (value, witness) in enumerate(zip(state["values"], state["witnesses"]), 1):
        if value <= 20:
            # Independent actual-product enumeration, explicitly bounded.
            products = {1}
            for a in witness:
                new = {p*a for p in products}
                if products & new:
                    raise ValueError(f"Non-distinct subset products at n={n}")
                products |= new
        elif find_relation(witness, factorizations, timeout_ms) is not None:
            raise ValueError(f"Invalid witness at n={n}")
        if upper_probe(solver, variables, n, value+1) is not None:
            raise ValueError(f"Saved cuts do not prove the upper bound at n={n}")


def _compute_locked(limit, checkpoint, output, timeout_ms=0, verify_only=False, bfile=None):
    state = load_state(checkpoint)
    if (bfile is not None and state["limit_completed"] == 0 and
            bfile.exists() and bfile.stat().st_size > 0):
        raise ValueError("No proved checkpoint is available, but a nonempty b-file exists. "
                         "Restore its checkpoint or choose new --checkpoint, --bfile and "
                         "--output paths. The existing b-file was not changed.")
    universe = max(limit, state["limit_completed"], state.get("universe_limit", 1),
                   max((a for cut in state["cuts"]
                        for a in cut["left"]+cut["right"]), default=1))
    fs = {a: factors(a) for a in range(2, universe+1)}
    cuts = {tuple(sorted(c["left"]+c["right"])): c for c in state["cuts"]}
    solver, variables = build_solver(universe, cuts.values(), timeout_ms)
    print(f"Checking saved n=1..{state['limit_completed']}...", file=sys.stderr, flush=True)
    verify_state(state, solver, variables, fs, timeout_ms)
    print("Saved completed range verified.", file=sys.stderr, flush=True)
    if verify_only:
        return
    if bfile is not None:
        write_bfile(bfile, state["values"])

    for key, relation in initial_relations(universe).items():
        if key not in cuts:
            cuts[key] = relation
            solver.add(z3.Or([z3.Not(variables[a]) for a in key]))
    started = time.monotonic()
    prior_elapsed = state.get("elapsed_seconds", 0.0)
    def save():
        state.update({"universe_limit": universe, "target_limit": limit,
                      "cuts": list(cuts.values()),
                      "z3_version": z3.get_version_string(),
                      "elapsed_seconds": prior_elapsed+time.monotonic()-started})
        atomic_write(checkpoint, json.dumps(state, indent=2)+"\n")

    try:
        for n in range(state["limit_completed"]+1, limit+1):
            candidates = [pure_prime_construction(n)]
            if state["witnesses"]:
                candidates.append(state["witnesses"][-1])
            pending = state.get("pending")
            if pending and pending.get("n") == n:
                candidate = pending["witness"]
                if (all(2 <= a <= n for a in candidate) and
                        len(set(candidate)) == len(candidate) and
                        find_relation(candidate, fs, timeout_ms) is None):
                    candidates.append(candidate)
            witness = list(max(candidates, key=len))
            lower = len(witness)
            refinements = 0
            state = {**state, "pending": {"n": n, "lower_bound": lower, "witness": witness}}
            while lower < n-1:
                selected = upper_probe(solver, variables, n, lower+1)
                if selected is None:
                    break
                relation = find_relation(selected, fs, timeout_ms)
                refinements += 1
                if relation is None:
                    witness, lower = selected, len(selected)
                    state = {**state, "pending": {"n": n, "lower_bound": lower, "witness": witness}}
                else:
                    key = tuple(sorted(relation["left"]+relation["right"]))
                    if key in cuts:
                        raise AssertionError("Existing cut was violated")
                    cuts[key] = relation
                    solver.add(z3.Or([z3.Not(variables[a]) for a in key]))
                if refinements % 20 == 0:
                    save()
                    print(f"n={n}, lower={lower}, refinements={refinements}",
                          file=sys.stderr, flush=True)
            state = completed_state(state, n, lower, witness, refinements)
            save()
            if bfile is not None:
                write_bfile(bfile, state["values"])
            print(f"n={n}: {lower} (optimal)", file=sys.stderr, flush=True)
    except (KeyboardInterrupt, IncompleteCheck):
        save()
        if bfile is not None:
            write_bfile(bfile, state["values"])
        print(f"Paused. Only n=1..{state['limit_completed']} are proved; "
              f"checkpoint saved to {checkpoint}.", file=sys.stderr, flush=True)
        raise

    text = ", ".join(map(str, state["values"][:limit]))
    atomic_write(output, text+"\n")
    print(text)
    print(f"Saved n=1..{limit} to {output}", file=sys.stderr, flush=True)


def completed_state(state, n, value, witness, refinements):
    """Construct a complete new term without mutating the last proved state."""
    if n != state["limit_completed"]+1:
        raise ValueError("Nonconsecutive completed term")
    validate_witness_shape(n, value, witness)
    return {**state,
            "values": state["values"]+[value],
            "witnesses": state["witnesses"]+[list(witness)],
            "statistics": state["statistics"]+[{"n": n, "refinements": refinements}],
            "limit_completed": n, "pending": None}


@contextmanager
def output_locks(paths):
    """Protect all shared result paths, including direct compute() calls."""
    with ExitStack() as stack:
        for path in sorted({Path(path).resolve() for path in paths}):
            path.parent.mkdir(parents=True, exist_ok=True)
            stream = stack.enter_context(open(str(path)+".lock", "a", encoding="utf-8"))
            try:
                fcntl.flock(stream.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as error:
                raise OutputLocked(f"Another process is using {path}") from error
        yield


def compute(limit, checkpoint, output, timeout_ms=0, verify_only=False, bfile=None):
    checked_integer(limit, "N", 1, MAX_N)
    checked_integer(timeout_ms, "timeout", 0, MAX_TIMEOUT_MS)
    checkpoint, output = Path(checkpoint).resolve(), Path(output).resolve()
    bfile = Path(bfile).resolve() if bfile is not None else None
    results = [checkpoint, output]+([bfile] if bfile is not None else [])
    paths = [Path(__file__).resolve()]+results
    if len(set(paths)) != len(paths):
        raise ValueError("Script and result paths must differ")
    for left, right in combinations(paths, 2):
        if left.exists() and right.exists() and left.samefile(right):
            raise ValueError("Result paths refer to the same file")
    locks = {Path(str(path)+".lock") for path in results}
    if locks.intersection(paths):
        raise ValueError("Result path conflicts with a lock file")
    with output_locks([checkpoint] if verify_only else results):
        return _compute_locked(limit, checkpoint, output, timeout_ms, verify_only, bfile)


def main():
    directory = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", nargs="?", type=int, default=100)
    parser.add_argument("--checkpoint", type=Path,
                        default=directory/"problem795_checkpoint.json")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--bfile", type=Path, default=directory/"b401472.txt",
                        help="save proved n a(n) rows incrementally (default: b401472.txt)")
    parser.add_argument("--timeout-ms", type=int, default=0,
                        help="per-query timeout; 0 disables the timeout")
    parser.add_argument("--verify-only", action="store_true")
    args = parser.parse_args()
    if not 1 <= args.N <= MAX_N or not 0 <= args.timeout_ms <= MAX_TIMEOUT_MS:
        parser.error(f"N must be in 1..{MAX_N}; timeout must be in 0..{MAX_TIMEOUT_MS}")
    output = args.output or directory/f"terms_1_to_{args.N}.txt"
    paths = [output.resolve(), args.bfile.resolve(),
             args.checkpoint.resolve(), Path(__file__).resolve()]
    if len(set(paths)) != len(paths):
        parser.error("The b-file, one-line output, checkpoint and script must have different paths")
    try:
        compute(args.N, args.checkpoint, output, args.timeout_ms, args.verify_only,
                bfile=args.bfile)
    except KeyboardInterrupt:
        return 130
    except IncompleteCheck as error:
        print(f"Incomplete solver query: {error}. No unproved value was appended.",
              file=sys.stderr)
        return 2
    except (OSError, ValueError, KeyError, OutputLocked) as error:
        parser.exit(1, f"Error: {error}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
