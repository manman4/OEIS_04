"""Compute A401472 (Erdos Problem 795) using integer/Boolean constraints.

Maximum size of a subset of {1, ..., n} whose subset products are all distinct.

Dependency: z3-solver. No published sequence values are used as bounds.
A checkpoint is verified and resumed automatically. Completed terms are printed
and written on one line only after the requested range has been proved.

PYTHONPATH=/tmp/erdos795-deps python3 -B "./401472_01.py" 40   
"""

import argparse
from collections import defaultdict
from itertools import combinations
import json
from math import prod
from pathlib import Path
import sys
import time

try:
    import z3
except ImportError as error:
    raise SystemExit("z3-solver is required; install the version in requirements.txt") from error


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
            assert prod(left) == prod(right)
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
    active = {a for a in items if z3.is_true(model.eval(positive[a])) or
              z3.is_true(model.eval(negative[a]))}
    for a in set(items)-active:
        checker.add(z3.Not(positive[a]), z3.Not(negative[a]))
    # Shrink a valid collision's support without allowing new elements.
    for a in sorted(active):
        checker.push()
        checker.add(z3.Not(positive[a]), z3.Not(negative[a]))
        answer = checked(checker)
        checker.pop()
        if answer == z3.sat:
            checker.add(z3.Not(positive[a]), z3.Not(negative[a]))
    assert checked(checker) == z3.sat
    model = checker.model()
    left = [a for a in items if z3.is_true(model.eval(positive[a]))]
    right = [a for a in items if z3.is_true(model.eval(negative[a]))]
    assert left and right and not set(left)&set(right)
    assert prod(left) == prod(right)
    return {"left": left, "right": right}


def atomic_write(path, text):
    from tempfile import NamedTemporaryFile
    temporary = None
    try:
        with NamedTemporaryFile(mode="w", encoding="utf-8", newline="\n",
                                dir=path.parent, prefix=f".{path.name}.",
                                delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(text)
        temporary.replace(path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def load_state(path):
    if not path.exists():
        return {"limit_completed": 0, "values": [], "witnesses": [],
                "cuts": [], "statistics": [], "elapsed_seconds": 0.0}
    state = json.loads(path.read_text(encoding="utf-8"))
    completed = state["limit_completed"]
    if not isinstance(completed, int) or not 0 <= completed <= 100:
        raise ValueError("Invalid completed range in checkpoint")
    if len(state["values"]) != completed or len(state["witnesses"]) != completed:
        raise ValueError("Checkpoint lengths disagree")
    for n, (value, witness) in enumerate(zip(state["values"], state["witnesses"]), 1):
        if not isinstance(value, int) or not 0 <= value <= n-1:
            raise ValueError(f"Invalid optimum at n={n}")
        if len(witness) != value or len(set(witness)) != value:
            raise ValueError(f"Invalid witness size at n={n}")
        if any(not isinstance(a, int) or not 2 <= a <= n for a in witness):
            raise ValueError(f"Invalid witness member at n={n}")
        if n > 1 and value-state["values"][n-2] not in (0, 1):
            raise ValueError(f"Invalid increment at n={n}")
    for relation in state["cuts"]:
        left, right = relation["left"], relation["right"]
        if not left or not right or set(left)&set(right):
            raise ValueError("Invalid collision cut")
        if len(set(left)) != len(left) or len(set(right)) != len(right):
            raise ValueError("Repeated factor in collision cut")
        if any(not isinstance(a, int) or not 2 <= a <= 100 for a in left+right):
            raise ValueError("Invalid factor in collision cut")
        if prod(left) != prod(right):
            raise ValueError("False arithmetic identity in collision cut")
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
                if z3.is_true(model.eval(variables[a]))]
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


def compute(limit, checkpoint, output, timeout_ms=0, verify_only=False):
    state = load_state(checkpoint)
    universe = max(limit, state.get("universe_limit", 1),
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

    for key, relation in initial_relations(universe).items():
        if key not in cuts:
            cuts[key] = relation
            solver.add(z3.Or([z3.Not(variables[a]) for a in key]))
    started = time.monotonic()
    prior_elapsed = state.get("elapsed_seconds", 0.0)
    pending = state.get("pending")

    def save():
        state.update({"universe_limit": universe, "target_limit": limit,
                      "cuts": list(cuts.values()), "pending": pending,
                      "z3_version": z3.get_version_string(),
                      "elapsed_seconds": prior_elapsed+time.monotonic()-started})
        atomic_write(checkpoint, json.dumps(state, indent=2)+"\n")

    try:
        for n in range(state["limit_completed"]+1, limit+1):
            candidates = [pure_prime_construction(n)]
            if state["witnesses"]:
                candidates.append(state["witnesses"][-1])
            if pending and pending.get("n") == n:
                candidate = pending["witness"]
                if (all(2 <= a <= n for a in candidate) and
                        len(set(candidate)) == len(candidate) and
                        find_relation(candidate, fs, timeout_ms) is None):
                    candidates.append(candidate)
            witness = list(max(candidates, key=len))
            lower = len(witness)
            refinements = 0
            pending = {"n": n, "lower_bound": lower, "witness": witness}
            while lower < n-1:
                selected = upper_probe(solver, variables, n, lower+1)
                if selected is None:
                    break
                relation = find_relation(selected, fs, timeout_ms)
                refinements += 1
                if relation is None:
                    witness, lower = selected, len(selected)
                    pending = {"n": n, "lower_bound": lower, "witness": witness}
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
            state["values"].append(lower)
            state["witnesses"].append(witness)
            state["statistics"].append({"n": n, "refinements": refinements})
            state["limit_completed"] = n
            pending = None
            save()
            print(f"n={n}: {lower} (optimal)", file=sys.stderr, flush=True)
    except (KeyboardInterrupt, IncompleteCheck):
        save()
        print(f"Paused. Only n=1..{state['limit_completed']} are proved; "
              f"checkpoint saved to {checkpoint}.", file=sys.stderr, flush=True)
        raise

    text = ", ".join(map(str, state["values"][:limit]))
    atomic_write(output, text+"\n")
    print(text)
    print(f"Saved n=1..{limit} to {output}", file=sys.stderr, flush=True)


def main():
    directory = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("N", nargs="?", type=int, default=100)
    parser.add_argument("--checkpoint", type=Path,
                        default=directory/"problem795_checkpoint.json")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--timeout-ms", type=int, default=0,
                        help="per-query timeout; 0 disables the timeout")
    parser.add_argument("--verify-only", action="store_true")
    args = parser.parse_args()
    if not 1 <= args.N <= 100 or args.timeout_ms < 0:
        parser.error("N must be in 1..100; timeout must be nonnegative")
    output = args.output or directory/f"terms_1_to_{args.N}.txt"
    if output.resolve() in {args.checkpoint.resolve(), Path(__file__).resolve()}:
        parser.error("Output must differ from the script and checkpoint")
    try:
        compute(args.N, args.checkpoint, output, args.timeout_ms, args.verify_only)
    except KeyboardInterrupt:
        return 130
    except IncompleteCheck as error:
        print(f"Incomplete solver query: {error}. No unproved value was appended.",
              file=sys.stderr)
        return 2
    except (OSError, ValueError, KeyError) as error:
        parser.exit(1, f"Error: {error}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
