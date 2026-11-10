# A401948 and Erdős Problem 607 in Lean 4

[日本語版](README_JA.md)

This Lake project proves that an executable reference recurrence computes $`F(n)`$, the number of distinct line-size sets realized by exactly $`n`$ points in the real plane.

For $`3\le s_1\lt\cdots\lt s_r`$ and $`r\ge2`$, `Erdos607.realizable_iff` says that the line-size set $`\{2,s_1,\ldots,s_r\}`$ is realizable if and only if

```math
\sum_{i=1}^r\max(0,s_i+i-r)\le n.
```

The classification also covers collinear configurations and the cases with at most one size greater than two. The proof of `Erdos607.certifiedCount_eq_F` connects that classification to the recurrence for increasing prefixes. The existing Python implementation evaluates the recurrence with a rolling sum and two tables. Its loop invariants are checked separately in the [mathematical proof](../401948_count_profiles_proof.md).

## Files

- [Definitions.lean](A401948Lean/Definitions.lean) defines points, lines, line-size profiles, and the required point count.
- [Main.lean](A401948Lean/Main.lean) proves the lower bound and the realizability equivalence.
- [OrdinaryLine.lean](A401948Lean/OrdinaryLine.lean) proves the Sylvester–Gallai theorem used in the classification.
- [Classification.lean](A401948Lean/Classification.lean) classifies all profiles and derives the count by length.
- [CountingDP.lean](A401948Lean/CountingDP.lean) proves what each DP cell counts.
- [Verification.lean](A401948Lean/Verification.lean) connects the recurrence to $`F(n)`$ and proves the length cutoff used in Python.
- [AxiomAudit.lean](A401948Lean/AxiomAudit.lean) checks the axioms used by these results.

## Verification

Lean 4.27.0 and Mathlib 4.27.0 are pinned in `lean-toolchain` and `lake-manifest.json`. Run these commands from the directory containing `lakefile.toml`. Lake can reuse an existing dependency cache.

```sh
lake build
lake env lean A401948Lean/AxiomAudit.lean
```

The audit reports the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
