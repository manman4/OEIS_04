# A401948 and Erdős Problem 607 in Lean 4

[日本語版](README_JA.md)

This Lake project proves that both the reference recurrence and the integer-partition DP compute $`F(n)`$, the number of distinct line-size sets realized by exactly $`n`$ points in the real plane.

For $`3\le s_1\lt\cdots\lt s_r`$ and $`r\ge2`$, `Erdos607.realizable_iff` says that the line-size set $`\{2,s_1,\ldots,s_r\}`$ is realizable if and only if

```math
\sum_{i=1}^r\max(0,s_i+i-r)\le n.
```

The classification also covers collinear configurations and the cases with at most one size greater than two. The proof of `Erdos607.certifiedCount_eq_F` connects that classification to the recurrence for increasing prefixes. The theorem `Erdos607.partitionHistogramCount_eq_F` proves that the integer-partition DP, with a batch limit $`N`$, gives $`F(n)`$ for every $`1\le n\le N`$. The Lean model uses the same truncated, ascending array updates as the [Python implementation](../401948_01.py) and proves the corresponding weighted histogram and cumulative sum correct. The theorem covers the mathematical computation. File output and the Python runtime are outside its scope.

## Files

- [Definitions.lean](A401948Lean/Definitions.lean) defines points, lines, line-size profiles, and the required point count.
- [Main.lean](A401948Lean/Main.lean) proves the lower bound and the realizability equivalence.
- [OrdinaryLine.lean](A401948Lean/OrdinaryLine.lean) proves the Sylvester–Gallai theorem used in the classification.
- [Classification.lean](A401948Lean/Classification.lean) classifies all profiles and derives the count by length.
- [CountingDP.lean](A401948Lean/CountingDP.lean) proves what each DP cell counts.
- [Verification.lean](A401948Lean/Verification.lean) connects the recurrence to $`F(n)`$ and proves the reference recurrence’s length cutoff.
- [PartitionDP.lean](A401948Lean/PartitionDP.lean) proves the ascending array update and its truncation correct.
- [PartitionCount.lean](A401948Lean/PartitionCount.lean) proves that the recurrence counts padded integer partitions.
- [ProfileSplit.lean](A401948Lean/ProfileSplit.lean) and [ProfileEncoding.lean](A401948Lean/ProfileEncoding.lean) give the bijection with the lists of line sizes.
- [FastVerification.lean](A401948Lean/FastVerification.lean) counts the choices of zero-cost sizes and connects the histogram to $`F(n)`$.
- [AxiomAudit.lean](A401948Lean/AxiomAudit.lean) checks the axioms used by these results.

## Verification

Lean 4.27.0 and Mathlib 4.27.0 are pinned in `lean-toolchain` and `lake-manifest.json`. Run these commands from the directory containing `lakefile.toml`. Lake can reuse an existing dependency cache.

```sh
lake build
lake env lean A401948Lean/AxiomAudit.lean
```

The audit reports the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
