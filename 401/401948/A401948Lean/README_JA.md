# A401948 と Erdős Problem 607 の Lean 4 形式化

[English README](README.md)

実平面上の相異なる $`n`$ 点で実現できる直線サイズ集合の総数 $`F(n)`$ を、実行可能な参照用の漸化式で求められることを証明する。

$`3\le s_1\lt\cdots\lt s_r`$、$`r\ge2`$ のとき、`Erdos607.realizable_iff` は、直線サイズ集合 $`\{2,s_1,\ldots,s_r\}`$ をちょうど $`n`$ 点で実現できることと、次の条件が同値であることを証明する。

```math
\sum_{i=1}^r\max(0,s_i+i-r)\le n.
```

全点が共線の場合や3以上のサイズが高々1種類の場合も分類する。`Erdos607.certifiedCount_eq_F` は、その分類と DP の漸化式をつなぎ、すべての正の $`n`$ で参照用の計算結果が $`F(n)`$ と一致することを示す。Python 版は同じ候補を整数分割の漸化式で数える。その導出は[計数方法の証明](../401948_count_profiles_proof.md)に記す。

## ファイル

- [Definitions.lean](A401948Lean/Definitions.lean) は点、直線、直線サイズ集合、必要点数の定義。
- [Main.lean](A401948Lean/Main.lean) は必要点数の下界と実現の必要十分条件の証明。
- [OrdinaryLine.lean](A401948Lean/OrdinaryLine.lean) は分類に使う Sylvester–Gallai の定理の証明。
- [Classification.lean](A401948Lean/Classification.lean) は実現できる集合の全分類と、サイズ数別の計数式の証明。
- [CountingDP.lean](A401948Lean/CountingDP.lean) は DP の各セルが数える候補の証明。
- [Verification.lean](A401948Lean/Verification.lean) は参照用 DP と $`F(n)`$ の一致および参照用の長さ打ち切り条件の証明。
- [AxiomAudit.lean](A401948Lean/AxiomAudit.lean) は主要定理の公理監査。

## 検証

Lean 4.27.0 と Mathlib 4.27.0 は `lean-toolchain` と `lake-manifest.json` で固定している。`lakefile.toml` のあるディレクトリで次を実行する。依存関係のキャッシュがあれば再利用できる。

```sh
lake build
lake env lean A401948Lean/AxiomAudit.lean
```

公理監査で報告されるのは Lean の標準公理 `propext`、`Classical.choice`、`Quot.sound` である。
