# A401948 と Erdős Problem 607 の Lean 4 形式化

[English README](README.md)

## 問題の定義から計数結果まで

### 点配置から直線サイズ集合へ

問題607では、実平面上の相異なる $`n`$ 点の集合 $`P`$ を取る。$`P`$ の2点以上を通る直線ごとに、その直線上にある $`P`$ の点の個数を調べ、同じ個数は一度だけ集合に入れる。Lean の `profile` がこの直線サイズ集合、`Realized n A` が集合 $`A`$ をちょうど $`n`$ 点で実現できるという条件、`F n` が実現できる集合の総数を表す。[Erdős Problem 607](https://www.erdosproblems.com/607)・[Lean の定義](A401948Lean/Definitions.lean)・[実現と計数の定義](A401948Lean/Classification.lean)

### 実現条件から A401947 の各列と A401948 の行和へ

$`3\le s_1\lt\cdots\lt s_r`$、$`r\ge2`$ のとき、`realizable_iff` は、サイズ集合 $`\{2,s_1,\ldots,s_r\}`$ をちょうど $`n`$ 点で実現できることと、次の条件が同値であることを証明する。

```math
L=\sum_{i=1}^r\max(0,s_i+i-r)\le n.
```

下界は各直線の共有点を数えて得る。逆向きでは、余分な共線を避けてちょうど $`L`$ 点で配置を作り、同じサイズ集合を保って $`n`$ 点まで増やす。非共線の配置には Sylvester–Gallai の定理によりサイズ2が現れる。全点が共線の場合と、3以上のサイズが高々1種類の場合を別に数えれば、すべての配置を分類できる。[実現の必要十分条件](A401948Lean/Main.lean)・[全分類](A401948Lean/Classification.lean)

A401947 の $`T(n,k)`$ は、この分類を集合の要素数 $`k`$ ごとに数えたもの。$`k\ge3`$ の列は、サイズ2と、それ以外の $`r=k-1`$ 種類を持つ集合を数える `countByLength n (k-1)` に対応する。$`k=0,1,2`$ は `smallProfiles` の場合分けに対応する。各列を足すと A401948 の $`F(n)`$ になり、Lean の `F_eq_countByLength` は小さい場合の合計と `countByLength` の和としてこの計数を証明している。[A401947](https://oeis.org/A401947)・[A401948](https://oeis.org/A401948)・[計数方法の証明](../401948_count_profiles_proof.md)

```math
F(n)=\sum_{k=0}^{K(n)} T(n,k),\quad K(n)=\lfloor\sqrt{4n+3}
floor-2.
```

### 行和から整数分割 DP へ

参照用 DP は、同じ $`L\le n`$ を満たすサイズ列を長さごとに数える。`dpAtLength_eq_count` が各長さの計数を、`certifiedCount_eq_F` が全長さを合わせた結果と幾何の $`F(n)`$ の一致を証明する。[参照用 DP](A401948Lean/CountingDP.lean)・[幾何の計数との一致](A401948Lean/Verification.lean)

高速版は、サイズ列を整数分割と点数に寄与しない末尾の選択に分ける。分割表の昇順更新と打ち切りを検証し、選択の重みを最小点数ごとに集計する。`fastPartitionCount_eq_certifiedCount` が参照用 DP との一致を、`partitionHistogramCount_eq_F` が累積集計の結果と幾何の $`F(n)`$ の一致を、任意の計算上限 $`N`$ と $`1\le n\le N`$ について証明する。ここまでが [Python 版](../401948_01.py) の計数処理に対応する Lean のモデルである。Python の実行系と b-file の保存処理は別の検証範囲となる。[整数分割 DP の最終定理](A401948Lean/FastVerification.lean)

### A401947 を個別に形式化する場合

幾何の分類を共有し、次の3つを個別の定理としてつなぐ。現行の Lean では、上記の `F_eq_countByLength` と A401948 の計数の一致まで証明済みである。

1. **各セル。** $`T(n,k)`$ を幾何学的に定義し、$`k\ge3`$ では `countByLength n (k-1)` と一致させる。$`k=0,1,2`$ は `smallProfiles` から導く。
2. **行の右端。** $`k\ge1`$ 種類を実現する最小点数 $`\lfloor(k+2)^2/4\rfloor`$ から、右端が $`\lfloor\sqrt{4n+3}\rfloor-2`$ になることを示す。$`n=1`$ では空集合が唯一の候補で、右端は0である。
3. **行和。** 右端までの $`T(n,k)`$ の和が既存の $`F(n)`$ と等しいことを示す。整数分割 DP はこの行和を高速に求める計算として接続する。

## ファイル

- [Definitions.lean](A401948Lean/Definitions.lean) は点、直線、直線サイズ集合、必要点数の定義。
- [Main.lean](A401948Lean/Main.lean) は必要点数の下界と実現の必要十分条件の証明。
- [OrdinaryLine.lean](A401948Lean/OrdinaryLine.lean) は分類に使う Sylvester–Gallai の定理の証明。
- [Classification.lean](A401948Lean/Classification.lean) は実現できる集合の全分類と、サイズ数別の計数式の証明。
- [CountingDP.lean](A401948Lean/CountingDP.lean) は DP の各セルが数える候補の証明。
- [Verification.lean](A401948Lean/Verification.lean) は DP と $`F(n)`$ の一致および 参照版の長さ打ち切り条件の証明。
- [PartitionDP.lean](A401948Lean/PartitionDP.lean) は分割表の昇順更新と打ち切りの証明。
- [PartitionCount.lean](A401948Lean/PartitionCount.lean) は漸化式とゼロで埋めた整数分割の個数の一致の証明。
- [ProfileSplit.lean](A401948Lean/ProfileSplit.lean) と [ProfileEncoding.lean](A401948Lean/ProfileEncoding.lean) は整数分割と直線サイズ列との全単射の証明。
- [FastVerification.lean](A401948Lean/FastVerification.lean) は点数に寄与しない末尾の選択肢を数え、累積集計と $`F(n)`$ をつなぐ証明。
- [AxiomAudit.lean](A401948Lean/AxiomAudit.lean) は主要定理の公理監査。

## 検証

Lean 4.27.0 と Mathlib 4.27.0 は `lean-toolchain` と `lake-manifest.json` で固定している。`lakefile.toml` のあるディレクトリで次を実行する。依存関係のキャッシュがあれば再利用できる。

```sh
lake build
lake env lean A401948Lean/AxiomAudit.lean
```

公理監査で報告されるのは Lean の標準公理 `propext`、`Classical.choice`、`Quot.sound` である。
