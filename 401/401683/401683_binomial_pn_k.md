# a(n) = Σ binomial(pn, k) a(n−k) の母関数と性質

## 主張

$p \ge 1$ を整数とし、数列 $a(n)$ を

$$
a(0) = 1, \qquad a(n) = \sum_{k=1}^{n} \binom{pn}{k}\, a(n-k) \quad (n \ge 1)
$$

で定める。母関数を $A(x) = \sum_{n \ge 0} a(n) x^n$ とする。

1. **母関数.**
   $$
   A(x) = \frac{1-(p-1)x}{1+x}\left(2A\!\left(\frac{x}{(1+x)^p}\right) - 1\right).
   $$
2. **割り切れる性質.** すべての $n \ge 1$ について $p \mid a(n)$ である。さらに $\gcd_{n \ge 1} a(n) = p$ である。

OEIS 形式では次のように書ける。

> G.f. A(x) satisfies A(x) = (1-(p-1)*x)/(1+x) * (2*A(x/(1+x)^p) - 1).
>
> p | a(n) for n > 0.

## 例

| $p$ | 母関数 | 数列 |
|---|---|---|
| 1 | $A(x) = \dfrac{1}{1+x}\bigl(2A(\tfrac{x}{1+x}) - 1\bigr)$ | 1, 1, 3, 13, 75, 541, 4683, …（Fubini 数） |
| 2 | $A(x) = \dfrac{1-x}{1+x}\bigl(2A(\tfrac{x}{(1+x)^2}) - 1\bigr)$ | 1, 2, 14, 134, 1646, 24842, 445658, … |
| 3 | $A(x) = \dfrac{1-2x}{1+x}\bigl(2A(\tfrac{x}{(1+x)^3}) - 1\bigr)$ | 1, 3, 33, 489, 9201, 211473, 5758539, … |
| 4 | $A(x) = \dfrac{1-3x}{1+x}\bigl(2A(\tfrac{x}{(1+x)^4}) - 1\bigr)$ | 1, 4, 60, 1204, 30524, 942524, 34424268, … |
| 5 | $A(x) = \dfrac{1-4x}{1+x}\bigl(2A(\tfrac{x}{(1+x)^5}) - 1\bigr)$ | 1, 5, 95, 2405, 76695, 2973755, … |

$p = 1$ の式は、Fubini 数のよく知られた式 $2A(x) = 1 + \dfrac{1}{1-x}A\!\left(\dfrac{x}{1-x}\right)$ で $x \to \dfrac{x}{1+x}$ と置き換えたものである。

## 母関数の証明（ラグランジュ反転）

$z = \dfrac{x}{(1+x)^p}$ とおくと $x = z\,\varphi(x)$、$\varphi(x) = (1+x)^p$ と書ける。べき級数 $F$ に対して

$$
\sum_{n \ge 0} z^n\, [x^n]\, F(x)\varphi(x)^n = \frac{F(x)}{1 - z\varphi'(x)}
$$

が成り立つ。ここで

$$
z\varphi'(x) = \frac{x}{(1+x)^p} \cdot p(1+x)^{p-1} = \frac{px}{1+x},
\qquad
1 - z\varphi'(x) = \frac{1-(p-1)x}{1+x}
$$

である。

$F(x) = A(x)$ とすると、$[x^k](1+x)^{pn} = \binom{pn}{k}$ より

$$
c(n) := [x^n]\, A(x)(1+x)^{pn} = \sum_{k=0}^{n} \binom{pn}{k}\, a(n-k)
$$

となる。よって

$$
\sum_{n \ge 0} c(n)\, z^n = \frac{(1+x)\,A(x)}{1-(p-1)x}
$$

が成り立つ。

$n \ge 1$ では、$k = 0$ の項 $a(n)$ に漸化式の和 $a(n)$ が加わるので $c(n) = 2a(n)$ である。$n = 0$ では $c(0) = 1$ である。まとめると $c(n) = 2a(n) - [n=0]$ なので、

$$
\frac{(1+x)\,A(x)}{1-(p-1)x} = 2A(z) - 1
$$

となり、$A(x)$ について解くと主張 1 の式が得られる。

**一意性.** この関数方程式を満たす級数は一つしかない。$z = x + O(x^2)$ なので、右辺の $x^n$ の係数は $2a(n) + (\text{$a(0),\dots,a(n-1)$ で決まる量})$ となり、$a(n)$ が順に決まるからである。したがって、母関数の式と漸化式は同じ数列を定める。 $\blacksquare$

## 割り切れる性質の証明

**補題.** $n \ge 1$ のとき

$$
\binom{pn}{n} = p\binom{pn-1}{n-1}.
$$

これは $\binom{N}{n} = \dfrac{N}{n}\binom{N-1}{n-1}$ に $N = pn$ を代入したものである。

**証明.** $n \ge 1$ について強い帰納法を使う。$1 \le m < n$ を満たすすべての $m$ で $p \mid a(m)$ が成り立つと仮定する（$n = 1$ のときは仮定は空である）。

$$
a(n) = \sum_{k=1}^{n-1} \binom{pn}{k}\, a(n-k) \;+\; \binom{pn}{n}\, a(0).
$$

1. **$1 \le k \le n-1$ の項.** $1 \le n-k \le n-1$ なので、帰納法の仮定から $p \mid a(n-k)$ である。
2. **$k = n$ の項.** $a(0) = 1$ なので、この項は $\binom{pn}{n}$ である。補題より $p$ の倍数である。

よって $p \mid a(n)$ である。

**最大であること.** $a(1) = \binom{p}{1} = p$ なので、$n \ge 1$ のすべての $a(n)$ を割り切る数は $p$ 以下である。したがって $\gcd_{n \ge 1} a(n) = p$ である。 $\blacksquare$

## binomial(tn+k−1, k) の族との関係

$$
b(0) = 1, \qquad b(n) = \sum_{k=1}^{n} \binom{tn+k-1}{k}\, b(n-k)
$$

の母関数は

$$
B(x) = \frac{1-(t+1)x}{1-x}\Bigl(2B\bigl(x(1-x)^t\bigr) - 1\Bigr)
$$

を満たす。この族で $t = -p$ とおくと、binomial(pn, k) の族と同じものになる。

1. 二項係数の上を負にする公式 $\binom{-N+k-1}{k} = (-1)^k\binom{N}{k}$ より、$t = -p$ では $\binom{-pn+k-1}{k} = (-1)^k\binom{pn}{k}$ となる。
2. よって $b(n) = \sum_{k=1}^{n} (-1)^k \binom{pn}{k}\, b(n-k)$ である。
3. $a(n) = (-1)^n b(n)$ とおくと、符号 $(-1)^n (-1)^k (-1)^{n-k} = 1$ が消えて、$a(n) = \sum_{k=1}^{n} \binom{pn}{k}\, a(n-k)$ となる。
4. 母関数では $A(x) = B(-x)$ である。$B$ の式で $t = -p$ とし、$x \to -x$ とすると
   - $\dfrac{1-(t+1)x}{1-x} \to \dfrac{1-(p-1)x}{1+x}$
   - $x(1-x)^t \to -\dfrac{x}{(1+x)^p}$、つまり $B\!\left(-\dfrac{x}{(1+x)^p}\right) = A\!\left(\dfrac{x}{(1+x)^p}\right)$

   となり、主張 1 の式と一致する。

割り切れる性質も対応している。binomial(tn+k−1, k) の族では $t \mid b(n)$、binomial(pn, k) の族では $p \mid a(n)$ である。どちらも $k = n$ の項から因数が出る。

| 族 | $k = n$ の項 | 割り切る数 |
|---|---|---|
| $\binom{tn+k-1}{k}$ | $\binom{(t+1)n-1}{n} = t\binom{(t+1)n-1}{n-1}$ | $t$ |
| $\binom{pn}{k}$ | $\binom{pn}{n} = p\binom{pn-1}{n-1}$ | $p$ |

## binomial(rn+k, k) の族との比較

| 漸化式 | 母関数 |
|---|---|
| $\binom{rn+k}{k}$ | $A(x) = \bigl(1-(r+1)x\bigr)\bigl(2A(x(1-x)^r) - 1\bigr)$ |
| $\binom{tn+k-1}{k}$ | $A(x) = \dfrac{1-(t+1)x}{1-x}\bigl(2A(x(1-x)^t) - 1\bigr)$ |
| $\binom{pn}{k}$ | $A(x) = \dfrac{1-(p-1)x}{1+x}\bigl(2A(\tfrac{x}{(1+x)^p}) - 1\bigr)$ |

## 補足

- 母関数の式は、$p = 1, \dots, 6$ について $x^{14}$ の係数まで整数演算で一致することを確かめた。
- $\gcd_{n \ge 1} a(n) = p$ は、$p = 1, \dots, 8$ について $n = 59$ まで数値計算で確かめた。
