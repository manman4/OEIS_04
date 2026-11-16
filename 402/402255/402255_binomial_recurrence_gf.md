# 二項係数型の漸化式と母関数の関数方程式

A402250〜A402255 の FORMULA（G.f. の関数方程式）を、一つの定理としてまとめて証明する。

## 1. 定理

整数 $`m \ge 0`$ と整数 $`r`$（負でもよい）を固定する。数列 $`b(n)`$ が与えられたとき、$`a(n)`$ を

```math
a(n) = b(n) + \sum_{k=1}^{n} \binom{mn+r}{k}\, a(n-k) \qquad (n \ge 0)
```

で定める（$`n=0`$ では和は空なので $`a(0)=b(0)`$）。ここで $`\binom{N}{k} = N(N-1)\cdots(N-k+1)/k!`$ は $`N`$ が負の整数でも使う一般の二項係数で、$`k<0`$ なら $`0`$ とする。

母関数を $`A(x)=\sum_{n\ge0} a(n)x^n`$、$`B(x)=\sum_{n\ge0} b(n)x^n`$ とおく。

**定理.** $`z = \dfrac{x}{(1+x)^m}`$ とおくと、形式的べき級数として

```math
A(x) = \frac{1-(m-1)x}{(1+x)^{r+1}} \Bigl( 2A(z) - B(z) \Bigr).
```

特に $`b(n)=1`$（$`B(z)=1/(1-z)`$）のとき

```math
A(x) = \frac{1-(m-1)x}{(1+x)^{r+1}} \left( 2A(z) - \frac{1}{1-z} \right).
```

## 2. OEIS の数列との対応（$`b(n)=1`$ の場合）

| 数列 | 漸化式の二項係数 | $`m`$ | $`r`$ | 関数方程式 |
|---|---|---|---|---|
| A402250 | $`\binom{2n-1}{k}`$ | 2 | $`-1`$ | $`A(x)=(1-x)\,(2A(z)-\frac{1}{1-z})`$, $`z=\frac{x}{(1+x)^2}`$ |
| A402251 | $`\binom{3n-1}{k}`$ | 3 | $`-1`$ | $`A(x)=(1-2x)\,(2A(z)-\frac{1}{1-z})`$, $`z=\frac{x}{(1+x)^3}`$ |
| A402252 | $`\binom{4n-1}{k}`$ | 4 | $`-1`$ | $`A(x)=(1-3x)\,(2A(z)-\frac{1}{1-z})`$, $`z=\frac{x}{(1+x)^4}`$ |
| A000629 | $`\binom{n}{k}`$ | 1 | $`0`$ | $`A(x)=\frac{1}{1+x}\,(2A(z)-\frac{1}{1-z})`$, $`z=\frac{x}{1+x}`$ |
| A402253 | $`\binom{2n}{k}`$ | 2 | $`0`$ | $`A(x)=\frac{1-x}{1+x}\,(2A(z)-\frac{1}{1-z})`$, $`z=\frac{x}{(1+x)^2}`$ |
| A402254 | $`\binom{3n}{k}`$ | 3 | $`0`$ | $`A(x)=\frac{1-2x}{1+x}\,(2A(z)-\frac{1}{1-z})`$, $`z=\frac{x}{(1+x)^3}`$ |
| A402255 | $`\binom{4n}{k}`$ | 4 | $`0`$ | $`A(x)=\frac{1-3x}{1+x}\,(2A(z)-\frac{1}{1-z})`$, $`z=\frac{x}{(1+x)^4}`$ |

$`r=-1`$ では係数 $`(1+x)^{r+1}`$ が $`1`$ になり、$`r=0`$ では $`1+x`$ になる。

## 3. 証明

### 3.1 漸化式の書き直し

漸化式の和に $`k=0`$ の項 $`\binom{mn+r}{0}a(n) = a(n)`$ を加えると、$`n \ge 0`$ で

```math
\sum_{k=0}^{n} \binom{mn+r}{k} a(n-k) = 2a(n) - b(n).
```

$`n=0`$ でも、左辺は $`\binom{r}{0}a(0)=a(0)`$、右辺は $`2a(0)-b(0)=a(0)`$ で成り立つ（$`\binom{r}{0}=1`$ は負の $`r`$ でも正しい）。$`j=n-k`$ とおくと

```math
2a(n) - b(n) = \sum_{j=0}^{n} \binom{mn+r}{n-j}\, a(j) \qquad (n\ge 0). \qquad (1)
```

(1) の両辺に $`z^n`$ を掛けて $`n \ge 0`$ で足すと

```math
2A(z) - B(z) = \sum_{j\ge0} a(j)\, S_j(z), \qquad S_j(z) = \sum_{n\ge0} \binom{mn+r}{n-j} z^n. \qquad (2)
```

$`z^n`$ の係数は $`j \le n`$ の有限和なので、和の順序を入れ替えてよい（$`n<j`$ では $`\binom{mn+r}{n-j}=0`$）。

### 3.2 補題

**補題.** $`z = x/(1+x)^m`$ のとき

```math
S_j(z) = \frac{x^j (1+x)^{r+1}}{1-(m-1)x}.
```

これは次の Lagrange–Bürmann の公式の特別な場合である。

**Lagrange–Bürmann の公式.** $`\varphi(t)`$ を $`\varphi(0)\ne0`$ の形式的べき級数とし、$`x=x(z)`$ を $`x = z\,\varphi(x)`$ の形式的べき級数解とする。任意の形式的べき級数（または形式的ローラン級数）$`F(t)`$ について

```math
\sum_{n} z^n\, [t^n]\bigl(F(t)\,\varphi(t)^n\bigr) = \frac{F(x)}{1 - z\,\varphi'(x)}.
```

*公式の証明.* 形式的留数 $`\mathop{\mathrm{Res}}\nolimits_z f = [z^{-1}] f`$ の変数変換の規則（$`z = z(t)`$ が位数 1 のとき $`\mathop{\mathrm{Res}}\nolimits_z f(z) = \mathop{\mathrm{Res}}\nolimits_t f(z(t))\, z'(t)`$）を使う。$`z = t/\varphi(t)`$ とおくと $`x(z(t)) = t`$ であり、

```math
z'(t) = \frac{\varphi(t) - t\varphi'(t)}{\varphi(t)^2}, \qquad
1 - z\,\varphi'(x) = 1 - \frac{t\varphi'(t)}{\varphi(t)} = \frac{\varphi(t) - t\varphi'(t)}{\varphi(t)}.
```

よって

```math
\begin{aligned}
[z^n]\frac{F(x)}{1-z\varphi'(x)} \\
&= \mathop{\mathrm{Res}}\nolimits_z \frac{z^{-n-1}F(x)}{1-z\varphi'(x)} \\
&= \mathop{\mathrm{Res}}\nolimits_t \left(\frac{t}{\varphi}\right)^{-n-1} F(t)\, \frac{\varphi}{\varphi - t\varphi'} \cdot \frac{\varphi - t\varphi'}{\varphi^2} \\
&= \mathop{\mathrm{Res}}\nolimits_t\, t^{-n-1} F(t)\, \varphi(t)^n \\
&= [t^n]\bigl(F(t)\varphi(t)^n\bigr). \qquad\square
\end{aligned}
```

*補題の証明.* $`\varphi(t) = (1+t)^m`$、$`F(t) = t^j (1+t)^r`$ とおく。

- $`x = z(1+x)^m`$ は $`z = x/(1+x)^m`$ と同じである。
- $`[t^n]\, t^j (1+t)^{mn+r} = \binom{mn+r}{n-j}`$ なので、公式の左辺はちょうど $`S_j(z)`$ である。

また、$`z(1+x)^m = x`$ を使うと

```math
1 - z\varphi'(x) = 1 - mz(1+x)^{m-1} = 1 - \frac{mx}{1+x} = \frac{1-(m-1)x}{1+x}.
```

したがって

```math
S_j(z) = x^j(1+x)^r \cdot \frac{1+x}{1-(m-1)x} = \frac{x^j(1+x)^{r+1}}{1-(m-1)x}. \qquad\square
```

### 3.3 定理の証明

補題を (2) に代入すると

```math
2A(z) - B(z) = \frac{(1+x)^{r+1}}{1-(m-1)x} \sum_{j\ge0} a(j)\,x^j = \frac{(1+x)^{r+1}}{1-(m-1)x}\, A(x).
```

両辺に $`\dfrac{1-(m-1)x}{(1+x)^{r+1}}`$ を掛ければ定理の式になる。$`\blacksquare`$

**形式的べき級数としての扱いについて.** $`z = x + O(x^2)`$ なので、$`A(z)`$、$`B(z)`$ を $`x`$ のべき級数に直す合成は意味を持つ。また (2) の右辺の和は、$`x^j`$ の項が $`x`$ の $`j`$ 次以上にしか効かないので、形式的べき級数として収束する。

## 4. 補足

### 4.1 二項係数の和としてよく知られた式

補題の $`j=0`$, $`r=0`$ の場合は、よく知られた

```math
\sum_{n\ge0}\binom{mn}{n} z^n = \frac{1+x}{1-(m-1)x}, \qquad z=\frac{x}{(1+x)^m}
```

である。$`r=-1`$ の場合 $`\sum_n \binom{mn-1}{n} z^n = \frac{1}{1-(m-1)x}`$ は、$`n\ge1`$ での $`\binom{mn-1}{n} = \frac{m-1}{m}\binom{mn}{n}`$ からも出る。

### 4.2 $`a(n)`$ を $`x`$ の級数から直接求める見方

定理の式は $`A(x)`$ を $`A(z)`$ で表しているが、$`z = x + O(x^2)`$ なので右辺の $`x^n`$ の係数は $`a(0),\dots,a(n)`$ だけで決まり、しかも $`a(n)`$ の係数は $`2-1=1`$ である。したがってこの式は $`a(n)`$ を逐次決める式にもなっていて、漸化式と同値である（$`b`$ が与えられたとき解は一意）。

### 4.3 数値による検算

$`m=0,1,\dots,5`$、$`r=-3,\dots,3`$、$`b(n) \in \{1,\ n+1,\ 2^n\}`$ のすべての組（計 126 通り）について、定理の両辺を有理数で $`x^{24}`$ の係数まで展開し、すべて一致することを確かめた。A402250〜A402255 については $`x^{39}`$ の係数まで一致を確かめた。

## 参考文献

- I. M. Gessel, Lagrange inversion, *J. Combin. Theory Ser. A* 144 (2016), 212–249.
