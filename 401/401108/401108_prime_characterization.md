# A401108：a(n) = n と素数性の同値性

## 定義と主張

[OEIS A401108](https://oeis.org/A401108) は、整数 $`n\ge 2`$ に対して次のように定義される（2026年10月15日確認）。

```math
M(n,k)=\max\{d\in\mathbb{Z}:1\le d\le n,\ d\mid\binom{n}{k}\},\qquad a(n)=\min_{1\le k\lt n}M(n,k).
```

各集合は $`1`$ を含む有限集合なので、最大値と最小値は存在する。証明する主張は次のとおりである。

```math
a(n)=n\quad\Longleftrightarrow\quad n\text{ は素数}.
```

## 二項係数の整除性への帰着

定義から常に $`M(n,k)\le n`$ であり、次が成り立つ。

```math
M(n,k)=n\quad\Longleftrightarrow\quad n\mid\binom{n}{k}.
```

したがって、これらの最小値が $`n`$ となることは、すべてが $`n`$ となることと同値である。つまり、

```math
a(n)=n\quad\Longleftrightarrow\quad n\mid\binom{n}{k}\text{ がすべての }1\le k\lt n\text{ について成り立つ}.
```

## 素数ならば a(n) = n

$`n=p`$ が素数であるとする。任意の $`1\le k\lt p`$ に対し、二項係数の恒等式から

```math
k\binom{p}{k}=p\binom{p-1}{k-1}.
```

右辺は $`p`$ の倍数である。一方、$`k`$ は $`p`$ と互いに素なので、$`p\mid\binom{p}{k}`$ が従う。これはすべての $`k`$ について成り立つため、$`a(p)=p`$ である。

## 合成数ならば a(n) は n より小さい

$`n`$ が合成数であるとし、その素因数を一つ $`p`$ とする。このとき $`1\lt p\lt n`$ なので、定義中の候補として $`k=p`$ を選べる。

まず、$`\binom{n-1}{p-1}`$ は $`p`$ で割り切れない。実際、

```math
(p-1)!\binom{n-1}{p-1}=\prod_{j=1}^{p-1}(n-j)\equiv\prod_{j=1}^{p-1}(-j)=(-1)^{p-1}(p-1)!\pmod p.
```

$`(p-1)!`$ は $`p`$ と互いに素なので、合同式でこれを消去でき、

```math
\binom{n-1}{p-1}\equiv(-1)^{p-1}\not\equiv 0\pmod p.
```

ここで、もし $`n\mid\binom{n}{p}`$ なら、ある整数 $`t`$ を用いて $`\binom{n}{p}=nt`$ と書ける。恒等式

```math
p\binom{n}{p}=n\binom{n-1}{p-1}
```

に代入して $`n`$ を消去すると、

```math
\binom{n-1}{p-1}=pt
```

となり、先ほどの合同式に矛盾する。よって $`n\nmid\binom{n}{p}`$ であり、$`M(n,p)\lt n`$ である。したがって、

```math
a(n)\le M(n,p)\lt n.
```

以上より、すべての整数 $`n\ge 2`$ について、$`a(n)=n`$ であることと $`n`$ が素数であることは同値である。□

## OEIS 短い英語証明

Since $`M(n,k)\le n`$, we have $`a(n)=n`$ if and only if $`n\mid\binom{n}{k}`$ for every $`1\le k\lt n`$. If $`n`$ is prime, this divisibility follows from $`k\binom{n}{k}=n\binom{n-1}{k-1}`$ and the coprimality of $`k`$ and $`n`$. If $`n`$ is composite, choose a prime divisor $`p\lt n`$. Reduction of the product formula modulo $`p`$ gives $`\binom{n-1}{p-1}\equiv(-1)^{p-1}\not\equiv0\pmod p`$. The identity $`p\binom{n}{p}=n\binom{n-1}{p-1}`$ then implies $`n\nmid\binom{n}{p}`$, since otherwise $`\binom{n-1}{p-1}`$ would be divisible by $`p`$. Hence $`a(n)\lt n`$.
