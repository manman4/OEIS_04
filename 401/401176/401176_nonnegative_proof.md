# A401176の非負性の証明

## 定義

$`\mathrm{spf}(k)`$ を合成数 $`k`$ の最小素因数とし、非負整数 $`n`$ に対して

```math
a(n)=n-\min_{k\gt n,\ k\text{ composite}} (k-\mathrm{spf}(k))
```

と定める。

最小値を取る対象は空でなく、その値は正整数なので、最小値は存在する。

## 主張

すべての整数 $`n\ge2`$ に対して、

```math
a(n)\ge0
```

が成り立つ。

## 証明

$`n\gt1`$ を整数とし、$`n`$ より大きい最初の偶数を $`k_0`$ とする。$`n`$ が偶数なら $`k_0=n+2`$、奇数なら $`k_0=n+1`$ なので、

```math
n\lt k_0\le n+2
```

である。また、$`k_0\ge4`$ であるため、$`k_0`$ は合成数であり、$`\mathrm{spf}(k_0)=2`$ となる。したがって、

```math
k_0-\mathrm{spf}(k_0)=k_0-2\le n.
```

$`k_0`$ は最小値を取る範囲に含まれるため、

```math
\min_{k\gt n,\ k\text{ composite}} (k-\mathrm{spf}(k))\le k_0-2\le n.
```

これを定義に代入すると、

```math
a(n)\ge n-n=0.
```

以上で証明された。

## 補足

奇数 $`n\ge3`$ では $`k_0=n+1`$ なので、同じ証明から $`a(n)\ge1`$ も分かる。

また、合成数 $`k`$ に対して $`\mathrm{spf}(k)\le k/2`$ かつ $`k\ge4`$ なので、

```math
k-\mathrm{spf}(k)\ge k/2\ge2.
```

$`k=4`$ で等号が成り立つため、$`n=0,1`$ のときの最小値はともに2であり、

```math
a(0)=-2,\quad a(1)=-1.
```

となる。

## 関連リンク

- [OEIS A401176](https://oeis.org/A401176)
- [Erdős Problem 463](https://www.erdosproblems.com/463)
