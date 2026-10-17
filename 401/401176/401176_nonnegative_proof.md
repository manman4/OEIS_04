# A401176：n ≥ 2 における非負性の証明

## 定義

\(\operatorname{spf}(k)\) を合成数 \(k\) の最小素因数とし、

\[
a(n)=n-\min_{\substack{k>n\\k\text{ は合成数}}}
\bigl(k-\operatorname{spf}(k)\bigr)
\]

と定める。

最小値を取る対象は空でなく、その値は正整数なので、最小値は存在する。

## 主張

すべての整数 \(n\ge2\) に対して、

\[
\boxed{a(n)\ge0}
\]

が成り立つ。

## 証明

\(n\) より大きい最初の偶数を \(k_0\) とする。すなわち、

\[
k_0=
\begin{cases}
n+2 & (n\text{ が偶数}),\\
n+1 & (n\text{ が奇数}).
\end{cases}
\]

\(n\ge2\) より \(k_0\ge4\) である。したがって \(k_0\) は合成数で、
\(\operatorname{spf}(k_0)=2\) となる。よって、

\[
k_0-\operatorname{spf}(k_0)=
\begin{cases}
n & (n\text{ が偶数}),\\
n-1 & (n\text{ が奇数})
\end{cases}
\le n.
\]

\(k_0\) は最小値を取る範囲に含まれるため、

\[
\min_{\substack{k>n\\k\text{ は合成数}}}
\bigl(k-\operatorname{spf}(k)\bigr)
\le k_0-\operatorname{spf}(k_0)\le n.
\]

これを定義に代入すると、

\[
a(n)\ge n-n=0.
\]

以上で証明された。

## 補足

同じ証明から、奇数 \(n\ge3\) では \(a(n)\ge1\) も分かる。

また、\(n=0,1\) では、合成数 \(k\) に対して
\(\operatorname{spf}(k)\le k/2\) かつ \(k\ge4\) なので、

\[
k-\operatorname{spf}(k)\ge k/2\ge2.
\]

\(k=4\) で等号が成り立つため、\(a(0)=-2\)、\(a(1)=-1\) となる。

## 関連リンク

- [OEIS A401176](https://oeis.org/A401176)
- [Erdős Problem 463](https://www.erdosproblems.com/463)
