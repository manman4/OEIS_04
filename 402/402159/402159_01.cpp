/*
 * Erdős Problem #284
 * f(k) = 1 = 1/n_1 + 1/n_2 + ... + 1/n_k（n_1 < n_2 < ... < n_k、正の整数）と書けるときの
 *        n_1 の最大値。k = 3, 4, ..., K について計算し、"2, 2, 3, ..." の形で標準出力に
 *        1 項ずつ書き出す（ファイルは作らない）。k = 1 では 1 = 1/1、k = 2 では表し方がない
 *        （1/a + 1/b = 1 で a < b となる整数解はない）ので、k = 3 から始める。
 *
 * 使う事実（証明つき）:
 *  (1) 上界: n_1 = n なら、相異なる k 個の分母はすべて n 以上なので
 *        1 = Sum 1/n_i <= 1/n + 1/(n+1) + ... + 1/(n+k-1)。
 *      よって f(k) <= u(k) := (右辺 >= 1 を満たす最大の n)。
 *  (2) k >= 3 なら n_1 = 2 の表し方が存在する（1 = 1/2 + 1/3 + 1/6 から始め、最大の分母 d を
 *      1/d = 1/(d+1) + 1/(d(d+1)) で置き換えると、分母は相異なるまま項が 1 つ増える）。
 *      u(k) の上界から 2 まで「n_1 = n の表し方があるか」を調べ、最初の解を得た n が f(k)。
 *  (3) 探索（残りの値 r = p/q を、分母 lo 以上の相異なる c 個の単位分数の和で表せるか）:
 *      ・c >= 2 なら次の分母 d は 1/d < r より d > q/p、かつ d >= lo。
 *      ・c 個の和は c/d 以下なので c/d >= r が必要（d について単調、成り立たなければ以後も不可）。
 *      ・c 個の和は 1/d + ... + 1/(d+c-1) 以下なので、これが r 未満なら打ち切る（d について単調）。
 *        浮動小数点で打ち切り候補を選び、各逆数を 2^120 倍して整数に切り上げた
 *        上界を r と厳密に比較してから打ち切る。
 *      ・c = 1 なら r が 1/d（d >= lo）の形かを直接調べる。
 *  (4) 残り 2 項（c = 2）: 1/a + 1/b = p/q（a < b）は pab = q(a+b)、すなわち
 *        (pa - q)(pb - q) = q^2,  0 < pa - q < pb - q
 *      と同値。よって x = pa - q は q^2 の約数で x < q を満たし、逆にそのような x から
 *      a = (x+q)/p、b = (q^2/x + q)/p が整数なら解になる。
 *      r = 1 - (選んだ単位分数の和) の既約分母 q は、選んだ分母の最小公倍数を割り切るので、
 *      q の素因数は選んだ分母の素因数に含まれる。選んだ分母（2^62 以下）を Miller-Rabin
 *      （64 bit で決定的な底）と Pollard rho で素因数分解し、q を分解して約数を列挙する。
 *      b の整数性は、q^2/x を作らずに (q^2/x) mod p を素因数の積から計算して判定する
 *      （q^2 は 2^128 を超えうるため）。
 *      a の候補が少ない（20 万以下）ときは、a を 1 つずつ試す直接法を使う。
 *      分解で q が割り切れきらない場合（理論上起こらない）も直接法に戻る。
 *
 * 安全性: 分数は既約にして __int128 で計算する。必要な積が 2^120 を超える場合や
 *         選ぶ分母が 2^62 を超える場合は、その項を未確定として終了コード 2 で停止する。
 *
 * 検証: k <= 19 を、Python の Fraction（多倍長の厳密な有理数）で、事実 (4) を使わずに
 *       同じ探索をした結果と照合した。k <= 21 は事実 (4) を使わない版と、k <= 25 は
 *       直接法と約数法の切り替えの基準を変えた版（通る計算の経路が異なる）と照合した。
 *
 * コンパイル: g++ -O2 -std=c++17 -Wall -Wextra -Wpedantic -Werror 402159_01.cpp -o 402159_01
 * 実行:       ./402159_01 [K]   （K の既定値 30、3 <= K <= 200）
 */
#include <cerrno>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <algorithm>
#include <functional>
#include <unordered_map>
#include <utility>
#include <vector>

namespace {

__extension__ typedef __int128 i128;
__extension__ typedef unsigned __int128 u128;
const i128 LIMIT = static_cast<i128>(1) << 120;
const long long MAX_CHOSEN = 1LL << 62;

i128 gcd128(i128 a, i128 b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) { i128 t = a % b; a = b; b = t; }
    return a;
}

[[noreturn]] void search_stop(const char *reason) {
    std::fprintf(stderr, "\nCurrent term unresolved: %s.\n", reason);
    std::exit(2);
}

// a*b を範囲検査つきで計算（a, b >= 0）
i128 mul_checked(i128 a, i128 b) {
    if (a != 0 && b > LIMIT / a) search_stop("integer product exceeds 2^120");
    return a * b;
}

// 1/d + 1/(d+1) + ... + 1/(d+c-1) を long double で
long double harmonic_block(long long d, int c) {
    long double s = 0;
    for (int i = c - 1; i >= 0; i--) s += 1.0L / static_cast<long double>(d + i);
    return s;
}

// Compare positive fractions (with nonnegative numerators) without cross products.
bool fraction_less(u128 a, u128 b, u128 c, u128 d) {
    bool reversed = false;
    for (;;) {
        u128 lhs = a / b, rhs = c / d;
        if (lhs != rhs) return reversed ? lhs > rhs : lhs < rhs;
        a %= b;
        c %= d;
        if (a == 0 || c == 0) return reversed ? c == 0 && a != 0 : a == 0 && c != 0;
        // Removing equal integer parts preserves order. Taking reciprocals reverses it.
        std::swap(a, b);
        std::swap(c, d);
        reversed = !reversed;
    }
}

bool harmonic_upper_below(long long d, int count, i128 p, i128 q) {
    const u128 scale = static_cast<u128>(LIMIT);
    u128 upper = 0;
    // Round each reciprocal upward. count <= 200, so upper <= 200 * 2^120 < 2^128.
    for (int i = 0; i < count; ++i) {
        u128 denominator = static_cast<u128>(d + i);
        upper += (scale + denominator - 1) / denominator;
    }
    return fraction_less(upper, scale, static_cast<u128>(p), static_cast<u128>(q));
}

// ---------- 64 bit 整数の素因数分解（Miller-Rabin + Pollard rho） ----------
typedef unsigned long long u64;

u64 mulmod(u64 a, u64 b, u64 m) { return static_cast<u64>(static_cast<u128>(a) * b % m); }
u64 powmod(u64 a, u64 e, u64 m) {
    u64 r = 1 % m;
    a %= m;
    while (e) { if (e & 1) r = mulmod(r, a, m); a = mulmod(a, a, m); e >>= 1; }
    return r;
}
// 64 bit で決定的な Miller-Rabin（底 2..37 の素数）
bool is_prime64(u64 n) {
    if (n < 2) return false;
    static const u64 small[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (u64 p : small) { if (n % p == 0) return n == p; }
    u64 d = n - 1; int s = 0;
    while ((d & 1) == 0) { d >>= 1; s++; }
    for (u64 a : small) {
        u64 x = powmod(a, d, n);
        if (x == 1 || x == n - 1) continue;
        bool comp = true;
        for (int i = 1; i < s; i++) { x = mulmod(x, x, n); if (x == n - 1) { comp = false; break; } }
        if (comp) return false;
    }
    return true;
}
// a*b mod m（m < 2^121）。256 bit を使わず、倍加と加算で計算する。
u128 mulmod128(u128 a, u128 b, u128 m) {
    u128 r = 0;
    a %= m;
    while (b) {
        if (b & 1) { r += a; if (r >= m) r -= m; }
        a += a; if (a >= m) a -= m;
        b >>= 1;
    }
    return r;
}
u64 gcd64(u64 a, u64 b) { while (b) { u64 t = a % b; a = b; b = t; } return a; }
u64 rho(u64 n) {
    if (n % 2 == 0) return 2;
    for (u64 c = 1; c < n; c++) {
        u64 x = 2, y = 2, d = 1;
        auto f = [&](u64 v) { return (mulmod(v, v, n) + c) % n; };
        while (d == 1) { x = f(x); y = f(f(y)); d = gcd64(x > y ? x - y : y - x, n); }
        if (d != n) return d;
    }
    search_stop("factorization did not produce a divisor");
}
void factor_rec(u64 n, std::vector<u64> &out) {
    if (n == 1) return;
    if (is_prime64(n)) { out.push_back(n); return; }
    for (u64 p = 2; p < 1000; p++) if (n % p == 0) { out.push_back(p); while (n % p == 0) n /= p; factor_rec(n, out); return; }
    u64 d = rho(n);
    factor_rec(d, out);
    factor_rec(n / d, out);
}
// n の相異なる素因数（キャッシュつき）
const std::vector<u64> &prime_factors(u64 n) {
    static std::unordered_map<u64, std::vector<u64>> cache;
    auto it = cache.find(n);
    if (it != cache.end()) return it->second;
    std::vector<u64> v;
    factor_rec(n, v);
    std::sort(v.begin(), v.end());
    v.erase(std::unique(v.begin(), v.end()), v.end());
    return cache.emplace(n, std::move(v)).first->second;
}

// 選んだ分母（n_1 から順に）
long long chosen[256];
int depth = 0;

// 事実 (4): 1/a + 1/b = p/q（a < b、a >= lo）の解があるか
bool two_terms(i128 p, i128 q, long long lo) {
    // a > q/p（1/a < r）かつ a < 2q/p（a < b）
    i128 alo = q / p + 1;
    if (alo < lo) alo = lo;
    i128 ahi = (2 * q - 1) / p;          // a <= floor((2q-1)/p) <=> pa < 2q
    if (alo > ahi) return false;
    const i128 DIRECT = 200000;
    bool use_divisors = (ahi - alo > DIRECT);
    if (use_divisors) {
        // q の素因数は選んだ分母の素因数に含まれる（事実 (4)）
        std::vector<u64> ps;
        for (int i = 0; i < depth; i++) {
            const std::vector<u64> &f = prime_factors(static_cast<u64>(chosen[i]));
            ps.insert(ps.end(), f.begin(), f.end());
        }
        std::sort(ps.begin(), ps.end());
        ps.erase(std::unique(ps.begin(), ps.end()), ps.end());
        std::vector<std::pair<u64, int>> fac;
        i128 rest = q;
        for (u64 pr : ps) {
            int e = 0;
            while (rest % pr == 0) { rest /= pr; e++; }
            if (e) fac.push_back({pr, 2 * e});   // q^2 の指数
        }
        if (rest != 1) use_divisors = false;      // 起こらないはずだが、念のため直接法へ
        // 約数の個数 Prod(2e+1) が直接法の候補数より十分少ないときだけ約数法を使う
        if (use_divisors) {
            long double ndiv = 1;
            for (auto &pe : fac) ndiv *= static_cast<long double>(pe.second + 1);
            if (ndiv * 8 > static_cast<long double>(ahi - alo + 1)) use_divisors = false;
        }
        if (use_divisors) {
            // q^2 の約数 x（x < q）を列挙する。y = q^2/x は 2^128 を超えうるので、
            // y を直接作らず、(y + q) が p で割り切れるかを y mod p で判定する。
            const u128 P = static_cast<u128>(p);
            const u128 qmodp = static_cast<u128>(q) % P;
            bool found = false;
            std::vector<int> ex(fac.size(), 0);   // x の各素因数の指数
            std::function<void(size_t, i128)> rec = [&](size_t idx, i128 x) {
                if (found) return;
                if (idx == fac.size()) {
                    if (x >= q) return;
                    if ((x + q) % p != 0) return;
                    i128 a = (x + q) / p;
                    if (a < lo) return;
                    // y mod p = Prod pr^(2e - ex) mod p
                    u128 ym = 1 % P;
                    for (size_t i = 0; i < fac.size(); i++)
                        for (int t = 0; t < fac[i].second - ex[i]; t++)
                            ym = mulmod128(ym, static_cast<u128>(fac[i].first) % P, P);
                    if ((ym + qmodp) % P != 0) return;
                    found = true;                 // b = (y+q)/p は整数で b > a（x < q < y）
                    return;
                }
                i128 v = x;
                for (int e = 0; e <= fac[idx].second; e++) {
                    if (v >= q) break;            // x < q の約数だけ（素因数は掛けるほど増える）
                    ex[idx] = e;
                    rec(idx + 1, v);
                    if (found) return;
                    if (e == fac[idx].second || v > (q - 1) / fac[idx].first) break;
                    v *= static_cast<i128>(fac[idx].first);
                }
                ex[idx] = 0;
            };
            rec(0, 1);
            return found;
        }
    }
    // 直接法: 各 a について 1/b = r - 1/a = (pa - q)/(qa) が単位分数か
    for (i128 a = alo; a <= ahi; a++) {
        i128 x = mul_checked(p, a) - q;
        i128 qa = mul_checked(q, a);
        if (qa % x == 0) return true;            // b = qa/x > a（x < q のため）
    }
    return false;
}

// r = p/q（既約、p > 0）を、分母 lo 以上の相異なる c 個の単位分数の和で表せるか
bool representable(i128 p, i128 q, int c, long long lo) {
    if (c == 1) return p == 1 && q >= lo;
    if (c == 2) return two_terms(p, q, lo);
    i128 first = std::max(static_cast<i128>(lo), q / p + 1);
    // Since c <= 200 and q <= 2^120, the product fits in unsigned 128 bits.
    u128 last = static_cast<u128>(c) * static_cast<u128>(q) / static_cast<u128>(p);
    if (static_cast<u128>(first) > last) return false;
    if (first > MAX_CHOSEN) search_stop("a candidate denominator exceeds 2^62");
    long long d = static_cast<long long>(first);
    const long double r = static_cast<long double>(p) / static_cast<long double>(q);
    for (; static_cast<u128>(d) <= last; ++d) {
        if (d > MAX_CHOSEN) search_stop("a candidate denominator exceeds 2^62");
        if (harmonic_block(d, c) + 1e-9L < r && harmonic_upper_below(d, c, p, q)) return false;
        // r - 1/d = (p*d - q) / (q*d)
        i128 np = mul_checked(p, d) - q;
        i128 nq = mul_checked(q, d);
        i128 g = gcd128(np, nq);
        chosen[depth++] = d;
        bool ok = representable(np / g, nq / g, c - 1, d + 1);
        depth--;
        if (ok) return true;
    }
    return false;
}

bool parse_limit(const char *text, int *value) {
    if (!*text) return false;
    for (const char *p = text; *p; p++)
        if (*p < '0' || *p > '9') return false;
    errno = 0;
    char *end;
    long parsed = std::strtol(text, &end, 10);
    if (errno == ERANGE || *end || parsed < 3 || parsed > 200) return false;
    *value = static_cast<int>(parsed);
    return true;
}

}  // namespace

int main(int argc, char **argv) {
    int K = 30;
    if (argc == 2 && (!std::strcmp(argv[1], "--help") || !std::strcmp(argv[1], "-h"))) {
        std::printf("Usage: %s [K] (3 <= K <= 200; default 30)\n", argv[0]);
        return 0;
    }
    if (argc > 2 || (argc == 2 && !parse_limit(argv[1], &K))) {
        std::fprintf(stderr, "Usage: %s [K]; K must be a decimal integer in 3..200.\n", argv[0]);
        return 1;
    }
    for (int k = 3; k <= K; k++) {
        // Since 1 <= k/n_1, k is an upper bound even if rounding leaves a candidate.
        long long u = 1;
        for (long long n = 2; n <= k; ++n) {
            if (harmonic_upper_below(n, k, 1, 1)) break;
            u = n;
        }
        long long found = -1;
        for (long long n1 = u; n1 >= 2; n1--) {    // 事実 (2)
            // 1 - 1/n1 = (n1-1)/n1 を、n1+1 以上の相異なる k-1 個の単位分数で
            depth = 0;
            chosen[depth++] = n1;
            bool ok = representable(n1 - 1, n1, k - 1, n1 + 1);
            depth = 0;
            if (ok) { found = n1; break; }
        }
        if (found < 0) {
            std::fprintf(stderr, "\nNo representation found for k=%d (should not happen).\n", k);
            return 1;
        }
        if (std::printf(k == 3 ? "%lld" : ", %lld", found) < 0 || std::fflush(stdout) != 0) {
            std::perror("write standard output");
            return 1;
        }
    }
    if (std::printf("\n") < 0 || std::fflush(stdout) != 0) {
        std::perror("write standard output");
        return 1;
    }
    return 0;
}
