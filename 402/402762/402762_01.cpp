/*
 * Erdős Problem #525  (A402762)
 * a(n) = 係数がすべて ±1 の n 次多項式 f(z) = c_0 + c_1 z + ... + c_n z^n（2^(n+1) 個）のうち、
 *        単位円上のすべての z で |f(z)| >= 1 となるものの個数。
 *        （問題 525 は、どこかで |f(z)| < 1 となる f が o(2^n) 個を除くすべてか、と問う。
 *          a(n) はその例外の個数。）
 * n = 0..N を計算し、"2, 0, 4, 0, 12, ..." の形で 1 項ずつ標準出力に書き出す（ファイルは作らない）。
 *
 * 使う事実（どれも証明つき、結果を変えない）:
 *  (0) 浮動小数点の前提: double は IEEE 754 の倍精度で、四則演算は最近接への丸め（u = 2^-53）。
 *      頼るのはこれだけで、標準ライブラリの三角関数などの精度には頼らない（cos, sin は自前の
 *      Taylor 級数 expi() で計算し、誤差の上界を証明する）。前提はコンパイル時（is_iec559、
 *      FLT_EVAL_METHOD == 0、-ffast-math でない）と実行時（丸めモード）に確かめ、満たさなければ止める。
 *      FMA への縮約があっても誤差の評価は成り立つ。
 *  (1) 対称性: f -> -f と f(z) -> f(-z) は |f| の単位円上の値の集合を変えない。
 *      n >= 1 では、この 2 つが生成する 4 つの変換で移り合う多項式はちょうど 4 個で
 *      （c_0 の符号と c_1 の符号の組がすべて現れる）、条件は 4 個で共通。よって c_0 = c_1 = +1 の
 *      2^(n-1) 個（「正規形」と呼ぶ）だけを調べて 4 倍する。n = 0 では f = ±1 で |f| = 1 なので a(0) = 2。
 *  (2) 実係数なので |f(e^{-iθ})| = |f(e^{iθ})|。
 *        h(θ) = |f(e^{iθ})|^2 - 1 = n + 2 Sum_{d=1..n} A_d cos(dθ),  A_d = Sum_j c_j c_{j+d}
 *      （|f|^2 = Sum_{j,k} c_j c_k e^{i(j-k)θ}、c_j^2 = 1）。2cos(dθ) = D_d(2cos θ)
 *      （D_d(y) = 2T_d(y/2)、D_0 = 2, D_1 = y, D_{d+1} = y D_d - D_{d-1}、整数係数）なので、
 *      y = 2cos θ として g(y) = n + Sum A_d D_d(y) は整数係数の多項式で、条件は「[-2, 2] 上で g >= 0」と同値。
 *  (3) 厳密な判定: g = Prod g_i^i（Yun の平方因子分解）とし、奇数重複度の因子の積 O を作る。
 *      g が (-2, 2) で符号を変えるのは O の根（奇数重複度の根）だけ。
 *        ・O が (-2, 2) に根をもてば、g はそこで符号を変えるので負になる点がある → 条件不成立。
 *        ・もたなければ g は (-2, 2) で符号を変えないので、g(t) != 0 となる内部の点 t で
 *          g(t) > 0 なら条件成立、g(t) < 0 なら不成立（端点は連続性で決まる）。
 *      O の (-2, 2) の根の数は、O から因子 y - 2, y + 2 を除いてから Sturm 列で数える。
 *      すべて多倍長整数で計算する（浮動小数点を使わない）。
 *  (4) 高速な除外（1 段目）: θ_j = πj/M（j = 0..M、M は 16(n+1) 以上の 2 の冪）で f(e^{iθ_j}) を倍精度で求め、
 *      |f|^2 < 1 - 10^-3 となる点があれば条件不成立とする。係数を下位 7 個（c_2..c_8）と上位に分け、
 *      f = (下位の和) + (上位の和) とする。下位の和は 128 x (M+1) の表（キャッシュに乗る大きさ）にし、
 *      上位の和は上位の組を Gray 符号の順に動かして、係数 1 個の変化分 ±2 z^i を足して更新する。
 *      誤差: z_j^i は powers() で作り、誤差は 2·10^-13·i 以下（Sum_{i<=30} で 9.3·10^-11 以下）。表と、上位の和を
 *      直接計算し直すとき（256 組の区切りの先頭と 1024 組ごと）の和の丸めは 10^-13 未満。その後の更新は
 *      高々 1023 回で、1 回の丸めは 4·10^-15 未満（|和| <= 31）。よって f の誤差は 10^-10 未満、
 *      |f| <= n+1 <= 31 より |f|^2 の誤差は 10^-8 未満。10^-3 の余裕があるので、計算した |f|^2 が 1 - 10^-3 未満なら
 *      真の値は 1 未満で、条件を満たす多項式を誤って除くことはない。
 *      2 段目（事実 (5) で決まらなかったものだけ）: 4097 点 θ_k = πk/4096 で、z = expi(θ_k)（誤差 < 1.5·10^-13）
 *      での f を Horner 法で計算して同じ判定をする。Horner 法の丸めは 1 段あたり 3u·31 + u·31 < 1.4·10^-14 で
 *      合計 4.4·10^-13 未満、z の誤差による f の誤差は Sum i·1.5·10^-13·1.01 < 7.1·10^-11 なので、
 *      f の誤差は 10^-10 未満で同じ結論になる。
 *  (5) 高速な「成立」の保証（fast_check の前のコメント）: 特別な点 θ = 0, π/3, π/2, 2π/3, π での
 *      h, h', h'' の符号を整数で正確に求め、h = 0 となる点の近くは 3 階微分の上界 L3 = 2 Sum d^3 |A_d|
 *      による Taylor 評価で h >= 0 を示す。残りの区間は 2 次の Taylor 展開と丸め誤差の上界で h > 0 を示す
 *      （まず cos, sin の表を使う固定の格子で、だめな所だけ二分する）。
 *      示せなかったものだけを 2 段目と (3) に回す。この関数が「不成立」と答えるのは、整数で正確に
 *      求めた符号から h < 0 となる点の存在が分かる場合だけ。
 *  (6) 反転の対称性: f*(z) = z^n f(1/z)（係数の並びを逆にしたもの）も単位円上で |f*(z)| = |f(z̄)| = |f(z)|
 *      （実係数）なので条件は共通。正規形 c に対し、f* を (1) の変換で正規形に直したものを r(c) とすると
 *        r(c)_j = c_n c_{n-j} (c_n c_{n-1})^j
 *      で、r は正規形の上の対合（r(r(c)) = c）。よって正規形で条件を満たすものの個数は
 *        #{r(c) = c} + 2 #{c < r(c)}（c は c_j = -1 を 1 とするビット列の整数として比べる）
 *      なので、r(c) < c のものは調べず、r(c) = c なら重み 1、c < r(c) なら重み 2 で数える。
 *  (7) 並列化: 上位の組をスレッドで分担し、最後に重みつきの数を合計する（結果はスレッド数によらない）。
 *
 * 検証:
 *  ・n <= 12 を、Python（sympy）の別の方法（g の実根を厳密に分離し、隣り合う根の間の有理数点で
 *    g の符号を厳密に調べる）で、すべての多項式について判定した結果と照合した。
 *  ・n <= 15 を、(4)(5)(6) を使わずすべての正規形を (3) で判定する版と照合した。
 *  ・n <= 21 で、1 段目を通ったすべての代表について、(5) の答え（成立／不成立）が (3) と一致することを確かめた。
 *  ・n <= 26 を、(6)(7) と表・格子の工夫を入れる前の版（1 スレッド）と照合した。
 *  ・n <= 24 で、スレッド数 1, 3, 7 の結果が一致することを確かめた。
 *  ・AddressSanitizer / UndefinedBehaviorSanitizer つきで n <= 18、ThreadSanitizer つきで n <= 17 を実行した。
 *  ・-march=native -ffp-contract=fast（FMA への縮約あり）でも n <= 24 の結果は同じ。
 *  ・expi(), powers() の誤差を long double の cosl, sinl と比べると 10^-15 程度で、証明した上界より十分小さい
 *    （正しさの根拠ではなく、実装の確認として）。
 *  ・n = 0..27: 2, 0, 4, 0, 12, 8, 28, 16, 108, 56, 324, 416, 964, 784, 3960, 3984, 11236, 14168,
 *    37516, 49040, 142932, 160504, 473800, 756560, 1700192, 2296008, 6417748, 8923760
 *    （2 スレッドで n <= 27 が約 18 秒。n が 2 増えるごとに約 3.5 倍で、n <= 30 は数分の見込み）。
 *
 * コンパイル: g++ -O2 -std=c++17 -Wall -Wextra -Wpedantic -Werror -pthread 402762_01.cpp -o 402762_01
 * 実行:       ./402762_01 [N [THREADS]]   （N の既定値 20、0 <= N <= 30。THREADS の既定値は CPU 数、1..256）
 */
#include <atomic>
#include <cerrno>
#include <cmath>
#include <cfenv>
#include <cfloat>
#include <limits>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <thread>
#include <utility>
#include <vector>

namespace {

// ---------------- 多倍長整数（符号つき、基数 2^32） ----------------
struct Big {
    bool neg = false;
    std::vector<uint32_t> m;          // 下位から。0 は空
};

void trim(Big &a) {
    while (!a.m.empty() && a.m.back() == 0) a.m.pop_back();
    if (a.m.empty()) a.neg = false;
}
Big from_ll(long long v) {
    Big a;
    unsigned long long u;
    if (v < 0) { a.neg = true; u = 0ULL - static_cast<unsigned long long>(v); } else u = static_cast<unsigned long long>(v);
    while (u) { a.m.push_back(static_cast<uint32_t>(u)); u >>= 32; }
    trim(a);
    return a;
}
bool is_zero(const Big &a) { return a.m.empty(); }
int sgn(const Big &a) { return is_zero(a) ? 0 : (a.neg ? -1 : 1); }
int cmp_abs(const Big &a, const Big &b) {
    if (a.m.size() != b.m.size()) return a.m.size() < b.m.size() ? -1 : 1;
    for (size_t i = a.m.size(); i-- > 0;)
        if (a.m[i] != b.m[i]) return a.m[i] < b.m[i] ? -1 : 1;
    return 0;
}
std::vector<uint32_t> add_abs(const std::vector<uint32_t> &a, const std::vector<uint32_t> &b) {
    std::vector<uint32_t> r(std::max(a.size(), b.size()) + 1, 0);
    uint64_t carry = 0;
    for (size_t i = 0; i < r.size(); i++) {
        uint64_t s = carry;
        if (i < a.size()) s += a[i];
        if (i < b.size()) s += b[i];
        r[i] = static_cast<uint32_t>(s);
        carry = s >> 32;
    }
    return r;
}
// |a| >= |b| を仮定
std::vector<uint32_t> sub_abs(const std::vector<uint32_t> &a, const std::vector<uint32_t> &b) {
    std::vector<uint32_t> r(a.size(), 0);
    int64_t borrow = 0;
    for (size_t i = 0; i < a.size(); i++) {
        int64_t s = static_cast<int64_t>(a[i]) - borrow - (i < b.size() ? static_cast<int64_t>(b[i]) : 0);
        if (s < 0) { s += (int64_t)1 << 32; borrow = 1; } else borrow = 0;
        r[i] = static_cast<uint32_t>(s);
    }
    return r;
}
Big add(const Big &a, const Big &b) {
    Big r;
    if (a.neg == b.neg) { r.m = add_abs(a.m, b.m); r.neg = a.neg; }
    else if (cmp_abs(a, b) >= 0) { r.m = sub_abs(a.m, b.m); r.neg = a.neg; }
    else { r.m = sub_abs(b.m, a.m); r.neg = b.neg; }
    trim(r);
    return r;
}
Big neg(Big a) { if (!is_zero(a)) a.neg = !a.neg; return a; }
Big sub(const Big &a, const Big &b) { return add(a, neg(b)); }
Big mul(const Big &a, const Big &b) {
    Big r;
    if (is_zero(a) || is_zero(b)) return r;
    r.m.assign(a.m.size() + b.m.size(), 0);
    for (size_t i = 0; i < a.m.size(); i++) {
        uint64_t carry = 0;
        for (size_t j = 0; j < b.m.size(); j++) {
            uint64_t cur = static_cast<uint64_t>(a.m[i]) * b.m[j] + r.m[i + j] + carry;
            r.m[i + j] = static_cast<uint32_t>(cur);
            carry = cur >> 32;
        }
        size_t k = i + b.m.size();
        while (carry) {
            uint64_t cur = static_cast<uint64_t>(r.m[k]) + carry;
            r.m[k] = static_cast<uint32_t>(cur);
            carry = cur >> 32;
            k++;
        }
    }
    r.neg = a.neg != b.neg;
    trim(r);
    return r;
}
// |a| を |b| で割る（Knuth のアルゴリズム D）。q = 商、r = 余り（どちらも非負）
void divmod_abs(const Big &a, const Big &b, Big &q, Big &r) {
    q = Big(); r = Big();
    if (is_zero(b)) { std::fprintf(stderr, "Internal error: division by zero.\n"); std::exit(3); }
    if (cmp_abs(a, b) < 0) { r.m = a.m; trim(r); return; }
    if (b.m.size() == 1) {
        uint64_t rem = 0, d = b.m[0];
        q.m.assign(a.m.size(), 0);
        for (size_t i = a.m.size(); i-- > 0;) {
            uint64_t cur = (rem << 32) | a.m[i];
            q.m[i] = static_cast<uint32_t>(cur / d);
            rem = cur % d;
        }
        trim(q);
        r = from_ll(static_cast<long long>(rem));
        return;
    }
    int s = __builtin_clz(b.m.back());
    std::vector<uint32_t> v(b.m.size()), u(a.m.size() + 1, 0);
    for (size_t i = b.m.size(); i-- > 0;)
        v[i] = (b.m[i] << s) | (s && i ? static_cast<uint32_t>(static_cast<uint64_t>(b.m[i - 1]) >> (32 - s)) : 0);
    u[a.m.size()] = s ? static_cast<uint32_t>(static_cast<uint64_t>(a.m.back()) >> (32 - s)) : 0;
    for (size_t i = a.m.size(); i-- > 0;)
        u[i] = (a.m[i] << s) | (s && i ? static_cast<uint32_t>(static_cast<uint64_t>(a.m[i - 1]) >> (32 - s)) : 0);
    size_t nlen = v.size(), mlen = a.m.size() - nlen;
    q.m.assign(mlen + 1, 0);
    for (size_t jj = mlen + 1; jj-- > 0;) {
        size_t j = jj;
        uint64_t num = (static_cast<uint64_t>(u[j + nlen]) << 32) | u[j + nlen - 1];
        uint64_t qhat = num / v[nlen - 1], rhat = num % v[nlen - 1];
        while (qhat >= (1ULL << 32) || qhat * v[nlen - 2] > ((rhat << 32) | u[j + nlen - 2])) {
            qhat--; rhat += v[nlen - 1];
            if (rhat >= (1ULL << 32)) break;
        }
        int64_t borrow = 0;
        uint64_t carry = 0;
        for (size_t i = 0; i < nlen; i++) {
            uint64_t p = qhat * v[i] + carry;
            carry = p >> 32;
            int64_t t = static_cast<int64_t>(u[i + j]) - borrow - static_cast<int64_t>(p & 0xffffffffULL);
            if (t < 0) { t += (int64_t)1 << 32; borrow = 1; } else borrow = 0;
            u[i + j] = static_cast<uint32_t>(t);
        }
        int64_t t = static_cast<int64_t>(u[j + nlen]) - borrow - static_cast<int64_t>(carry);
        if (t < 0) {
            u[j + nlen] = static_cast<uint32_t>(t + ((int64_t)1 << 32));
            qhat--;
            uint64_t c = 0;
            for (size_t i = 0; i < nlen; i++) {
                uint64_t sum = static_cast<uint64_t>(u[i + j]) + v[i] + c;
                u[i + j] = static_cast<uint32_t>(sum);
                c = sum >> 32;
            }
            u[j + nlen] = static_cast<uint32_t>(static_cast<uint64_t>(u[j + nlen]) + c);
        } else {
            u[j + nlen] = static_cast<uint32_t>(t);
        }
        q.m[j] = static_cast<uint32_t>(qhat);
    }
    trim(q);
    r.m.assign(nlen, 0);
    for (size_t i = 0; i < nlen; i++)
        r.m[i] = (u[i] >> s) | (s ? static_cast<uint32_t>(static_cast<uint64_t>(u[i + 1]) << (32 - s)) : 0);
    trim(r);
}
// 割り切れることを確かめて a / b（符号つき）
Big div_exact(const Big &a, const Big &b) {
    Big q, r;
    divmod_abs(a, b, q, r);
    if (!is_zero(r)) { std::fprintf(stderr, "Internal error: inexact division.\n"); std::exit(3); }
    q.neg = !is_zero(q) && (a.neg != b.neg);
    return q;
}
Big gcd_abs(Big a, Big b) {
    a.neg = false; b.neg = false;
    while (!is_zero(b)) { Big q, r; divmod_abs(a, b, q, r); a = b; b = r; }
    return a;
}

// ---------------- 整数係数多項式（係数は下位から） ----------------
typedef std::vector<Big> Poly;

void ptrim(Poly &p) { while (!p.empty() && is_zero(p.back())) p.pop_back(); }
int deg(const Poly &p) { return static_cast<int>(p.size()) - 1; }   // 0 多項式は -1
Poly deriv(const Poly &p) {
    Poly r;
    for (size_t i = 1; i < p.size(); i++) r.push_back(mul(p[i], from_ll(static_cast<long long>(i))));
    ptrim(r);
    return r;
}
Big content(const Poly &p) {
    Big g;
    for (const Big &c : p) g = gcd_abs(g, c);
    return g;
}
// 正の内容で割る（符号は保つ）
Poly prim(const Poly &p) {
    if (p.empty()) return p;
    Big c = content(p);
    Poly r;
    for (const Big &x : p) r.push_back(div_exact(x, c));
    return r;
}
// 正の定数 lc(b)^2 の冪を掛けた擬剰余（符号を保つため |lc| の偶数乗ではなく、lc^(δ+1) の符号を補正）
Poly prem_pos(Poly a, const Poly &b) {
    int db = deg(b);
    const Big &lb = b.back();
    int delta = deg(a) - db;
    if (delta < 0) return a;
    int k = delta + 1;                       // lc(b)^k を掛けることになる
    while (deg(a) >= db && !a.empty()) {
        int shift = deg(a) - db;
        Big la = a.back();
        for (Big &x : a) x = mul(x, lb);
        for (int i = 0; i <= db; i++) a[i + shift] = sub(a[i + shift], mul(la, b[i]));
        ptrim(a);
        k--;
    }
    for (; k > 0; k--) for (Big &x : a) x = mul(x, lb);    // 合計で lc(b)^(δ+1) 倍
    if (lb.neg && ((delta + 1) & 1)) for (Big &x : a) x = neg(x);   // 掛けた定数を正にする
    return a;
}
Poly pgcd(Poly a, Poly b) {
    a = prim(a); b = prim(b);
    while (!b.empty()) {
        Poly r = prim(prem_pos(a, b));
        a = b; b = r;
    }
    if (!a.empty() && a.back().neg) for (Big &x : a) x = neg(x);
    return a;
}
// a を原始多項式 b で割る（割り切れることを確かめる）
Poly pdiv_exact(Poly a, const Poly &b) {
    int db = deg(b);
    if (deg(a) < db) { if (a.empty()) return Poly(); std::fprintf(stderr, "Internal error: poly division.\n"); std::exit(3); }
    Poly q(static_cast<size_t>(deg(a) - db + 1));
    while (!a.empty() && deg(a) >= db) {
        int shift = deg(a) - db;
        Big c = div_exact(a.back(), b.back());
        q[static_cast<size_t>(shift)] = c;
        for (int i = 0; i <= db; i++) a[static_cast<size_t>(i + shift)] = sub(a[static_cast<size_t>(i + shift)], mul(c, b[static_cast<size_t>(i)]));
        ptrim(a);
    }
    if (!a.empty()) { std::fprintf(stderr, "Internal error: inexact poly division.\n"); std::exit(3); }
    ptrim(q);
    return q;
}
Poly pmul(const Poly &a, const Poly &b) {
    if (a.empty() || b.empty()) return Poly();
    Poly r(a.size() + b.size() - 1);
    for (size_t i = 0; i < a.size(); i++)
        for (size_t j = 0; j < b.size(); j++) r[i + j] = add(r[i + j], mul(a[i], b[j]));
    ptrim(r);
    return r;
}
// p(num / 2^e) の符号（分母を払った値の符号）
int sign_at_dyadic(const Poly &p, long long num, int e) {
    Big s, pw = from_ll(1), N = from_ll(num);
    int d = deg(p);
    for (int i = 0; i <= d; i++) {
        Big term = mul(p[static_cast<size_t>(i)], pw);
        Big scale = from_ll(1);
        for (int t = 0; t < (d - i) * e; t++) scale = mul(scale, from_ll(2));
        s = add(s, mul(term, scale));
        pw = mul(pw, N);
    }
    return sgn(s);
}
int sign_at_int(const Poly &p, long long x) { return sign_at_dyadic(p, x, 0); }

// Sturm 列で、平方因子のない多項式 O の (-2, 2) の根の数（O(±2) != 0 を仮定）
int sturm_roots_open(const Poly &O) {
    if (deg(O) <= 0) return 0;
    std::vector<Poly> S;
    S.push_back(prim(O));
    S.push_back(prim(deriv(O)));
    while (!S.back().empty() && deg(S.back()) > 0) {
        Poly r = prem_pos(S[S.size() - 2], S.back());
        for (Big &x : r) x = neg(x);
        ptrim(r);
        if (r.empty()) break;
        S.push_back(prim(r));
    }
    auto changes = [&](long long x) {
        int c = 0, last = 0;
        for (const Poly &p : S) {
            int sg = sign_at_int(p, x);
            if (sg == 0) continue;
            if (last != 0 && sg != last) c++;
            last = sg;
        }
        return c;
    };
    return changes(-2) - changes(2);
}

// 事実 (3): 整数係数 g について、[-2, 2] 上で g >= 0 か
bool nonneg_on_interval(const Poly &g0) {
    Poly g = g0;
    ptrim(g);
    if (g.empty()) return true;                       // g = 0（n = 0 の場合のみ）
    if (deg(g) == 0) return sgn(g[0]) >= 0;
    // Yun の平方因子分解: g = c * Prod a_i^i
    Poly f = prim(g);                                  // 正の内容で割るので符号は g と同じ
    Poly fp = deriv(f);
    Poly a0 = pgcd(f, fp);
    Poly b = pdiv_exact(f, a0);                        // b = f / gcd(f, f'),  c = f' / gcd(f, f')
    Poly c = pdiv_exact(fp, a0);
    Poly odd; odd.push_back(from_ll(1));              // 奇数重複度の因子の積
    for (int i = 1; deg(b) > 0; i++) {
        Poly bp = deriv(b);
        Poly d = c;                                    // d = c - b'
        if (d.size() < bp.size()) d.resize(bp.size());
        for (size_t t = 0; t < bp.size(); t++) d[t] = sub(d[t], bp[t]);
        ptrim(d);
        Poly ai = pgcd(b, d);                          // d = 0 なら ai = b（残り全部が重複度 i）
        if (i & 1) odd = pmul(odd, ai);
        b = pdiv_exact(b, ai);
        c = d.empty() ? Poly() : pdiv_exact(d, ai);
        if (c.empty() && deg(b) > 0) {                // 起こらないはずだが安全のため
            std::fprintf(stderr, "Internal error: Yun factorization.\n"); std::exit(3);
        }
    }
    // O から因子 y - 2, y + 2 を除く（端点の根は符号の判定に関係しない）
    Poly ym2{from_ll(-2), from_ll(1)}, yp2{from_ll(2), from_ll(1)};
    while (deg(odd) > 0 && sign_at_int(odd, 2) == 0) odd = pdiv_exact(odd, ym2);
    while (deg(odd) > 0 && sign_at_int(odd, -2) == 0) odd = pdiv_exact(odd, yp2);
    if (sturm_roots_open(odd) > 0) return false;      // (-2, 2) で符号が変わる
    // 符号は (-2, 2) で一定。g(t) != 0 となる点 t = num/2^e（|t| < 2）を探して符号を見る
    for (int e = 1; e <= 40; e++)
        for (long long num = -(2LL << e) + 1; num < (2LL << e); num += 2) {
            int s = sign_at_dyadic(g, num, e);
            if (s != 0) return s > 0;
        }
    std::fprintf(stderr, "Internal error: no nonzero point found.\n");
    std::exit(3);
}

// ---------------- 本体 ----------------
long long Dk[32][32];                                  // D_d(y) = 2T_d(y/2) の係数

bool exact_check(int n, const int *c) {
    long long A[32] = {0};
    for (int d = 1; d <= n; d++) for (int j = 0; j + d <= n; j++) A[d] += c[j] * c[j + d];
    long long gc[32] = {0};                            // g(y) = n + Sum A_d D_d(y)
    gc[0] = n;
    for (int d = 1; d <= n; d++) for (int i = 0; i <= d; i++) gc[i] += A[d] * Dk[d][i];
    Poly g;
    for (int i = 0; i <= n; i++) g.push_back(from_ll(gc[i]));
    return nonneg_on_interval(g);
}

// ---------------- 誤差の上界が証明できる浮動小数点計算 ----------------
// 前提（事実 (0)）: double は IEEE 754 の倍精度で、四則演算は最近接への丸め（単位丸め誤差 u = 2^-53）。
//   標準ライブラリの三角関数などの精度には頼らない。前提はコンパイル時と実行時（main の先頭）に確かめる。
//   a*b+c が FMA に縮約されても、下の誤差評価はそのまま成り立つ（丸めが 1 回減るだけ）。
static_assert(std::numeric_limits<double>::is_iec559, "IEEE 754 double is required");
#if !defined(FLT_EVAL_METHOD) || FLT_EVAL_METHOD != 0
#error "FLT_EVAL_METHOD must be 0 (no extended-precision intermediates)"
#endif
#ifdef __FAST_MATH__
#error "Do not compile with -ffast-math."
#endif

struct Cx { double re, im; };
inline Cx cadd(Cx x, Cx y) { return Cx{x.re + y.re, x.im + y.im}; }
inline Cx cscale(double s, Cx x) { return Cx{s * x.re, s * x.im}; }   // s = ±1, ±2 なら丸めなし
// 積: 各成分の誤差は 2u(|ac|+|bd|) 以下（FMA の有無によらない）。よって |誤差| <= 2√2 u|x||y| < 3u|x||y|
inline Cx cmul(Cx x, Cx y) { return Cx{x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re}; }
inline double norm2(Cx x) { return x.re * x.re + x.im * x.im; }

// e^{it}（0 <= t <= 3.2）を Taylor 級数で計算する。|expi(t) - e^{it}| < 1.5·10^-13。
//   cos, sin の各 22 項 t^j/j! を、前の項に t^2 を掛けて整数 (j-1)j で割って作る（整数は double で正確）。
//   第 k 項の相対誤差は (1+u)^{3k} - 1 <= 3.01ku、22 項の和の丸めは 21.1u Sum|項| 以下。
//   t <= 3.2 で Sum|項| <= cosh 3.2 < 12.3、Sum k|項| <= (t/2)cosh t < 19.7 なので、各成分の誤差は
//   (3.01·19.7 + 21.1·12.3·1.01) u < 330u < 10^-13。打ち切り誤差は交代級数の次の項 3.2^44/44! < 10^-32 以下。
Cx expi(double t) {
    if (!(t >= 0.0 && t <= 3.2)) { std::fprintf(stderr, "Internal error: expi argument out of range.\n"); std::exit(3); }
    const double t2 = t * t;
    double term = 1.0, c = 1.0;
    for (int k = 1; k <= 21; k++) { term = term * t2 / ((2.0 * k - 1.0) * (2.0 * k)); c += (k & 1) ? -term : term; }
    term = t;
    double s = t;
    for (int k = 1; k <= 21; k++) { term = term * t2 / ((2.0 * k) * (2.0 * k + 1.0)); s += (k & 1) ? -term : term; }
    return Cx{c, s};
}

// p[d] ≈ e^{idt}（d = 0..n <= 30）を e^{it} の掛け算で作る。|p[d] - e^{idt}| <= 2·10^-13·d。
//   帰納法: e_{d+1} <= e_d |p_1| + e_1 + 3u |p_d||p_1| <= e_d (1 + 1.5·10^-13) + 1.5·10^-13 + 3.4·10^-16。
void powers(double t, int n, Cx *p) {
    p[0] = Cx{1.0, 0.0};
    if (n >= 1) p[1] = expi(t);
    for (int d = 2; d <= n; d++) p[d] = cmul(p[d - 1], p[1]);
}

// 事実 (5) で使う固定の格子: [0, π] を K 個の小区間 [a_k, b_k] に分け、中心 m_k での cos(d m_k), sin(d m_k) を表にする
struct Grid {
    int n = 0, K = 0;
    std::vector<double> a, b, m, r;                    // r_k: [a_k, b_k] ⊂ [m_k - r_k, m_k + r_k]
    std::vector<double> cs, sn;                        // cs[k*(n+1)+d] = cos(d m_k), sn = sin(d m_k)
};

void build_grid(Grid &G, int n) {
    G.n = n;
    G.K = static_cast<int>(M_PI * n) + 1;              // 幅は 1/n 未満
    G.a.resize(G.K); G.b.resize(G.K); G.m.resize(G.K); G.r.resize(G.K);
    G.cs.assign(static_cast<size_t>(G.K) * (n + 1), 0.0);
    G.sn.assign(static_cast<size_t>(G.K) * (n + 1), 0.0);
    for (int k = 0; k < G.K; k++) {
        // 隣どうしは同じ式で端点を共有する（a_0 = 0、b_{K-1} = M_PI。M_PI と π の差 < 1.3·10^-16 は r の余裕 10^-15 で覆う）
        double a = (k == 0) ? 0.0 : M_PI * k / G.K, b = (k == G.K - 1) ? M_PI : M_PI * (k + 1) / G.K;
        double m = 0.5 * (a + b);
        G.a[k] = a; G.b[k] = b; G.m[k] = m;
        G.r[k] = std::max(m - a, b - m) + 1e-15;
        Cx p[32];
        powers(m, n, p);                               // 誤差 <= 2·10^-13·d
        for (int d = 0; d <= n; d++) {
            G.cs[static_cast<size_t>(k) * (n + 1) + d] = p[d].re;
            G.sn[static_cast<size_t>(k) * (n + 1) + d] = p[d].im;
        }
    }
}

// 事実 (5): 浮動小数点と整数による「成立」の保証（保証できなければ -1 を返し、事実 (3) に回す）。
//   h(θ) = n + 2 Sum A_d cos(dθ) について |h'''(θ)| <= L3 = 2 Sum d^3 |A_d|。
//   (a) 特別な点 p = kπ/6（k = 0, 2, 3, 4, 6）では 2cos(dp) は整数、sin(dp) は整数と
//       正の定数（1 または √3/2）の積なので、2h(p)、h'(p) の符号、2h''(p) を整数で正確に求める。
//         h(p) < 0、または h(p) = 0 かつ h'(p) != 0、または h(p) = h'(p) = 0 かつ h''(p) < 0 なら、
//         p の近くで h < 0 となる点があるので 0（不成立）を返す（整数による厳密な判定）。
//         h(p) = h'(p) = 0, h''(p) > 0 なら、Taylor の定理により |u| <= u_p = 1.5 h''(p)/L3 で
//         h(p+u) >= h''(p)u^2/2 - L3|u|^3/6 >= h''(p)u^2/4 >= 0。この範囲（0.99 倍に縮めたもの）を除外する。
//         h(p) = h'(p) = h''(p) = 0 なら -1。
//   (b) 残りを小区間 [m-r, m+r] で覆い、h(m), h'(m), h''(m) を倍精度で計算して
//         h(m+t) >= min_{|t|<=r} (h(m) + h'(m)t + h''(m)t^2/2) - (丸め誤差) - L3 r^3/6
//       が正なら、その小区間で h > 0。小区間はまず固定の格子（表の cos, sin を使う）で、
//       除外範囲にかかる格子や正にならない格子は、その部分を二分しながら調べる（数と深さに上限）。
//       丸め誤差（事実 (0) の前提だけを使う）: cos(dm), sin(dm) は powers() で作り、誤差 <= 2·10^-13·30 = 6·10^-12。
//       よって h(m), h'(m), h''(m) の誤差は、和の丸め（<= 62u·係数の絶対値の和）も含めて
//       それぞれ S0, S1, S2（係数の絶対値の和）の 6.1·10^-12 倍以下。r <= 1/(2n) + 10^-15 なので
//       L3 r^3/6 <= S0 で、2 次式の最小値と最後の引き算の丸め（相対 10u 程度）は 10^-14 (S0 + S1 r + S2 r^2)
//       以下。合わせて余裕 10^-11 (S0 + S1 r + S2 r^2) で覆う。
int fast_check(int n, const long long *A, const Grid &G) {
    static const int cos2[12] = {2, 0, 1, 0, -1, 0, -2, 0, -1, 0, 1, 0};   // 2cos(aπ/6)（a は偶数か 3 の倍数のみ使う）
    static const int sig[12] = {0, 0, 1, 1, 1, 0, 0, 0, -1, -1, -1, 0};     // sin(aπ/6) の符号（同上）
    static const int ks[5] = {0, 2, 3, 4, 6};
    double L3 = 0, S0 = n, S1 = 0, S2 = 0;
    double w0[32], w1[32], w2[32];                     // 2A_d, -2dA_d, -2d^2 A_d
    for (int d = 1; d <= n; d++) {
        double ad = static_cast<double>(A[d]), a = std::fabs(ad);
        L3 += 2.0 * d * d * d * a; S0 += 2.0 * a; S1 += 2.0 * d * a; S2 += 2.0 * d * d * a;
        w0[d] = 2.0 * ad; w1[d] = -2.0 * d * ad; w2[d] = -2.0 * d * d * ad;
    }
    if (L3 <= 0) return -1;
    double exlo[5], exhi[5];
    int nex = 0;
    for (int k : ks) {
        long long H2 = 2LL * n, D = 0, C2 = 0;
        for (int d = 1; d <= n; d++) {
            int a = (d * k) % 12;
            H2 += 2 * A[d] * cos2[a];
            D += d * A[d] * sig[a];
            C2 -= 2LL * d * d * A[d] * cos2[a];
        }
        // 2h(p) = H2、h'(p) は -D の正の定数倍、2h''(p) = C2
        if (H2 < 0) return 0;
        if (H2 > 0) continue;
        if (D != 0) return 0;
        if (C2 < 0) return 0;
        if (C2 == 0) return -1;
        double u = 0.99 * 1.5 * (static_cast<double>(C2) / 2.0) / L3;
        double pc = M_PI * k / 6.0;
        exlo[nex] = pc - u; exhi[nex] = pc + u; nex++;
    }
    // 除外範囲を左端の昇順に並べる（高々 5 個）
    for (int i = 1; i < nex; i++)
        for (int j = i; j > 0 && exlo[j] < exlo[j - 1]; j--) { std::swap(exlo[j], exlo[j - 1]); std::swap(exhi[j], exhi[j - 1]); }

    // 小区間 [m-r, m+r] で、2 次の Taylor 評価の下界が正か
    auto cell_ok = [&](double c0, double c1, double c2, double r) {
        double q = std::min(c0 - c1 * r + c2 * r * r / 2, c0 + c1 * r + c2 * r * r / 2);
        if (c2 > 0 && std::fabs(c1) < c2 * r) q = std::min(q, c0 - c1 * c1 / (2 * c2));
        return q - 1e-11 * (S0 + S1 * r + S2 * r * r) - L3 * r * r * r / 6.0 > 0;
    };
    struct Cell { double a, b; int depth; };
    Cell stk[128];
    int budget = 4000;
    // [lo, hi] を二分しながら調べる（e^{idm} は掛け算で作る）
    auto check_range = [&](double lo, double hi) -> bool {
        if (hi <= lo) return true;
        int sp = 0;
        stk[sp++] = Cell{lo, hi, 0};
        while (sp > 0) {
            Cell cl = stk[--sp];
            if (--budget < 0) return false;
            // m は [a, b] 内。差の丸め誤差（<= 4.5·10^-16）を 10^-15 で覆って、[a, b] ⊂ [m-r, m+r] とする
            double m = 0.5 * (cl.a + cl.b), r = std::max(m - cl.a, cl.b - m) + 1e-15;
            double c0 = n, c1 = 0, c2 = 0;
            Cx p[32];
            powers(m, n, p);                           // 誤差 <= 2·10^-13·d
            for (int d = 1; d <= n; d++) { c0 += w0[d] * p[d].re; c1 += w1[d] * p[d].im; c2 += w2[d] * p[d].re; }
            if (cell_ok(c0, c1, c2, r)) continue;
            if (cl.depth >= 50 || cl.b - cl.a < 1e-10 || sp + 2 > 128) return false;
            stk[sp++] = Cell{cl.a, m, cl.depth + 1};
            stk[sp++] = Cell{m, cl.b, cl.depth + 1};
        }
        return true;
    };
    for (int k = 0; k < G.K; k++) {
        const double a = G.a[k], b = G.b[k];
        bool touches = false;
        for (int i = 0; i < nex; i++)
            if (exhi[i] > a && exlo[i] < b) { touches = true; break; }
        if (touches) {
            // 除外範囲を除いた部分だけを二分で調べる
            double cur = a;
            for (int i = 0; i < nex && cur < b; i++) {
                if (exhi[i] <= cur) continue;
                if (exlo[i] > cur && !check_range(cur, std::min(exlo[i], b))) return -1;
                if (exhi[i] > cur) cur = exhi[i];
            }
            if (cur < b && !check_range(cur, b)) return -1;
            continue;
        }
        const double *cs = &G.cs[static_cast<size_t>(k) * (n + 1)], *sn = &G.sn[static_cast<size_t>(k) * (n + 1)];
        double c0 = n, c1 = 0, c2 = 0;
        for (int d = 1; d <= n; d++) { c0 += w0[d] * cs[d]; c1 += w1[d] * sn[d]; c2 += w2[d] * cs[d]; }
        if (cell_ok(c0, c1, c2, G.r[k])) continue;
        if (--budget < 0 || !check_range(a, b)) return -1;
    }
    return 1;
}

bool parse_uint(const char *text, long lo, long hi, int *value) {
    if (!*text) return false;
    for (const char *p = text; *p; p++)
        if (*p < '0' || *p > '9') return false;
    errno = 0;
    char *end;
    long parsed = std::strtol(text, &end, 10);
    if (errno == ERANGE || *end || parsed < lo || parsed > hi) return false;
    *value = static_cast<int>(parsed);
    return true;
}

// 64 bit のビット順を逆にする
inline uint64_t bitrev64(uint64_t x) {
    x = ((x >> 1) & 0x5555555555555555ULL) | ((x & 0x5555555555555555ULL) << 1);
    x = ((x >> 2) & 0x3333333333333333ULL) | ((x & 0x3333333333333333ULL) << 2);
    x = ((x >> 4) & 0x0F0F0F0F0F0F0F0FULL) | ((x & 0x0F0F0F0F0F0F0F0FULL) << 4);
    x = ((x >> 8) & 0x00FF00FF00FF00FFULL) | ((x & 0x00FF00FF00FF00FFULL) << 8);
    x = ((x >> 16) & 0x0000FFFF0000FFFFULL) | ((x & 0x0000FFFF0000FFFFULL) << 16);
    return (x >> 32) | (x << 32);
}

// 事実 (6): c_0 = c_1 = +1 の多項式（ビット j が 1 ⇔ c_j = -1）の反転の代表 r(c)
//   r(c)_j = c_n c_{n-j} (c_n c_{n-1})^j、ビットでは b'_j = b_n ^ b_{n-j} ^ (j (b_n ^ b_{n-1}) mod 2)
inline uint64_t rev_rep(uint64_t B, int n) {
    const uint64_t all = (n == 63) ? ~0ULL : ((1ULL << (n + 1)) - 1);
    uint64_t R = bitrev64(B) >> (63 - n);
    const uint64_t bn = (B >> n) & 1, bn1 = (B >> (n - 1)) & 1;
    if (bn) R ^= all;
    if (bn ^ bn1) R ^= 0xAAAAAAAAAAAAAAAAULL & all;
    return R;
}

// n 次の a(n)/4 を、スレッド数 nthreads で計算する（n >= 1）
long long count_quarter(int n, int nthreads) {
    const int FINE = 4096;                             // 2 段目の標本点 θ_k = π k / FINE（k = 0..FINE）
    // 2 段目の点を、粗い点から細かい点への順（ビット反転順）に並べる（除外が早く決まりやすい）
    static std::vector<Cx> fine;
    if (fine.empty()) {
        std::vector<int> ks;
        ks.push_back(0); ks.push_back(FINE);
        for (int step = FINE; step > 1; step >>= 1)
            for (int k = step / 2; k < FINE; k += step) ks.push_back(k);
        for (int k : ks) fine.push_back(expi(M_PI * k / FINE));                  // 誤差 < 1.5·10^-13
    }
    // 標本点 θ_j = π j / M（j = 0..M、M は 2 の冪で M >= 16(n+1)）
    int M = 1;
    while (M < 16 * (n + 1)) M <<= 1;
    const int P = M + 1;
    // 調べる順の初期値: 粗い点から細かい点へ（ビット反転順）。各スレッドで、除外に使った点を前へ移す
    std::vector<int> order0;
    order0.push_back(0); order0.push_back(M);
    for (int step = M; step > 1; step >>= 1)
        for (int j = step / 2; j < M; j += step) order0.push_back(j);
    // 事実 (4): 係数を下位 L 個（c_2..c_{L+1}）と上位 H 個（c_{L+2}..c_n）に分け、f(z_j) = lo[lm][j] + hi[j]。
    const int F = n - 1;                               // 動かす係数 c_2..c_n の個数
    const int L = F < 7 ? F : 7, H = F - L;            // 下位の表は 128 x P 個（キャッシュに乗る大きさ）
    const size_t NL = static_cast<size_t>(1) << L;
    std::vector<Cx> zpow(static_cast<size_t>(P) * (n + 1));                    // z_j^i（誤差 <= 2·10^-13·i）
    for (int j = 0; j < P; j++) powers(M_PI * j / M, n, &zpow[static_cast<size_t>(j) * (n + 1)]);
    std::vector<Cx> lo(NL * static_cast<size_t>(P));                           // lo[lm][j]
    for (size_t lm = 0; lm < NL; lm++)
        for (int j = 0; j < P; j++) {
            const Cx *z = &zpow[static_cast<size_t>(j) * (n + 1)];
            Cx s = cadd(z[0], z[1]);                                             // c_0 = c_1 = +1
            for (int t = 0; t < L; t++) s = cadd(s, cscale((lm >> t) & 1 ? -1.0 : 1.0, z[2 + t]));
            lo[lm * P + j] = s;
        }
    Grid grid;
    build_grid(grid, n);
    const unsigned long long NH = 1ULL << H;
    const unsigned long long CHUNK = 256;              // スレッドに渡す上位の組の数（Gray 符号の区切り）
    std::atomic<unsigned long long> next(0);
    std::vector<long long> partial(static_cast<size_t>(nthreads), 0);

    auto worker = [&](int tid) {
        std::vector<Cx> hi(static_cast<size_t>(P));
        std::vector<int> order = order0;
        int c[32];
        long long good = 0;                            // 重み（事実 (6)）つきの数
        const double thr = 1.0 - 1e-3;
        for (;;) {
            const unsigned long long i0 = next.fetch_add(CHUNK);
            if (i0 >= NH) break;
            const unsigned long long i1 = (i0 + CHUNK < NH) ? i0 + CHUNK : NH;
            for (unsigned long long idx = i0; idx < i1; idx++) {
                const unsigned long long hm = idx ^ (idx >> 1);                     // Gray 符号
                if (idx == i0 || (idx & 1023) == 0) {
                    // 上位の和を直接計算する（区切りの先頭と 1024 組ごと）
                    for (int j = 0; j < P; j++) {
                        const Cx *z = &zpow[static_cast<size_t>(j) * (n + 1)];
                        Cx s{0.0, 0.0};
                        for (int t = 0; t < H; t++) s = cadd(s, cscale((hm >> t) & 1 ? -1.0 : 1.0, z[2 + L + t]));
                        hi[static_cast<size_t>(j)] = s;
                    }
                } else {
                    // 直前の組と 1 個の係数だけ違う: hi += (新しい符号 - 古い符号) z^i
                    const int t = __builtin_ctzll(idx);
                    const double dlt = ((hm >> t) & 1) ? -2.0 : 2.0;
                    for (int j = 0; j < P; j++)
                        hi[static_cast<size_t>(j)] = cadd(hi[static_cast<size_t>(j)], cscale(dlt, zpow[static_cast<size_t>(j) * (n + 1) + 2 + L + t]));
                }
                for (size_t lm = 0; lm < NL; lm++) {
                    const Cx *row = &lo[lm * P];
                    bool rejected = false;
                    for (size_t q = 0; q < order.size(); q++) {
                        const int j = order[q];
                        if (norm2(cadd(row[j], hi[static_cast<size_t>(j)])) < thr) {
                            if (q > 0) std::swap(order[q], order[q / 2]);           // よく効く点を前へ
                            rejected = true;
                            break;
                        }
                    }
                    if (rejected) continue;
                    // 事実 (6): 反転の代表と比べて重みを決める
                    const uint64_t Bm = (static_cast<uint64_t>(lm) << 2) | (static_cast<uint64_t>(hm) << (2 + L));
                    const uint64_t Rm = rev_rep(Bm, n);
                    if (Rm < Bm) continue;
                    const int w = (Rm == Bm) ? 1 : 2;
                    for (int i = 0; i <= n; i++) c[i] = ((Bm >> i) & 1) ? -1 : 1;
                    long long A[32] = {0};
                    for (int d = 1; d <= n; d++) for (int j = 0; j + d <= n; j++) A[d] += c[j] * c[j + d];
                    const int fc = fast_check(n, A, grid);   // 事実 (5)
                    if (fc == 1) { good += w; continue; }
                    if (fc == 0) continue;
                    // 事実 (4) の 2 段目: FINE+1 点で Horner 法により f を直接計算する
                    rejected = false;
                    for (size_t k = 0; k < fine.size() && !rejected; k++) {
                        const Cx z = fine[k];
                        Cx v{0.0, 0.0};
                        for (int i = n; i >= 0; i--) { v = cmul(v, z); v.re += static_cast<double>(c[i]); }
                        if (norm2(v) < thr) rejected = true;
                    }
                    if (rejected) continue;
                    if (exact_check(n, c)) good += w;  // 事実 (2)(3)
                }
            }
        }
        partial[static_cast<size_t>(tid)] = good;
    };
    std::vector<std::thread> pool;
    for (int t = 1; t < nthreads; t++) pool.emplace_back(worker, t);
    worker(0);
    for (auto &th : pool) th.join();
    long long total = 0;
    for (long long v : partial) total += v;
    return total;
}

}  // namespace

int main(int argc, char **argv) {
    int N = 20;
    unsigned hc = std::thread::hardware_concurrency();
    int T = (hc >= 1 && hc <= 256) ? static_cast<int>(hc) : 1;
    if (argc == 2 && (!std::strcmp(argv[1], "--help") || !std::strcmp(argv[1], "-h"))) {
        std::printf("Usage: %s [N [THREADS]] (0 <= N <= 30, default 20; 1 <= THREADS <= 256, default: number of CPUs)\n", argv[0]);
        return 0;
    }
    if (argc > 3 || (argc >= 2 && !parse_uint(argv[1], 0, 30, &N)) || (argc == 3 && !parse_uint(argv[2], 1, 256, &T))) {
        std::fprintf(stderr, "Usage: %s [N [THREADS]]; N in 0..30, THREADS in 1..256.\n", argv[0]);
        return 1;
    }
    // D_d(y) = 2T_d(y/2)（2cos(dθ) = D_d(2cos θ)）: D_0 = 2, D_1 = y, D_{d+1} = y D_d - D_{d-1}
    // （係数の絶対値は 2^d 以下で、64 bit に十分収まる）
    if (std::fegetround() != FE_TONEAREST) {          // 事実 (0) の前提
        std::fprintf(stderr, "Rounding mode must be round-to-nearest.\n");
        return 1;
    }
    std::memset(Dk, 0, sizeof Dk);
    Dk[0][0] = 2; Dk[1][1] = 1;
    for (int d = 1; d + 1 < 32; d++)
        for (int i = 0; i < 32; i++)
            Dk[d + 1][i] = (i > 0 ? Dk[d][i - 1] : 0) - Dk[d - 1][i];

    for (int n = 0; n <= N; n++) {
        long long count;
        if (n == 0) count = 2;                         // 事実 (1): f = ±1
        else count = 4 * count_quarter(n, T);          // 事実 (1)
        if (std::printf(n == 0 ? "%lld" : ", %lld", count) < 0 || std::fflush(stdout) != 0) {
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
