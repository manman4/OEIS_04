/*
 * Erdős Problem #319  (A402839)
 * a(N) = 次を満たす A ⊆ {1..N} の大きさ |A| の最大値（なければ 0）:
 *        符号 δ: A -> {-1, 1} があって Sum_{n in A} δ_n/n = 0 で、空でない真部分集合 A' ⊊ A では
 *        Sum_{n in A'} δ_n/n != 0（「最小の 0 和集合」と呼ぶ）。
 * N = 1..NMAX を計算し、"0, 0, 0, 0, 0, 4, ..." の形で 1 項ずつ標準出力に書き出す（ファイルは作らない）。
 *
 * 記法: 符号つき集合を δ ∈ {-1, 0, 1}^N で表す（A = δ の台）。δ が 0 和なら -δ も 0 和で、最小性も同じ。
 *
 * 使う事実（どれも証明つき、結果を変えない）:
 *  (1) a(N) >= a(N-1)（{1..N-1} の集合は {1..N} の集合でもある）。a(N) > a(N-1) となるのは、最大のものが
 *      N を含むときだけ。よって N を含む最小の 0 和集合で、大きさが a(N-1)+1 以上のものだけを探せばよく、
 *      全体の符号を反転して δ_N = +1 としてよい。
 *  (2) 最小性の言い換え: N を含む 0 和集合 Z が最小でない ⇔ Z∖{N} の空でない部分集合（符号は Z のまま）で
 *      和が 0 のものがある。
 *      （⇒）真部分集合 Y が 0 和なら Z∖Y も空でない 0 和で、Y と Z∖Y の一方は N を含まない。（⇐）明らか。
 *  (3) 使えない元の除去: 集合 U（最初は {1..N}）の元だけからなる 0 和集合を考え、素数 p について
 *      e = max_{n in U} v_p(n)、層 T = {n in U : v_p(n) = e}、L = lcm(U) とする。和に L を掛けると、
 *      T 以外の項 δ_n L/n は p で割り切れ、T の項は L/n = (L/p^e)/(n/p^e) なので
 *        Sum_{n in T} δ_n (n/p^e)^{-1} ≡ 0 (mod p)
 *      が必要。これを満たす δ|_T が 0 だけなら T の元はどの 0 和集合にも現れないので U から除き、
 *      変化がなくなるまで繰り返す（除いた元を使う集合はもともとないので、結果は変わらない）。
 *  (4) 和は L = lcm(U) を分母にした整数 S = Sum δ_n w_n（w_n = L/n）で正確に計算する（__int128、
 *      L·|U| < 2^125 を確かめる）。
 *  (5) 探索の順と枝刈り: 元を、N を先頭に、残りを最大素因数の大きい順に並べて符号 {+, -, 0} を決める。
 *      各素数 q について M_q = q^{v_q(L)} とし、表 maxc[q][i][r] =「位置 i 以降の元で和 ≡ r (mod M_q) と
 *      するときに使える元の最大個数（作れなければ -1）」を作る。途中の和 S について、
 *      r = -S mod M_q で maxc が -1 なら S = 0 にできない（S = 0 なら S ≡ 0 (mod M_q)）ので枝を切り、
 *      （選んだ数）+ maxc < （目標の大きさ）でも切る。さらに |S| > （残りの w の和）でも切る。
 *  (6) 末尾の t 個（t <= 13）は、符号つき部分集合の和を表にして並べておき、和が -S のものを
 *      二分探索で引く（半分全列挙）。表は和が等しいものの中で大きさの降順なので、先頭の大きさで切れる。
 *  (7) 末尾の表からは、空でない 0 和の部分集合を含む符号つき部分集合を前もって除く（N を含まないので、
 *      (2) よりそれを使う Z は最小でない）。
 *  (8) 最小性は元を 1 個加えるたびに調べる: 選んだ元（N 以外）の列に元 x を加えるとき、
 *      「x を含む空でない 0 和の部分集合ができる」⇔「それまでの列の部分集合で和が -(x の符号つきの w) の
 *      ものがある」。できるなら (2) よりその先はどれも最小でないので枝を切る。どの段階でもできなければ
 *      Z∖{N} の空でない 0 和の部分集合はない（あればその中で最後に加えた元のときに見つかる）ので、
 *      Z は最小。部分集合の探索は列の先頭から「入れる／入れない」を決め、各素数の剰余の集合と、
 *      残りの部分和の範囲 [-（符号 - の w の和）, （符号 + の w の和）] で枝を切る。
 *
 * 検証: N <= 31 を、すべての符号つき部分集合を調べる素朴な版（(3) の代わりに「素数 p >= 3、p^2 > N で
 *       p の倍数が使えない」場合だけを除き、(5)-(8) を使わず、最小性もすべての部分集合で調べる）と照合した。
 *       N <= 40 を、(3) の除去をしない版とも照合した。
 *       AddressSanitizer / UndefinedBehaviorSanitizer つきで N <= 42 を実行した。
 *       N = 1..60: 0, 0, 0, 0, 0, 4, 4, 4, 4, 4, 4, 6, 6, 6, 8, 8, 8, 10, 10, 10, 12, 12, 12, 14, 14, 14, 14,
 *       15, 15, 16, 16, 16, 18, 18, 19, 20, 20, 20, 20, 20, 20, 20, 20, 22, 22, 22, 22, 24, 24, 24, 24,
 *       27, 27, 29, 30, 31, 31, 31, 31, 32（N <= 50 で約 1.5 秒、N <= 60 で約 25 秒）。
 *
 * コンパイル: g++ -O2 -std=c++17 -Wall -Wextra -Wpedantic -Werror 402839_01.cpp -o 402839_01
 * 実行:       ./402839_01 [NMAX]   （NMAX の既定値 40、1 <= NMAX <= 120）
 */
#include <algorithm>
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

namespace {

__extension__ typedef __int128 i128;
constexpr int MAXN = 120;
constexpr int MAXP = 32;                               // N <= 120 の素数の個数 30 以下
constexpr int MAXPOS = MAXN + 2;

// {0..M-1} の部分集合（M = M_q <= N <= 120 < 128）を 128 bit で表す
__extension__ typedef unsigned __int128 Bits;
inline bool btest(Bits b, int r) { return (b >> r) & 1; }
// 集合を a だけ巡回シフト（法 M）: {(r + a) mod M}
inline Bits brot(Bits b, int a, int M, Bits mask) {
    if (a == 0) return b;
    return ((b << a) | (b >> (M - a))) & mask;
}

int isprime(int p) {
    if (p < 2) return 0;
    for (int d = 2; d * d <= p; d++) if (p % d == 0) return 0;
    return 1;
}
int vp(int n, int p) { int e = 0; while (n % p == 0) { n /= p; e++; } return e; }
int lpf(int n) { int r = 1; for (int p = 2; p <= n; p++) if (n % p == 0) { r = p; while (n % p == 0) n /= p; } return r; }
i128 gcd128(i128 a, i128 b) { while (b) { i128 t = a % b; a = b; b = t; } return a; }

// ---------------- N ごとの問題 ----------------
int N, m;                                              // m = 使える元の数
std::vector<int> el;                                   // 並べた元（el[0] = N）
std::vector<i128> w;                                   // w = L / el
std::vector<int> primes, mod;                          // 素数 q と M_q
std::vector<std::vector<int>> wr;                      // wr[qi][i] = w[i] mod M_q
int target;                                            // 探す大きさの下限
int best;                                              // 見つけた最小の 0 和集合の最大の大きさ

// ---------------- (5)(6) 主探索 ----------------
int head;                                              // 先頭から head 個を探索、残り（末尾）は表
// 全体の表: maxc[qi][i][r] = 位置 i 以降の元（符号 {+,-,0}）で和 ≡ r (mod M_q) とするときに使える元の最大個数
//   （作れなければ -1）。事実 (5) の剰余の判定と個数の上界を兼ねる。
signed char maxc[MAXP][MAXPOS][128];
std::vector<i128> suf;                                 // suf[i] = Sum_{j>=i} w[j]
struct TailEntry { i128 sum; int size; uint32_t code; };
std::vector<TailEntry> tail;
int res[32];
std::vector<int> pick, picksg;                         // 選んだ元（N 以外）と符号

// 事実 (8): 選んだ元（N 以外）の列 pick（長さ d）について、位置 j 以降の元の部分和（符号は固定）の
//   剰余の集合 sfs[d][j] と、符号 +, - の元の w の和 spos[d][j], sneg[d][j] を持つ。元を 1 個加えるたびに「新しい元を含む 0 和の
//   部分集合ができるか」= 「pick の部分集合で和が -(新しい元の符号つきの w) のものがあるか」を、
//   pick の先頭（大きい素因数の元）から決める探索で調べる（剰余と大きさで枝を切る）。
constexpr int MAXD = MAXN;                             // pick の長さの上限（|A| <= N）
Bits sfs[MAXD + 1][MAXD + 1][MAXP];
i128 spos[MAXD + 1][MAXD + 1], sneg[MAXD + 1][MAXD + 1];   // 位置 j 以降の符号 + の w の和、- の w の和
int pe[MAXD], ps[MAXD];                                // pick の元の番号と符号
int qres[MAXD + 1][MAXP];
int qd;                                                // 探索中の pick の長さ

// pick の位置 j 以降の部分集合で和 rem となるものがあるか（qres[j] = rem mod M_q）
bool qdfs(int j, i128 rem) {
    if (rem == 0) return true;
    if (j == qd) return false;
    if (rem > spos[qd][j] || -rem > sneg[qd][j]) return false;   // 部分和は [-sneg, spos] の中
    for (size_t qi = 0; qi < primes.size(); qi++)
        if (!btest(sfs[qd][j][qi], qres[j][qi])) return false;
    const int e = pe[j], sg = ps[j];
    for (size_t qi = 0; qi < primes.size(); qi++) {   // 元 j を入れる: 残り rem - sg·w
        const int M = mod[qi], a = wr[qi][e];
        const int x = qres[j][qi];
        qres[j + 1][qi] = sg > 0 ? (x >= a ? x - a : x + M - a) : (x + a >= M ? x + a - M : x + a);
    }
    if (qdfs(j + 1, sg > 0 ? rem - w[e] : rem + w[e])) return true;
    for (size_t qi = 0; qi < primes.size(); qi++) qres[j + 1][qi] = qres[j][qi];   // 入れない
    return qdfs(j + 1, rem);
}

// 長さ d の pick に元 e（符号 sg）を加える。新しい元を含む 0 和の部分集合ができるなら false（加えない）
bool push_elem(int d, int e, int sg) {
    if (d >= MAXD) { std::fprintf(stderr, "\nInternal error: pick too long.\n"); std::exit(2); }
    for (size_t qi = 0; qi < primes.size(); qi++) {
        const int M = mod[qi], a = wr[qi][e];
        qres[0][qi] = sg > 0 ? (a == 0 ? 0 : M - a) : a;   // rem = -sg·w の剰余
    }
    qd = d;
    if (qdfs(0, sg > 0 ? -w[e] : w[e])) return false;
    for (size_t qi = 0; qi < primes.size(); qi++) {
        const int M = mod[qi], a = wr[qi][e];
        const Bits mask = (static_cast<Bits>(1) << M) - 1;
        const int sh = sg > 0 ? a : (M - a) % M;
        for (int j = 0; j <= d; j++) sfs[d + 1][j][qi] = sfs[d][j][qi] | brot(sfs[d][j][qi], sh, M, mask);
        sfs[d + 1][d + 1][qi] = 1;                     // 空の和 0
    }
    for (int j = 0; j <= d; j++) {
        spos[d + 1][j] = spos[d][j] + (sg > 0 ? w[e] : 0);
        sneg[d + 1][j] = sneg[d][j] + (sg > 0 ? 0 : w[e]);
    }
    spos[d + 1][d + 1] = sneg[d + 1][d + 1] = 0;
    pe[d] = e; ps[d] = sg;
    return true;
}

// 先頭側（N 以外に 0 和の部分なし）に末尾側の元を順に加え、どこでも 0 和の部分ができなければ最小（事実 (2)(8)）
void check_candidate(int size, int d) {
    if (size < target) return;
    for (size_t k = d; k < pick.size(); k++)
        if (!push_elem(static_cast<int>(k), pick[k], picksg[k])) return;
    if (size > best) best = size;
    if (best + 1 > target) target = best + 1;          // 以後はもっと大きいものだけを探す
}

void dfs(int i, i128 S, int size) {
    if (size + (m - i) < target) return;               // 個数の上界
    if ((S < 0 ? -S : S) > suf[i]) return;             // |S| の上界
    for (size_t qi = 0; qi < primes.size(); qi++) {    // 剰余の表と個数の上界（事実 (5)）
        const int need = (mod[qi] - res[qi]) % mod[qi];
        const int c = maxc[qi][i][need];
        if (c < 0 || size + c < target) return;
    }
    if (i == head) {                                   // 事実 (6): 末尾は表で引く
        const i128 want = -S;
        auto it = std::lower_bound(tail.begin(), tail.end(), want,
                                   [](const TailEntry &t, i128 v) { return t.sum < v; });
        for (; it != tail.end() && it->sum == want; ++it) {
            if (size + it->size < target) break;       // 大きさの降順なので以後も足りない
            const size_t base = pick.size();
            for (int j = head; j < m; j++) {
                const uint32_t c = (it->code >> (2 * (j - head))) & 3;
                if (c) { pick.push_back(j); picksg.push_back(c == 1 ? 1 : -1); }
            }
            check_candidate(size + it->size, static_cast<int>(base));
            pick.resize(base); picksg.resize(base);
        }
        return;
    }
    int save[32];
    for (int s = 1; s >= -1; s -= 2) {                 // + と -
        for (size_t qi = 0; qi < primes.size(); qi++) {
            save[qi] = res[qi];
            const int M = mod[qi], a = wr[qi][i];
            res[qi] = s > 0 ? (res[qi] + a) % M : (res[qi] + M - a) % M;
        }
        if (push_elem(static_cast<int>(pick.size()), i, s)) {   // 事実 (8): 0 和の部分ができるなら枝を切る
            pick.push_back(i); picksg.push_back(s);
            dfs(i + 1, s > 0 ? S + w[i] : S - w[i], size + 1);
            pick.pop_back(); picksg.pop_back();
        }
        for (size_t qi = 0; qi < primes.size(); qi++) res[qi] = save[qi];
    }
    dfs(i + 1, S, size);                               // 0（使わない）
}

// N を含み大きさ >= lower の最小の 0 和集合の最大の大きさ（なければ 0）
int solve(int lower) {
    // 事実 (3): 使えない元を除く
    std::vector<int> U;
    for (int n = 1; n <= N; n++) U.push_back(n);
    for (bool changed = true; changed;) {
        changed = false;
        for (int p = 2; p <= N && !changed; p++) {
            if (!isprime(p)) continue;
            int e = 0;
            for (int n : U) e = std::max(e, vp(n, p));
            if (e == 0) continue;
            int pe = 1;
            for (int t = 0; t < e; t++) pe *= p;
            std::vector<int> T;
            for (int n : U) if (vp(n, p) == e) T.push_back(n);
            // 0 以外の符号で Sum δ (n/p^e)^{-1} ≡ 0 (mod p) にできるか（剰余と「空でない」の DP）
            std::vector<char> any(p, 0), ne(p, 0);     // any: 空を含む到達、ne: 空でない到達
            any[0] = 1;
            for (int n : T) {
                int r = (n / pe) % p, inv = 1;
                while (inv * r % p != 1) inv++;
                std::vector<char> a2 = any, n2 = ne;
                for (int x = 0; x < p; x++) {
                    if (!any[x] && !ne[x]) continue;
                    for (int s = -1; s <= 1; s += 2) {
                        int y = ((x + s * inv) % p + p) % p;
                        n2[y] = 1;
                    }
                }
                any.swap(a2); ne.swap(n2);
            }
            if (!ne[0]) {
                std::vector<int> U2;
                for (int n : U) if (vp(n, p) != e) U2.push_back(n);
                U.swap(U2);
                changed = true;
            }
        }
    }
    if (std::find(U.begin(), U.end(), N) == U.end()) return 0;   // N は使えない
    // 並べ方: N を先頭、残りは最大素因数の降順（同じなら v の大きい順、大きい順）
    std::vector<int> rest;
    for (int n : U) if (n != N) rest.push_back(n);
    std::sort(rest.begin(), rest.end(), [](int a, int b) {
        int la = lpf(a), lb = lpf(b);
        if (la != lb) return la > lb;
        return a > b;
    });
    el.clear(); el.push_back(N);
    for (int n : rest) el.push_back(n);
    m = static_cast<int>(el.size());
    // 事実 (4): L とあふれの確認
    i128 L = 1;
    const i128 LIM = static_cast<i128>(1) << 125;
    for (int n : el) {
        i128 g = gcd128(L, n);
        L = L / g * n;
        if (L > LIM / (m + 1)) { std::fprintf(stderr, "\nN=%d is too large (L overflow).\n", N); std::exit(2); }
    }
    w.assign(m, 0);
    for (int i = 0; i < m; i++) w[i] = L / el[i];
    primes.clear(); mod.clear();
    for (int p = 2; p <= N; p++) {
        if (!isprime(p)) continue;
        int e = 0;
        for (int n : el) e = std::max(e, vp(n, p));
        if (e == 0) continue;
        int pe = 1;
        for (int t = 0; t < e; t++) pe *= p;
        primes.push_back(p); mod.push_back(pe);
    }
    if (primes.size() > MAXP) { std::fprintf(stderr, "\nInternal error: too many primes.\n"); std::exit(2); }
    wr.assign(primes.size(), std::vector<int>(m));
    for (size_t qi = 0; qi < primes.size(); qi++)
        for (int i = 0; i < m; i++) wr[qi][i] = static_cast<int>(w[i] % mod[qi]);
    for (size_t qi = 0; qi < primes.size(); qi++) {
        const int M = mod[qi];
        for (int r = 0; r < M; r++) maxc[qi][m][r] = (r == 0) ? 0 : -1;
        for (int i = m - 1; i >= 0; i--) {
            const int a = wr[qi][i];
            for (int r = 0; r < M; r++) {
                int b = maxc[qi][i + 1][r];
                const int u = maxc[qi][i + 1][(r + M - a) % M], v = maxc[qi][i + 1][(r + a) % M];   // + または - を使う
                if (u >= 0 && u + 1 > b) b = u + 1;
                if (v >= 0 && v + 1 > b) b = v + 1;
                maxc[qi][i][r] = static_cast<signed char>(b);
            }
        }
    }
    suf.assign(m + 1, 0);
    for (int i = m - 1; i >= 0; i--) suf[i] = suf[i + 1] + w[i];
    // 事実 (6): 末尾 t 個の表（N は含めない）
    const int t = std::min(13, m - 1);
    head = m - t;
    tail.clear();
    uint32_t pw = 1;
    for (int j = 0; j < t; j++) pw *= 3;
    // 事実 (8): 空でない 0 和の部分を含む符号つき部分集合は除く。bad[c] は、c（3 進の符号）が空でない
    //   0 和の部分を含むか。c 自身が 0 和か、c の 1 か所を 0 にしたもの（c より小さい番号）が bad なら bad。
    std::vector<char> bad(pw, 0);
    std::vector<i128> sum3(pw, 0);
    std::vector<int> size3(pw, 0);
    uint32_t p3[32];
    p3[0] = 1;
    for (int j = 1; j <= t; j++) p3[j] = p3[j - 1] * 3;
    for (uint32_t c3 = 1; c3 < pw; c3++) {
        int j = 0;                                     // 最下位の 0 でない桁
        while ((c3 / p3[j]) % 3 == 0) j++;
        const uint32_t d = (c3 / p3[j]) % 3, prev = c3 - d * p3[j];
        sum3[c3] = sum3[prev] + (d == 1 ? w[head + j] : -w[head + j]);
        size3[c3] = size3[prev] + 1;
        bool b = (sum3[c3] == 0);
        for (int k = 0; k < t && !b; k++) {
            const uint32_t dk = (c3 / p3[k]) % 3;
            if (dk && bad[c3 - dk * p3[k]]) b = true;
        }
        bad[c3] = b;
    }
    for (uint32_t c3 = 0; c3 < pw; c3++) {
        if (bad[c3]) continue;
        uint32_t c = c3, code = 0;
        for (int j = 0; j < t; j++) { code |= (c % 3) << (2 * j); c /= 3; }
        tail.push_back(TailEntry{sum3[c3], size3[c3], code});
    }
    std::sort(tail.begin(), tail.end(), [](const TailEntry &a, const TailEntry &b) {
        if (a.sum != b.sum) return a.sum < b.sum;
        return a.size > b.size;
    });
    // 主探索: δ_N = +1 を固定（事実 (1)）
    target = lower; best = 0;
    for (size_t qi = 0; qi < primes.size(); qi++) res[qi] = wr[qi][0] % mod[qi];
    pick.clear(); picksg.clear();
    for (size_t qi = 0; qi < primes.size(); qi++) sfs[0][0][qi] = 1;   // 空の和 0
    spos[0][0] = sneg[0][0] = 0;
    dfs(1, w[0], 1);
    return best;
}

bool parse_limit(const char *text, int *value) {
    if (!*text) return false;
    for (const char *p = text; *p; p++)
        if (*p < '0' || *p > '9') return false;
    errno = 0;
    char *end;
    long parsed = std::strtol(text, &end, 10);
    if (errno == ERANGE || *end || parsed < 1 || parsed > MAXN) return false;
    *value = static_cast<int>(parsed);
    return true;
}

}  // namespace

int main(int argc, char **argv) {
    int NMAX = 40;
    if (argc == 2 && (!std::strcmp(argv[1], "--help") || !std::strcmp(argv[1], "-h"))) {
        std::printf("Usage: %s [NMAX] (1 <= NMAX <= %d; default 40)\n", argv[0], MAXN);
        return 0;
    }
    if (argc > 2 || (argc == 2 && !parse_limit(argv[1], &NMAX))) {
        std::fprintf(stderr, "Usage: %s [NMAX]; NMAX must be a decimal integer in 1..%d.\n", argv[0], MAXN);
        return 1;
    }
    int a = 0;
    for (N = 1; N <= NMAX; N++) {
        const int b = solve(a + 1);                    // 事実 (1)
        if (b > a) a = b;
        if (std::printf(N == 1 ? "%d" : ", %d", a) < 0 || std::fflush(stdout) != 0) {
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
