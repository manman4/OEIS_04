/*
 * Erdős Problem #543  (A402761)
 * a(n) = f(n) = 次を満たす最小の k: 位数 n のどのアーベル群 G についても、G の k 元部分集合 A を
 *        一様にランダムに選ぶと、確率 1/2 以上で G のすべての元が A の部分和（空和 0 を含む）になる。
 *        言い換えると「部分和が G 全体を覆う k 元部分集合が、全体 C(n,k) 個の半分以上ある」。
 * n = 1..N を計算し、"0, 1, 3, 3, ..." の形で 1 項ずつ標準出力に書き出す（ファイルは作らない）。
 *
 * 使う事実（どれも証明つき、結果を変えない）:
 *  (1) 位数 n のアーベル群は、n = Prod p^e と素因数分解したとき、各 p について e の分割
 *      e = e_1 + e_2 + ... を選んで作る Z_{p^{e_1}} x Z_{p^{e_2}} x ... の直積で、同型を除き
 *      ちょうど 1 回ずつ現れる（有限アーベル群の基本定理）。f(n) は群ごとの値 g(G) の最大値。
 *  (2) 覆う確率は k について単調非減少: 一様な (k+1) 元集合 B から一様に 1 元を除くと一様な
 *      k 元集合 A ⊂ B になり、A が覆えば B も覆う。よって g(G) は「覆う確率 >= 1/2」となる
 *      最小の k で、f(n) を求めるには、現在の最大値 m について群ごとに k = m で判定し、
 *      満たさなければ m を 1 ずつ増やせばよい。
 *  (3) 2^k < n なら k 元集合の部分和は高々 2^k 個で G を覆えない。よって k >= ceil(log2 n) から始める。
 *  (4) 判定は整数で行う: 覆う k 元集合の個数 c について 2c >= C(n,k)。部分集合を順に数えながら、
 *      c が必要数 ceil(C(n,k)/2) に達したら「満たす」、残り全部が覆っても届かなくなったら
 *      「満たさない」と、その時点で打ち切る（結果は全部数えたときと同じ）。
 *  (5) 部分和の集合は 64 bit のビット集合で持つ。元 a を加えると R |= (R + a)。
 *      R + a は R の各元を a だけ平行移動した集合（群の加法表で計算）。
 *
 * 検証: n <= 30 を、すべての群・すべての k 元集合を最後まで数える素朴な版（(2)(4) なし）と照合した。
 *       n <= 16 はさらに Python の別実装（集合演算）とも照合済み。
 *
 * コンパイル: g++ -O2 -std=c++17 -Wall -Wextra -Wpedantic -Werror 402761_01.cpp -o 402761_01
 * 実行:       ./402761_01 [N]   （N の既定値 30、1 <= N <= 64）
 */
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

namespace {

typedef uint64_t u64;
__extension__ typedef unsigned __int128 u128;
constexpr int MAXN = 64;

int n;
int addt[MAXN][MAXN];                     // 加法表（元は 0..n-1、0 が単位元）
u64 total, need, cnt, seen;               // C(n,k), ceil(C/2), 覆った数, 数え終えた数
bool decided;

// 平行移動: R + a
inline u64 translate(u64 R, int a) {
    u64 out = 0;
    while (R) {
        int s = __builtin_ctzll(R);
        R &= R - 1;
        out |= 1ULL << addt[s][a];
    }
    return out;
}

// x 以降から残り r 個を選ぶ。R = 現在の部分和の集合
void dfs(int x, int r, u64 R, u64 full) {
    if (decided) return;
    if (r == 0) {
        seen++;
        if (R == full) cnt++;
        if (cnt >= need) decided = true;                       // 事実 (4): 満たす
        else if (cnt + (total - seen) < need) decided = true;  // 事実 (4): 満たさない
        return;
    }
    for (int a = x; a <= n - r; a++) {
        dfs(a + 1, r - 1, R | translate(R, a), full);
        if (decided) return;
    }
}

u64 binom(int a, int b) {
    if (b < 0 || b > a) return 0;
    u64 c = 1;
    for (int i = 1; i <= b; i++)            // 途中の積は 128 bit で計算（C(64,32) < 2^63 なので結果は収まる）
        c = static_cast<u64>(static_cast<u128>(c) * static_cast<unsigned>(a - b + i) / static_cast<unsigned>(i));
    return c;
}

// 群 Z_{m_1} x ... x Z_{m_r} で、k 元集合の半分以上が覆うか
bool half_cover(const std::vector<int> &mods, int k) {
    // 加法表（混合基数で元を番号付け）
    for (int a = 0; a < n; a++)
        for (int b = 0; b < n; b++) {
            int x = a, y = b, res = 0, mul = 1;
            for (int m : mods) {
                int da = x % m, db = y % m;
                x /= m; y /= m;
                res += ((da + db) % m) * mul;
                mul *= m;
            }
            addt[a][b] = res;
        }
    total = binom(n, k);
    need = (total + 1) / 2;
    cnt = 0; seen = 0; decided = false;
    const u64 full = (n == 64) ? ~0ULL : ((1ULL << n) - 1);
    dfs(0, k, 1ULL, full);                                     // 空和 0 から始める
    return cnt >= need;
}

// 位数 n のアーベル群をすべて列挙（事実 (1)）
std::vector<std::vector<int>> abelian_groups(int nn) {
    std::vector<int> ps, es;
    int x = nn;
    for (int p = 2; p * p <= x; p++)
        if (x % p == 0) { int e = 0; while (x % p == 0) { x /= p; e++; } ps.push_back(p); es.push_back(e); }
    if (x > 1) { ps.push_back(x); es.push_back(1); }
    std::vector<std::vector<int>> res(1);                      // 自明群は空の直積
    for (size_t i = 0; i < ps.size(); i++) {
        // e の分割をすべて
        std::vector<std::vector<int>> parts;
        std::vector<int> cur;
        struct Gen {
            static void go(int e, int mx, std::vector<int> &cur, std::vector<std::vector<int>> &out) {
                if (e == 0) { out.push_back(cur); return; }
                for (int q = (e < mx ? e : mx); q >= 1; q--) { cur.push_back(q); go(e - q, q, cur, out); cur.pop_back(); }
            }
        };
        Gen::go(es[i], es[i], cur, parts);
        std::vector<std::vector<int>> next;
        for (auto &g : res)
            for (auto &part : parts) {
                std::vector<int> h = g;
                for (int q : part) { int v = 1; for (int t = 0; t < q; t++) v *= ps[i]; h.push_back(v); }
                next.push_back(h);
            }
        res.swap(next);
    }
    for (auto &g : res) if (g.empty()) g.push_back(1);
    // 分割は大きい部分から作るので、最初の群は巡回群 Z_n になる（最大値が早く決まりやすい）
    return res;
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
    int N = 30;
    if (argc == 2 && (!std::strcmp(argv[1], "--help") || !std::strcmp(argv[1], "-h"))) {
        std::printf("Usage: %s [N] (1 <= N <= %d; default 30)\n", argv[0], MAXN);
        return 0;
    }
    if (argc > 2 || (argc == 2 && !parse_limit(argv[1], &N))) {
        std::fprintf(stderr, "Usage: %s [N]; N must be a decimal integer in 1..%d.\n", argv[0], MAXN);
        return 1;
    }
    for (n = 1; n <= N; n++) {
        int m = 0;                                             // 事実 (3): ceil(log2 n)
        while ((1LL << m) < n) m++;
        for (const auto &g : abelian_groups(n)) {
            while (!half_cover(g, m)) {                        // 事実 (2)
                m++;
                if (m > n) { std::fprintf(stderr, "\nInternal error at n=%d.\n", n); return 2; }
            }
        }
        if (std::printf(n == 1 ? "%d" : ", %d", m) < 0 || std::fflush(stdout) != 0) {
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
