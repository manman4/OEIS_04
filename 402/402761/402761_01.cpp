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
 *  (4) 判定は整数で行う: 覆う k 元集合の個数 c について 2c >= C(n,k)。数えながら、
 *      c が必要数 ceil(C(n,k)/2) に達したら「満たす」、残り全部が覆っても届かなくなったら
 *      「満たさない」と、その時点で打ち切る（結果は全部数えたときと同じ）。
 *  (5) 元 0 は部分和を変えない（R ∪ (R + 0) = R）。そこで探索では 0 以外の元だけを小さい順に選ぶ。
 *      探索の節点「0 以外の元を x 未満から集合 S（t 個）だけ選んだ」は、k 元集合 T のうち
 *      T ∩ {1..x-1} = S となるもの全体を表し、その個数は、残りの元 {x..n-1} ∪ {0}（m+1 個、m = n-x）
 *      から k-t 個選ぶ C(m+1, k-t) 個。その内訳は
 *        ・次に選ぶ 0 以外の元が a（x <= a <= n-1）のもの: C(n-a, k-t-1) 個（子の節点）
 *        ・0 以外の元をもう選ばないもの: t = k なら T = S、t = k-1 なら T = S ∪ {0} の 1 個、
 *          それ以外は 0 個（部分和はどちらも S の部分和と同じ）
 *      で、合計が C(m+1, k-t) になる（Pascal の公式の和）。
 *  (6) まとめて数える: S の部分和が G 全体なら、元を加えても部分和は G 全体のままなので、節点の
 *      C(m+1, k-t) 個はすべて覆う。まとめて加えて、その下は探索しない。
 *  (7) 覆えない枝を切る: 元を 1 個加えると部分和の集合 R は R ∪ (R + a) で、大きさは高々 2 倍。
 *      節点で |R| = s、まだ加えられる 0 以外の元が高々 r = min(k-t, m) 個なら、
 *      部分和は高々 s·2^r 個。これが n 未満なら節点の C(m+1, k-t) 個はどれも覆わない。
 *  (8) 部分和の集合は 64 bit のビット集合で持つ（元は混合基数で番号付け、第 1 成分が最下位）。
 *      平行移動 R + a は成分ごとの巡回シフトの合成: 第 i 成分（法 m_i、位取り B_i、周期 P_i = B_i m_i）
 *      を a_i だけずらすと、第 i 成分が m_i - a_i 未満の元は番号が a_i B_i 増え、それ以外は
 *      P_i - a_i B_i 減る。よって (R & mask) << (a_i B_i) | (R & ~mask) >> (P_i - a_i B_i)。
 *
 * 検証: (5)-(8) を使わない前の版（部分集合を 1 個ずつ数える）と、次の 2 点を照合した。
 *       ・事実 (4) の打ち切りを外し、n <= 30 のすべての群、k <= 8 で、覆う k 元集合の個数そのもの。
 *       ・n <= 40 の a(n)。
 *       AddressSanitizer / UndefinedBehaviorSanitizer つきで n <= 30 も実行した。
 *       n = 1..35 は約 0.3 秒（前の版は約 1.7 秒）、n = 1..40 は約 1.2 秒（前の版は約 6 秒）。
 *       前の版は n <= 30 を、すべての群・すべての k 元集合を最後まで数える素朴な版と、
 *       n <= 16 を Python の別実装（集合演算）と照合済み。
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
constexpr int MAXN = 64;

int n, K;
u64 full;
u64 C[MAXN + 2][MAXN + 2];                // 二項係数（C(64,32) < 2^63 なので収まる）
u64 total, need, cnt, seen;               // C(n,k), ceil(C/2), 覆った数, 数え終えた数
bool decided;

// 平行移動 R + a（事実 (8)）。元 a ごとに、0 でない成分の数だけ (mask, up, down) を持つ
struct Shift { u64 mask; int up, down; };
std::vector<Shift> shifts[MAXN];

inline u64 translate(u64 R, int a) {
    for (const Shift &s : shifts[a])
        R = ((R & s.mask) << s.up) | ((R & ~s.mask & full) >> s.down);
    return R;
}

// 数え終えた部分集合を加え、事実 (4) で打ち切れるか調べる
inline void account(u64 covered, u64 all) {
    cnt += covered;
    seen += all;
    if (cnt >= need) decided = true;                           // 満たす
    else if (cnt + (total - seen) < need) decided = true;      // 満たさない
}

// 節点: 0 以外の元を x 未満から t 個選び、部分和の集合が R（事実 (5)）
void dfs(int x, int t, u64 R) {
    const int m = n - x;
    const u64 here = C[m + 1][K - t];                          // この節点が表す k 元集合の数
    if (R == full) { account(here, here); return; }            // 事実 (6)
    const int r = (K - t < m) ? K - t : m;
    // 事実 (7)。r >= 7 なら s·2^r >= 128 > n なので調べない（シフトのあふれも防ぐ）
    if (r < 7 && (static_cast<u64>(__builtin_popcountll(R)) << r) < static_cast<u64>(n)) {
        account(0, here);
        return;
    }
    if (K - t <= 1) { account(0, 1); if (decided) return; }    // 0 以外をもう選ばない 1 個（覆わない）
    if (t == K) return;
    for (int a = x; a <= n - 1; a++) {
        dfs(a + 1, t + 1, R | translate(R, a));
        if (decided) return;
    }
}

// 群 Z_{m_1} x ... x Z_{m_r} で、k 元集合の半分以上が覆うか
bool half_cover(const std::vector<int> &mods, int k) {
    // 事実 (8) の表: 成分 i ごとに、ずらす量 d（1..m_i-1）のマスク
    for (int a = 0; a < n; a++) shifts[a].clear();
    int B = 1;
    for (int m : mods) {
        const int P = B * m;
        for (int a = 0; a < n; a++) {
            const int d = (a / B) % m;                         // a の第 i 成分
            if (d == 0) continue;
            u64 mask = 0;
            for (int y = 0; y < n; y++)
                if ((y / B) % m < m - d) mask |= 1ULL << y;
            shifts[a].push_back(Shift{mask, d * B, P - d * B});
        }
        B = P;
    }
    K = k;
    total = C[n][k];
    need = (total + 1) / 2;
    cnt = 0; seen = 0; decided = false;
    dfs(1, 0, 1ULL);                                           // 空和 0 から始める
    if (!decided && seen != total) {                           // 全部数え終えたなら数は合うはず
        std::fprintf(stderr, "\nInternal error: count mismatch at n=%d.\n", n);
        std::exit(2);
    }
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
        std::vector<std::vector<int>> parts;                   // e の分割をすべて
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
    for (int i = 0; i <= MAXN + 1; i++) {                      // Pascal の三角形（負の下の添字は 0 として扱う）
        C[i][0] = 1;
        for (int j = 1; j <= i; j++) C[i][j] = C[i - 1][j - 1] + (j <= i - 1 ? C[i - 1][j] : 0);
    }
    for (n = 1; n <= N; n++) {
        full = (n == 64) ? ~0ULL : ((1ULL << n) - 1);
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
