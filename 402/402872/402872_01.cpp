/*
 * Erdős Problem #572 に関連する数列
 * a(n) = ex(n; C_6) = 長さ 6 の閉路を含まない n 頂点の単純グラフの辺の数の最大値。
 * n = 1..NMAX を計算し、"0, 1, 3, 6, 10, ..." の形で 1 項ずつ標準出力に書き出す（ファイルは作らない）。
 *
 * 使う事実（どれも証明つき、結果を変えない）:
 *  (1) 下界: C6 を含まないグラフ G1（b 頂点）と G2（n-b+1 頂点）を 1 頂点で貼り合わせても C6 はできない
 *      （閉路は切断点をまたげないので、閉路はどちらか一方に含まれる）。よって
 *        a(n) >= E0(n) = max_{2<=b<=n-1} a(b) + a(n-b+1)。
 *      したがって「辺の数が T = E0(n)+1 以上で C6 を含まない n 頂点グラフ」があるかを調べ、あればその最大の
 *      辺の数が a(n)、なければ a(n) = E0(n)。
 *  (2) 生成（McKay の canonical augmentation）: グラフ G の親を「標準的な最小次数の頂点を除いたグラフ」とする。
 *      標準的な頂点は、最小次数の頂点のうち不変量 (inv1, 色) が辞書式で最大のもの、その中で nauty の
 *      標準ラベルが最大のもの（inv1 = 近傍の次数の和と三角形の数、色 = color refinement。どちらも同型で
 *      保たれるので、この規則は同型写像と両立する）。親に頂点 v を 1 個足して子を作り、v がその軌道に
 *      入るときだけ子として受け入れる。同じ親から同型な子ができる重複は、子の標準形で取り除く。
 *      C6 を含まない性質は部分グラフに引き継がれるので、C6 を含まないグラフはすべてこの木に 1 回ずつ現れる。
 *  (3) 必要な辺の数: k 頂点のグラフの最小次数は ⌊2e/k⌋ 以下なので、親の辺の数は
 *      e - ⌊2e/k⌋ 以上（この式は e について単調非減少）。よって目標 T から
 *        L_n = T, L_k = L_{k+1} - ⌊2 L_{k+1}/(k+1)⌋
 *      とすると、辺の数 T 以上の n 頂点グラフに至る途中の k 頂点のグラフは L_k 本以上の辺をもつ。
 *  (4) 足す頂点 v の近傍 S（|S| = d）の条件:
 *      ・C6 ができない ⇔ S の相異なる 2 点 s, t が親の中で長さ 4 の道（5 頂点が相異なる）で結ばれない。
 *        よって S は「長さ 4 の道で結ばれる 2 点」を辺とするグラフ H の独立集合。
 *      ・v は子の最小次数の頂点: 親での次数が d-1 の頂点は S に必ず入り、d-2 以下の頂点があれば不可能。
 *        よって d <= （親の最小次数）+ 1。
 *      ・子の辺の数 e + d >= L_{k+1}。
 *  (5) 最後の段（n 頂点）では同型判定をせず、条件を満たす S の最大の大きさだけを求める。
 *  (6) nauty を省ける場合: 新しい頂点 v より (inv1, 色) が大きい最小次数の頂点があれば棄却。v が唯一の最大なら
 *      v が標準的な頂点で、標準形を計算せずに受け入れてよい。このとき同じ親から同型な子ができるのは、
 *      近傍 S と S' が親の自己同型群 Aut(P) の同じ軌道にあるときだけ（子の同型写像は標準的な頂点 v を v に
 *      移すので、P の自己同型を引き起こして S を S' に移す。逆も成り立つ）。そこで Aut(P) の生成元を nauty で
 *      1 回だけ求め（必要になったときに）、S がその軌道の中でビット列として最小のときだけ受け入れる。
 *      群の位数が 5000 を超える親では、この方法を使わず、子の標準形で重複を除く。どちらを使うかは親ごとに
 *      決まり、v が唯一の最大かどうかは同型な子の間で共通なので、二つの方法が混ざって取りこぼすことはない。
 *  (7) 先読みの上界: j 頂点、辺 e 本、最小次数 δ のグラフから木を下るとき、次に足す頂点の次数 d は
 *      (i) d <= δ + 1（頂点を 1 個除くと最小次数は高々 1 減るので、子の最小次数 d は親の最小次数 + 1 以下）、
 *      (ii) d (t-1) <= 2e（d は子の平均次数以下）、(iii) d <= t、(iv) e + d <= a(t+1)（t+1 < n）を満たし、
 *      子の最小次数は d。この条件での n 頂点での辺の数の最大値を動的計画法で表にし、T に届かない枝を切る。
 *      （(iv) は e について減少なので貪欲には決められず、DP が必要。）
 *  (8) 並列化: 第 min(10, n-2) 段のグラフを DFS の順に番号付けし、番号 mod P で P 個のプロセスに分担する
 *      （fork）。それより上の段の動作は最後の段の結果に依存しないので、番号付けはどのプロセスでも同じ。
 *      各プロセスの最大値の最大をとる（結果はプロセス数によらない）。
 *  (9) nauty には (次数, inv1) による初期の色分けを渡す（細分の手間が減る）。色は同型で保たれる量の値の順で
 *      決まり、どの自己同型も色を保つので、標準形・軌道・自己同型群は色なしの場合と同じ意味をもつ。
 *
 * 検証: n <= 10 を、nauty-geng で全連結グラフを生成して C6 の有無を調べた結果と照合した。
 *       n <= 23 を、B. McKay の extremal graph のデータ（C6-free の表、n <= 37 が確定値）と照合した。
 *       プロセス数 1, 2, 3, 7 で結果が同じことを確かめた。
 *       n <= 20 の各段で生成されるグラフの数が、事実 (6)(9) を入れる前の版（重複をすべて子の標準形で除く版）と
 *       一致することを確かめた（取りこぼしも重複もない）。
 *       AddressSanitizer / UndefinedBehaviorSanitizer つきで n <= 18 を実行した。
 *       時間の目安: 2 プロセスで n <= 21 が約 4 秒、n <= 23 が約 70 秒。n が 1 増えるごとに約 2〜3 倍。
 *
 * コンパイル（nauty のライブラリが必要。Debian/Ubuntu は libnauty-dev、macOS は brew install nauty）:
 *   g++ -O2 -std=c++17 -Wall -Wextra -Wpedantic -Werror 402872_01.cpp -o 402872_01 -lnauty
 *   （ヘッダやライブラリの場所が標準でなければ -I/-L を足す。例: -I$(brew --prefix)/include -L$(brew --prefix)/lib）
 * 実行: ./402872_01 [NMAX [PROCS]]   （NMAX の既定値 16、1 <= NMAX <= 32。PROCS の既定値は CPU 数）
 */
#include <nauty/nauty.h>

#include <algorithm>
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <unordered_set>
#include <vector>

#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

namespace {

constexpr int MAXV = 32;

int n;                                                 // 目標の頂点数
int L[MAXV + 2];                                       // 事実 (3) の必要な辺の数
int bestE;                                             // 最後の段で見つけた辺の数の最大値（なければ -1）
int Tgt;                                               // 目標の辺の数 T
int exk[MAXV + 2];                                     // 求めた a(k)（k < n）
int mwords;                                            // nauty の 1 行の語数
int splitLevel = -1, nworkers = 1, workerId = 0;       // 事実 (8) の並列化
long long splitCounter = 0;

// 事実 (7): j 頂点、辺 e 本、最小次数 delta のグラフから、事実 (2) の木を下って n 頂点に至るときの
//   辺の数の上界 fb[j][e][delta]。次に足す頂点の次数 d は
//     (i) d <= delta + 1（頂点を除くと最小次数は高々 1 減るので、子の最小次数 d は親の最小次数 + 1 以下）、
//     (ii) d (t-1) <= 2e（d は子の平均次数以下）、(iii) d <= t、(iv) e + d <= a(t+1)（t+1 < n のとき）
//   を満たし、子の最小次数は d になる。この条件だけを使った最大値を、n 頂点の側から動的計画法で求める
//   （(iv) は e について減少なので、貪欲には決められない）。
constexpr int MAXE = MAXV * (MAXV - 1) / 2;
std::vector<int> fbtab;                                // fb[j][e][delta]、到達できなければ -1
inline int &fb(int j, int e, int delta) { return fbtab[(static_cast<size_t>(j) * (MAXE + 1) + e) * (MAXV + 1) + delta]; }
void build_fb() {
    fbtab.assign(static_cast<size_t>(MAXV + 1) * (MAXE + 1) * (MAXV + 1), -1);
    for (int e = 0; e <= MAXE; e++) for (int dl = 0; dl <= MAXV; dl++) fb(n, e, dl) = e;
    for (int t = n - 1; t >= 1; t--)
        for (int e = 0; e <= t * (t - 1) / 2; e++)
            for (int dl = 0; dl <= t; dl++) {
                int dm = dl + 1;
                if (dm > t) dm = t;
                if (t >= 2 && 2 * e / (t - 1) < dm) dm = 2 * e / (t - 1);
                if (t + 1 < n && exk[t + 1] - e < dm) dm = exk[t + 1] - e;
                int best = -1;
                for (int d = 0; d <= dm; d++) { const int v = fb(t + 1, e + d, d); if (v > best) best = v; }
                fb(t, e, dl) = best;
            }
}

// 事実 (4): H[s] = 親の中で s と長さ 4 の道で結ばれる頂点の集合
void paths4(int k, const uint32_t *adj, uint32_t *H) {
    for (int s = 0; s < k; s++) {
        uint32_t res = 0;
        for (uint32_t A = adj[s]; A; A &= A - 1) {
            const int a = __builtin_ctz(A);
            for (uint32_t B = adj[a] & ~(1u << s); B; B &= B - 1) {
                const int b = __builtin_ctz(B);
                for (uint32_t C = adj[b] & ~((1u << s) | (1u << a)); C; C &= C - 1) {
                    const int c = __builtin_ctz(C);
                    res |= adj[c] & ~((1u << s) | (1u << a) | (1u << b));   // t != s, a, b（t != c は自明）
                }
            }
        }
        H[s] = res;
    }
}

// 頂点の色分け（同型で保たれる）: 次数から始め、「自分の色と近傍の色の多重集合」のハッシュで細分し、
// 色の数が増えなくなるまで繰り返す（color refinement）。色はハッシュ値の順位なので、同型写像は色を保つ
// （ハッシュの衝突があっても、色分けが粗くなるだけで同型不変であることは変わらない）。
inline uint64_t mix(uint64_t x) {
    x += 0x9E3779B97F4A7C15ULL;
    x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL;
    x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL;
    return x ^ (x >> 31);
}
int refine(int nv, const uint32_t *adj, int *col) {
    for (int i = 0; i < nv; i++) col[i] = __builtin_popcount(adj[i]);
    int ncol = -1;
    for (int round = 0; round < nv; round++) {
        uint64_t h[MAXV], sorted[MAXV];
        for (int i = 0; i < nv; i++) {
            uint64_t s = 0;
            for (uint32_t A = adj[i]; A; A &= A - 1) s += mix(static_cast<uint64_t>(col[__builtin_ctz(A)]));
            h[i] = mix(static_cast<uint64_t>(col[i]) * 0x100000001B3ULL ^ s);
            sorted[i] = h[i];
        }
        std::sort(sorted, sorted + nv);
        const int nc = static_cast<int>(std::unique(sorted, sorted + nv) - sorted);
        for (int i = 0; i < nv; i++) col[i] = static_cast<int>(std::lower_bound(sorted, sorted + nc, h[i]) - sorted);
        if (nc == ncol) break;
        ncol = nc;
    }
    return ncol;
}

// 頂点の簡単な不変量: 近傍の次数の和と、頂点を含む三角形の数
inline uint64_t inv1(const uint32_t *adj, int w) {
    uint64_t s = 0, tri = 0;
    for (uint32_t A = adj[w]; A; A &= A - 1) {
        const int u = __builtin_ctz(A);
        s += static_cast<uint64_t>(__builtin_popcount(adj[u]));
        tri += static_cast<uint64_t>(__builtin_popcount(adj[u] & adj[w]));
    }
    return s * 1024 + tri / 2;
}

// nauty に渡す初期の色分け（事実 (9)）: 頂点を (次数, inv1) の昇順に並べ、値が同じものを同じ色にする。
// 色は同型で保たれる量だけで決まり、色の並び順も値の順なので、標準形と軌道は色なしの場合と同じ意味をもつ
// （どの自己同型も次数と inv1 を保つ）。
void set_partition(int nv, const uint32_t *adj, int *lab, int *ptn) {
    uint64_t kv[MAXV];
    for (int i = 0; i < nv; i++) {
        kv[i] = (static_cast<uint64_t>(__builtin_popcount(adj[i])) << 48) | inv1(adj, i);
        lab[i] = i;
    }
    std::sort(lab, lab + nv, [&](int a, int b) { return kv[a] < kv[b]; });
    for (int i = 0; i < nv; i++) ptn[i] = (i + 1 < nv && kv[lab[i]] == kv[lab[i + 1]]) ? 1 : 0;
}

// 親の自己同型群の生成元（nauty の userautomproc で集める）
std::vector<std::vector<int>> *genSink = nullptr;
void collect_gen(int, int *perm, int *, int, int, int nv) {
    if (genSink) genSink->push_back(std::vector<int>(perm, perm + nv));
}

// 親 P（k 頂点）の自己同型群の生成元を gens に入れ、群の位数が CAP 以下なら true
constexpr double GROUP_CAP = 5000.0;
bool parent_group(int k, const uint32_t *adj, std::vector<std::vector<int>> &gens) {
    graph g[MAXV * 4];
    int lab[MAXV], ptn[MAXV], orbits[MAXV];
    static DEFAULTOPTIONS_GRAPH(options);
    statsblk stats;
    options.defaultptn = FALSE;
    options.userautomproc = collect_gen;
    EMPTYGRAPH(g, mwords, k);
    for (int i = 0; i < k; i++)
        for (uint32_t A = adj[i]; A; A &= A - 1) {
            const int j = __builtin_ctz(A);
            if (j > i) ADDONEEDGE(g, i, j, mwords);
        }
    set_partition(k, adj, lab, ptn);
    gens.clear();
    genSink = &gens;
    densenauty(g, lab, ptn, orbits, &options, &stats, mwords, k, NULL);
    genSink = nullptr;
    return stats.grpsize2 == 0 && stats.grpsize1 <= GROUP_CAP;
}

// 事実 (6): S が Aut(P) による軌道の中で（ビット列の整数として）最小か。
//   軌道の大きさは群の位数（<= GROUP_CAP）以下。訪問済みの判定は世代番号つきのハッシュ表で行う。
constexpr int HT = 1 << 14;                            // > 2 * GROUP_CAP
uint32_t htKey[HT], htGen[HT], htStamp = 0;
uint32_t orbitBuf[static_cast<int>(GROUP_CAP) + 1];
bool orbit_min(uint32_t S, const std::vector<std::vector<int>> &gens) {
    if (gens.empty()) return true;
    if (++htStamp == 0) { std::memset(htGen, 0, sizeof htGen); htStamp = 1; }
    auto insert = [&](uint32_t x) {                    // 新しく入れたら true
        uint32_t h = static_cast<uint32_t>(mix(x)) & (HT - 1);
        while (htGen[h] == htStamp) {
            if (htKey[h] == x) return false;
            h = (h + 1) & (HT - 1);
        }
        htGen[h] = htStamp; htKey[h] = x;
        return true;
    };
    int len = 0;
    orbitBuf[len++] = S;
    insert(S);
    for (int h = 0; h < len; h++)
        for (const auto &pm : gens) {
            uint32_t img = 0;
            for (uint32_t X = orbitBuf[h]; X; X &= X - 1) img |= 1u << pm[__builtin_ctz(X)];
            if (img < S) return false;
            if (insert(img)) {
                if (len > static_cast<int>(GROUP_CAP)) { std::fprintf(stderr, "\nInternal error: orbit too large.\n"); std::exit(2); }
                orbitBuf[len++] = img;
            }
        }
    return true;
}

// 標準的な最小次数の頂点（事実 (2) の規則）: 最小次数の頂点のうち、(inv1, 色) が辞書式で最大のもの、
// その中で nauty の標準ラベルが最大のもの。key[i] = inv1 * 2^32 + 色（最小次数の頂点だけ使う）。
// 子 G（nv 頂点、新しい頂点は nv-1）の標準形を cankey に入れ、新しい頂点がその軌道に入るかを返す。
bool canonical_child(int nv, const uint32_t *adj, const uint64_t *key, std::string &cankey) {
    graph g[MAXV * 4], cg[MAXV * 4];
    int lab[MAXV], ptn[MAXV], orbits[MAXV];
    static DEFAULTOPTIONS_GRAPH(options);
    statsblk stats;
    options.getcanon = TRUE;
    options.defaultptn = FALSE;
    EMPTYGRAPH(g, mwords, nv);
    for (int i = 0; i < nv; i++)
        for (uint32_t A = adj[i]; A; A &= A - 1) {
            const int j = __builtin_ctz(A);
            if (j > i) ADDONEEDGE(g, i, j, mwords);
        }
    set_partition(nv, adj, lab, ptn);
    densenauty(g, lab, ptn, orbits, &options, &stats, mwords, nv, cg);
    cankey.assign(reinterpret_cast<const char *>(cg), sizeof(graph) * static_cast<size_t>(mwords) * nv);
    const int dv = __builtin_popcount(adj[nv - 1]);    // v は最小次数（事実 (4)）
    uint64_t maxkey = 0;
    for (int i = 0; i < nv; i++)
        if (__builtin_popcount(adj[i]) == dv && key[i] > maxkey) maxkey = key[i];
    for (int i = nv - 1; i >= 0; i--) {                // 標準ラベルが最大のもの
        const int w = lab[i];
        if (__builtin_popcount(adj[w]) == dv && key[w] == maxkey) return orbits[w] == orbits[nv - 1];
    }
    return false;
}

// 新しい頂点 v = nv-1 が標準的な頂点の候補かを、不変量だけで判定する（v は最小次数であることが
// 事実 (4) で保証済み）。戻り値 0: 候補でない（棄却）、1: v が唯一の候補（受理）、2: nauty が必要。
// key には最小次数の頂点の (inv1, 色) を入れる（inv1 だけで決まるときは色を計算しない）。
int quick_test(int nv, const uint32_t *adj, uint64_t *key) {
    const int v = nv - 1, dv = __builtin_popcount(adj[v]);
    const uint64_t iv = inv1(adj, v);
    bool tie = false;
    for (int i = 0; i < v; i++) {
        if (__builtin_popcount(adj[i]) != dv) continue;
        const uint64_t t = inv1(adj, i);
        if (t > iv) return 0;
        if (t == iv) tie = true;
        key[i] = t << 32;
    }
    key[v] = iv << 32;
    if (!tie) return 1;
    int col[MAXV];
    refine(nv, adj, col);
    for (int i = 0; i < nv; i++)
        if (__builtin_popcount(adj[i]) == dv) key[i] = (inv1(adj, i) << 32) | static_cast<uint64_t>(col[i]);
    for (int i = 0; i < v; i++) {
        if (__builtin_popcount(adj[i]) != dv) continue;
        if (key[i] > key[v]) return 0;
        if (key[i] == key[v]) return 2;
    }
    return 1;
}

void gen(int k, const uint32_t *adj, int e);

// 親（k 頂点、辺 e 本）に、近傍 S の頂点を足す。cand から r 個を独立に選ぶ
struct ChildCtx {
    int k, e, d;
    const uint32_t *adj;
    const uint32_t *H;
    std::unordered_set<std::string> *seen;
    int group_state;                                   // 親の群: 0 = 未計算、1 = 位数 <= CAP、2 = それより大
    std::vector<std::vector<int>> *gens;               // 親の自己同型群の生成元
    bool final_found;
};

void pick(ChildCtx &cx, uint32_t S, uint32_t cand, int r) {
    if (r == 0) {
        if (cx.k + 1 == n) { cx.final_found = true; return; }   // 事実 (5)
        uint32_t child[MAXV];
        for (int i = 0; i < cx.k; i++) child[i] = cx.adj[i] | (((S >> i) & 1) ? (1u << cx.k) : 0u);
        child[cx.k] = S;
        uint64_t key[MAXV];
        const int q = quick_test(cx.k + 1, child, key);
        if (q == 0) return;
        if (q == 1) {                                  // 事実 (6): v が唯一の候補なら、軌道で重複を除く
            if (cx.group_state == 0) cx.group_state = parent_group(cx.k, cx.adj, *cx.gens) ? 1 : 2;
            if (cx.group_state == 1) {
                if (orbit_min(S, *cx.gens)) gen(cx.k + 1, child, cx.e + cx.d);
                return;
            }
        }
        std::string cankey;
        if (!canonical_child(cx.k + 1, child, key, cankey)) return;
        if (!cx.seen->insert(cankey).second) return;  // 同じ親からの同型な子
        gen(cx.k + 1, child, cx.e + cx.d);
        return;
    }
    if (__builtin_popcount(cand) < r) return;
    while (cand && !cx.final_found) {
        const int u = __builtin_ctz(cand);
        cand &= cand - 1;
        if (__builtin_popcount(cand) + 1 < r) return;
        pick(cx, S | (1u << u), cand & ~cx.H[u], r - 1);
    }
}

void gen(int k, const uint32_t *adj, int e) {
    if (k == splitLevel && (splitCounter++ % nworkers) != workerId) return;   // 事実 (8): 他のプロセスの担当
    int deg[MAXV], mindeg = MAXV;
    for (int i = 0; i < k; i++) { deg[i] = __builtin_popcount(adj[i]); if (deg[i] < mindeg) mindeg = deg[i]; }
    if (fb(k, e, mindeg) < Tgt) return;               // 事実 (7)
    uint32_t H[MAXV];
    paths4(k, adj, H);
    std::unordered_set<std::string> seen;
    std::vector<std::vector<int>> gens;
    int group_state = 0;                               // 親の群は必要になったときに計算する
    int dmin = L[k + 1] - e;
    if (dmin < 0) dmin = 0;
    int dmax = (mindeg + 1 < k) ? mindeg + 1 : k;
    // 最後の段は大きい d から調べ、見つかれば終わり
    for (int dd = 0; dd <= dmax - dmin; dd++) {
        const int d = (k + 1 == n) ? dmax - dd : dmin + dd;
        if (k + 1 == n && e + d <= bestE) break;
        if (k + 1 < n && fb(k + 1, e + d, d) < Tgt) continue;   // 事実 (7)
        uint32_t forced = 0;
        for (int i = 0; i < k; i++) if (deg[i] == d - 1) forced |= 1u << i;
        bool ok = true;
        for (int i = 0; i < k; i++) if (deg[i] < d - 1) ok = false;
        if (!ok) continue;
        uint32_t fh = 0;
        for (uint32_t F = forced; F; F &= F - 1) fh |= H[__builtin_ctz(F)];
        if (fh & forced) continue;                     // 必ず入る頂点どうしが長さ 4 の道で結ばれる
        const int r = d - __builtin_popcount(forced);
        if (r < 0) continue;
        const uint32_t all = (k == 32) ? ~0u : ((1u << k) - 1);
        const uint32_t cand = all & ~forced & ~fh;
        ChildCtx cx{k, e, d, adj, H, &seen, group_state, &gens, false};
        pick(cx, forced, cand, r);
        group_state = cx.group_state;
        if (k + 1 == n && cx.final_found) { bestE = e + d; break; }
    }
}

bool parse_limit(const char *text, long lo, long hi, int *value) {
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

}  // namespace

int main(int argc, char **argv) {
    int NMAX = 16;
    const long ncpu = sysconf(_SC_NPROCESSORS_ONLN);
    int P = (ncpu >= 1 && ncpu <= 256) ? static_cast<int>(ncpu) : 1;
    if (argc == 2 && (!std::strcmp(argv[1], "--help") || !std::strcmp(argv[1], "-h"))) {
        std::printf("Usage: %s [NMAX [PROCS]] (1 <= NMAX <= %d, default 16; 1 <= PROCS <= 256, default: number of CPUs)\n", argv[0], MAXV);
        return 0;
    }
    if (argc > 3 || (argc >= 2 && !parse_limit(argv[1], 1, MAXV, &NMAX)) || (argc == 3 && !parse_limit(argv[2], 1, 256, &P))) {
        std::fprintf(stderr, "Usage: %s [NMAX [PROCS]]; NMAX in 1..%d, PROCS in 1..256.\n", argv[0], MAXV);
        return 1;
    }
    mwords = SETWORDSNEEDED(MAXV);
    nauty_check(WORDSIZE, mwords, MAXV, NAUTYVERSIONID);
    std::vector<int> a(NMAX + 1, 0);
    for (n = 1; n <= NMAX; n++) {
        int E0 = 0;                                    // 事実 (1)
        for (int b = 2; b <= n - 1; b++) if (a[b] + a[n - b + 1] > E0) E0 = a[b] + a[n - b + 1];
        if (n == 1) a[n] = 0;
        else {
            L[n] = E0 + 1;                             // 事実 (3)
            Tgt = E0 + 1;
            for (int k = 1; k < n; k++) exk[k] = a[k];
            build_fb();
            for (int k = n - 1; k >= 1; k--) L[k] = L[k + 1] - (2 * L[k + 1]) / (k + 1);
            bestE = -1;
            if (L[1] <= 0) {
                const uint32_t adj1[MAXV] = {0};
                if (P <= 1 || n < 12) {
                    splitLevel = -1;
                    gen(1, adj1, 0);
                } else {
                    // 事実 (8): 第 splitLevel 段の頂点を DFS の順に番号付けし、番号 mod P で P 個のプロセスに分ける
                    splitLevel = std::min(10, n - 2);
                    std::vector<int> fds;
                    std::vector<pid_t> pids;
                    std::fflush(stdout);
                    for (int w = 0; w < P; w++) {
                        int fd[2];
                        if (pipe(fd) != 0) { std::perror("pipe"); return 1; }
                        const pid_t pid = fork();
                        if (pid < 0) { std::perror("fork"); return 1; }
                        if (pid == 0) {
                            close(fd[0]);
                            nworkers = P; workerId = w; splitCounter = 0;
                            gen(1, adj1, 0);
                            const int v = bestE;
                            const bool ok = write(fd[1], &v, sizeof v) == static_cast<ssize_t>(sizeof v);
                            close(fd[1]);
                            _exit(ok ? 0 : 1);
                        }
                        close(fd[1]);
                        fds.push_back(fd[0]);
                        pids.push_back(pid);
                    }
                    for (int w = 0; w < P; w++) {
                        int v = -1;
                        const bool ok = read(fds[w], &v, sizeof v) == static_cast<ssize_t>(sizeof v);
                        close(fds[w]);
                        int status = 0;
                        if (waitpid(pids[w], &status, 0) != pids[w] || !ok || !WIFEXITED(status) || WEXITSTATUS(status) != 0) {
                            std::fprintf(stderr, "\nWorker process failed at n=%d.\n", n);
                            return 2;
                        }
                        if (v > bestE) bestE = v;
                    }
                }
            }
            a[n] = (bestE > E0) ? bestE : E0;
        }
        if (std::printf(n == 1 ? "%d" : ", %d", a[n]) < 0 || std::fflush(stdout) != 0) {
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
