/*
 * Erdős Problem #581
 * f(m) = 辺が m 本で三角形を含まないグラフ G 全体での、G の最大 2 部部分グラフの辺数
 *        （= 最大カット）の最小値。
 *        すなわち「三角形のない m 辺グラフは必ず f(m) 辺の 2 部部分グラフを含み、
 *        f(m) より大きい値では成り立たない」。
 * m = 0..M を計算し、"m f(m)" を 1 行ずつ標準出力に書く（ファイルは作らない）。
 * f(0) = 0（辺のないグラフは三角形を含まず、2 部部分グラフの辺数は 0）。
 *
 * グラフの列挙には nauty の geng を使う（三角形なし -t、2 連結 -C）。
 * erdos581_01.cpp との違い: 列挙を「連結・最小次数 2 以上」から「2 連結」に絞り（事実 (2b)）、
 * 頂点数の打ち切りを n-1 >= best から n >= best に強めた（事実 (5)、耳分解による）。
 * geng のコマンド名は環境変数 GENG で指定できる（既定は geng、なければ nauty-geng を試す）。
 *
 * 使う事実（どれも証明つき、結果を変えない）:
 *  (0) 孤立点は辺にも最大カットにも影響しないので、孤立点のないグラフだけを考えればよい。
 *  (1) 葉（次数 1 の頂点 v、辺 uv）があるグラフ G では maxcut(G) = maxcut(G - v) + 1
 *      （v を u と反対側に置けば辺 uv は必ずカットに入る）。G - v は三角形のない m-1 辺グラフ
 *      なので maxcut(G) >= f(m-1) + 1。逆に f(m-1) を達成するグラフに葉を 1 本つけると
 *      三角形は生じず maxcut = f(m-1) + 1。よって葉のあるグラフ全体での最小値は f(m-1) + 1。
 *  (2) 非連結なグラフ（葉なし）の最大カットは成分ごとの最大カットの和なので、
 *      辺数 a と m-a の部分に分けて f(a) + f(m-a) 以上。互いに素な和で等号が達成できる。
 *  (2b) 切断点 v をもつ連結グラフ G は、v だけを共有し辺を分け合う 2 つの部分 G1, G2
 *      （どちらも辺を 1 本以上もつ）に分かれる。G1, G2 の最大カットを、v が同じ側になるよう
 *      一方を全反転して合わせれば maxcut(G) = maxcut(G1) + maxcut(G2) >= f(a) + f(m-a)。
 *      よって切断点をもつグラフは (2) の候補を下回らず、2 連結グラフだけを調べればよい。
 *      （葉をもつグラフも、K2 を除き切断点をもつ。）
 *  (3) 残りは 2 連結（特に連結で最小次数 2 以上）のグラフ。次数の和 2m >= 2n より頂点数 n <= m。
 *      また三角形のない非 2 部グラフは長さ 5 以上の奇閉路を含むので n >= 5
 *      （2 部グラフなら最大カットは m で、(1) の候補 f(m-1)+1 <= m を下回らない）。
 *  (4) Mantel の定理より、三角形のない n 頂点グラフの辺数は floor(n^2/4) 以下なので、
 *      m > floor(n^2/4) の n は調べなくてよい（geng もこの範囲を受け付けない）。
 *  (5) 2 連結で閉路でない n 頂点グラフ G の最大カットは n 以上。
 *      G は耳分解をもつ: 閉路 C に、端点が既存の相異なる頂点で内部が新しいパス（耳）を順に加える。
 *      閉路でないので耳が 1 つ以上ある。C と最初の耳は、2 頂点 x, y を結ぶ内部で交わらない
 *      3 本のパス（θ グラフ、辺 a+b+c 本、頂点 a+b+c-1 個）をなす。3 つの閉路の長さの和
 *      2(a+b+c) は偶数なので奇閉路は高々 2 つで、2 つあればそれらが共有するパスの辺を 1 本
 *      カットから外せば 2 部になる。よって θ の最大カットは (a+b+c) - 1 = 頂点数 以上。
 *      残りの各耳（長さ l、新しい頂点 l-1 個）は、両端の側が決まっていても内部の頂点を交互に
 *      置けば l-1 本以上の辺をカットに入れられる。合計で最大カット >= n。
 *      よって n >= best（現在の候補値）となる n 以降は最小値を更新しない（n について単調）。
 *      閉路そのものは別に扱う: C_m（m 奇数 >= 5）の最大カットは m-1、偶数なら m（候補 m-1 を加える）。
 *  以上から f(m) = min( f(m-1) + 1,  min_{1<=a<m} f(a) + f(m-a),
 *                      min{ maxcut(G) : G 2 連結・三角形なし・m 辺・5 <= n <= m } )。
 *
 * 最大カットの計算: 現在の候補値 best（上の最初の 2 つの最小値から始め、見つかるたびに下げる）
 *   より小さいかだけが問題なので、
 *   ・まず局所探索（1 頂点ずつ移して改善する）でよいカットを作り、best 以上なら打ち切る。
 *   ・そうでなければ、最後の頂点の側を固定して 2^(n-1) 通りを Gray 符号で 1 頂点ずつ変えながら
 *     調べる。カットが best 以上になった時点で打ち切る（このグラフは最小値を更新しない）。
 *     最後まで調べたら、そのときの最大値がこのグラフの最大カットで、best 未満なので更新する。
 *
 * 検証: m <= 16 を、geng の出力をすべて最大カットの総当たりにかける別のスクリプトと照合した。
 *
 * コンパイル: g++ -O2 -std=c++17 -Wall -Wextra -Wpedantic -Werror -pthread 401972_02.cpp -o 401972_02
 * 実行:       ./401972_02 [M [J]]   （M は 1..40、既定値 20。J は 1..64、既定値 1）
 */
#include <atomic>
#include <cerrno>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <thread>
#include <vector>

namespace {

constexpr int MAXM = 40;                  // n <= m <= 40 で 64 bit の Gray 符号に収まる
constexpr int MAXN = MAXM;

struct Graph {
    int n = 0;
    int m = 0;
    int eu[MAXM * MAXM], ev[MAXM * MAXM];
    std::vector<int> adj[MAXN];
};

// graph6 を読む（n <= 62 の 1 文字の頂点数のみ）。失敗なら false。
bool parse_graph6(const char *s, Graph &g) {
    size_t len = std::strlen(s);
    while (len > 0 && (s[len - 1] == '\n' || s[len - 1] == '\r')) len--;
    if (len == 0) return false;
    int n = s[0] - 63;
    if (n < 1 || n > MAXN) return false;
    size_t need = 1 + (static_cast<size_t>(n) * (n - 1) / 2 + 5) / 6;
    if (len != need) return false;
    g.n = n;
    g.m = 0;
    for (int i = 0; i < n; i++) g.adj[i].clear();
    size_t bit = 0;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++) {
            int c = s[1 + bit / 6] - 63;
            if (c < 0 || c > 63) return false;
            if ((c >> (5 - bit % 6)) & 1) {
                if (g.m >= MAXM * MAXM) return false;
                g.eu[g.m] = i; g.ev[g.m] = j; g.m++;
                g.adj[i].push_back(j);
                g.adj[j].push_back(i);
            }
            bit++;
        }
    return true;
}

// 局所探索で得たカットの値（下界）
int local_search_cut(const Graph &g) {
    std::vector<int> side(g.n, 0);
    // BFS で交互に色を付けて初期解にする（2 部グラフならこれで m）
    std::vector<int> seen(g.n, 0), q;
    for (int s = 0; s < g.n; s++) {
        if (seen[s]) continue;
        seen[s] = 1; q.assign(1, s);
        for (size_t h = 0; h < q.size(); h++) {
            int v = q[h];
            for (int w : g.adj[v]) if (!seen[w]) { seen[w] = 1; side[w] = side[v] ^ 1; q.push_back(w); }
        }
    }
    bool improved = true;
    while (improved) {
        improved = false;
        for (int v = 0; v < g.n; v++) {
            int same = 0, diff = 0;
            for (int w : g.adj[v]) (side[w] == side[v] ? same : diff)++;
            if (same > diff) { side[v] ^= 1; improved = true; }
        }
    }
    int cut = 0;
    for (int e = 0; e < g.m; e++) cut += side[g.eu[e]] != side[g.ev[e]];
    return cut;
}

// 最大カットが threshold 未満ならその値を、threshold 以上なら threshold を返す
int maxcut_below(const Graph &g, int threshold) {
    if (local_search_cut(g) >= threshold) return threshold;
    const int n = g.n;
    std::vector<int> side(n, 0);
    int cut = 0, best = 0;
    // same_cnt[v] = v と同じ側にいる隣接点の数
    std::vector<int> same_cnt(n);
    for (int v = 0; v < n; v++) same_cnt[v] = static_cast<int>(g.adj[v].size());
    // 頂点 n-1 の側は固定。残り n-1 頂点を Gray 符号で 1 つずつ反転する。
    const unsigned long long total = 1ULL << (n - 1);
    for (unsigned long long step = 1; step < total; step++) {
        int v = __builtin_ctzll(step);   // 反転する頂点（0 .. n-2）
        int deg = static_cast<int>(g.adj[v].size());
        // 反転で、同じ側だった辺がカットに入り、異なる側だった辺がカットから出る
        cut += same_cnt[v] - (deg - same_cnt[v]);
        for (int w : g.adj[v]) same_cnt[w] += (side[w] == side[v]) ? -1 : +1;
        side[v] ^= 1;
        same_cnt[v] = deg - same_cnt[v];
        if (cut > best) {
            best = cut;
            if (best >= threshold) return threshold;
        }
    }
    return best;
}

bool parse_limit(const char *text, int maximum, int *value) {
    if (!*text) return false;
    for (const char *p = text; *p; p++)
        if (*p < '0' || *p > '9') return false;
    errno = 0;
    char *end;
    long parsed = std::strtol(text, &end, 10);
    if (errno == ERANGE || *end || parsed < 1 || parsed > maximum) return false;
    *value = static_cast<int>(parsed);
    return true;
}

std::string geng_command() {
    const char *env = std::getenv("GENG");
    if (env && *env) {
        // 環境変数は英数字と / . _ - のみ許す（シェルに渡すため）
        for (const char *p = env; *p; p++) {
            char c = *p;
            bool ok = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') ||
                      c == '/' || c == '.' || c == '_' || c == '-';
            if (!ok) { std::fprintf(stderr, "GENG contains unsupported characters.\n"); std::exit(1); }
        }
        return env;
    }
    if (std::system("command -v geng >/dev/null 2>&1") == 0) return "geng";
    if (std::system("command -v nauty-geng >/dev/null 2>&1") == 0) return "nauty-geng";
    std::fprintf(stderr, "geng (nauty) not found; set GENG to its path.\n");
    std::exit(1);
}

// geng の出力の res 番目の部分（全 mod 個）を調べ、best を下げる。失敗なら false。
// geng の res/mod 指定は出力を mod 個の互いに素な部分に分けるので、全部分を合わせると
// 全グラフをちょうど 1 回ずつ調べたことになる。
bool scan_part(const std::string &geng, int n, int m, int res, int mod, std::atomic<int> &best) {
    char cmd[256];
    int length;
    if (mod == 1)
        length = std::snprintf(cmd, sizeof cmd, "%s -tCq %d %d:%d", geng.c_str(), n, m, m);
    else
        length = std::snprintf(cmd, sizeof cmd, "%s -tCq %d %d:%d %d/%d", geng.c_str(), n, m, m, res, mod);
    if (length < 0 || static_cast<size_t>(length) >= sizeof cmd) {
        std::fprintf(stderr, "geng command exceeds the command buffer.\n");
        return false;
    }
    FILE *in = popen(cmd, "r");
    if (!in) { std::perror("popen geng"); return false; }
    static thread_local Graph g;
    char line[1024];
    bool ok = true;
    while (std::fgets(line, sizeof line, in)) {
        if (!parse_graph6(line, g) || g.m != m || g.n != n) {
            std::fprintf(stderr, "Unexpected geng output for n=%d, m=%d.\n", n, m);
            ok = false;
            break;
        }
        int cur = best.load();
        int v = maxcut_below(g, cur);
        while (v < cur && !best.compare_exchange_weak(cur, v)) {}   // best = min(best, v)
    }
    if (std::ferror(in)) {
        std::fprintf(stderr, "Error reading geng output for n=%d, m=%d.\n", n, m);
        ok = false;
    }
    int st = pclose(in);
    if (ok && st != 0) {
        std::fprintf(stderr, "geng failed (status %d) for n=%d, m=%d.\n", st, n, m);
        ok = false;
    }
    return ok;
}

}  // namespace

int main(int argc, char **argv) {
    int M = 20, J = 1;
    if (argc == 2 && (!std::strcmp(argv[1], "--help") || !std::strcmp(argv[1], "-h"))) {
        std::printf("Usage: %s [M [J]] (M is 1..%d, default 20; J = number of parallel geng processes, 1..64, default 1). Requires nauty geng.\n", argv[0], MAXM);
        return 0;
    }
    if (argc > 3 || (argc >= 2 && !parse_limit(argv[1], MAXM, &M)) ||
        (argc == 3 && (!parse_limit(argv[2], 64, &J)))) {
        std::fprintf(stderr, "Usage: %s [M [J]]; M in 1..%d, J in 1..64.\n", argv[0], MAXM);
        return 1;
    }
    const std::string geng = geng_command();
    std::vector<int> f(M + 1, 0);                         // f(0) = 0
    if (std::printf("0 0\n") < 0 || std::fflush(stdout) != 0) {
        std::perror("write standard output");
        return 1;
    }
    for (int m = 1; m <= M; m++) {
        int init = f[m - 1] + 1;                          // 事実 (1)
        if (m >= 5 && m % 2 == 1 && m - 1 < init) init = m - 1;   // 事実 (5): 奇閉路 C_m
        for (int a = 1; a < m; a++)                       // 事実 (2)
            if (f[a] + f[m - a] < init) init = f[a] + f[m - a];
        std::atomic<int> best(init);
        for (int n = 5; n <= m; n++) {                    // 事実 (3)
            if (m > n * n / 4) continue;                  // 事実 (4): Mantel の定理
            if (n >= best.load()) break;                  // 事実 (5): 閉路でなければ maxcut >= n
            std::vector<std::thread> workers;
            std::vector<char> ok(J, 1);
            for (int r = 0; r < J; r++)
                workers.emplace_back([&, r] { ok[r] = scan_part(geng, n, m, r, J, best) ? 1 : 0; });
            for (auto &t : workers) t.join();
            for (int r = 0; r < J; r++) if (!ok[r]) return 1;
        }
        f[m] = best.load();
        if (std::printf("%d %d\n", m, f[m]) < 0 || std::fflush(stdout) != 0) {
            std::perror("write standard output");
            return 1;
        }
    }
    return 0;
}
