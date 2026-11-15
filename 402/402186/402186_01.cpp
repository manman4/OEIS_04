/*
 * Erdős Problem #160  (A402186)
 * a(n) = h(n) = {1, ..., n} を塗り分けて、どの 4 項等差数列にも 3 色以上が現れるように
 *        するのに必要な最小の色数。
 * k = 1, 2, ..., K について「k 色で塗れる最大の n」を求め、それから h(n) を出す。
 * h(n) を "1, 1, 1, 3, ..." の形で標準出力に書き出す（ファイルは作らない）。
 *
 * 使う事実（どれも証明つき、結果を変えない）:
 *  (1) h は n について単調非減少: {1..n+1} の塗り分けを {1..n} に制限しても条件を満たす。
 *      よって M(k) = (k 色で塗れる最大の n) とすると、h(n) = min{k : M(k) >= n}。
 *      M(k) も k について単調非減少（使わない色があってもよい）。
 *  (2) n <= 3 では 4 項等差数列がないので h(n) = 1。n >= 4 では {1,2,3,4} 自体が
 *      4 項等差数列なので 3 色以上が必要（h(n) >= 3）。よって M(1) = M(2) = 3。
 *  (3) 探索: 1, 2, 3, ... の順に色を決める。色は「まだ使っていない色のうち番号最小のもの」
 *      までしか使わない（色の付け替えで移り合う塗り分けを 1 つだけ調べる）。
 *      n に色を付けるとき、n で終わる 4 項等差数列 (n-3d, n-2d, n-d, n) がすべて 3 色以上か調べる。
 *      （どの 4 項等差数列も最大の項に色を付けた時点で 1 度だけ調べられる。）
 *  (4) 先読みによる枝刈り: n まで色を決めたとき、n より後の位置 x について、x で終わる
 *      4 項等差数列のうち前の 3 項がすべて決まっているもの（x - d <= n）を調べる。
 *        ・前の 3 項が 1 色なら、x の色によらず 2 色以下になるので行き詰まり。
 *        ・前の 3 項が 2 色なら、x はその 2 色以外でなければならない。
 *      x に使える色（k 色のうち、上の条件で禁止されないもの）がなくなれば、その枝からは
 *      x 以上の長さの塗り分けは作れない。目標は「現在の最長 + 1」に届くかなので、
 *      x <= 現在の最長 + 1 の範囲だけを調べればよい（それより先は目標に関係しない）。
 *
 * 検証: k <= 5 を、(4) を使わない素朴な探索と照合した（M = 3, 3, 12, 22, 35）。
 *
 * コンパイル: g++ -O2 -std=c++17 -Wall -Wextra -Wpedantic -Werror 402186_01.cpp -o 402186_01
 * 実行:       ./402186_01 [K]   （K の既定値 6、1 <= K <= 16）
 */
#include <cerrno>
#include <cstdio>
#include <cstdlib>
#include <cstring>

namespace {

constexpr int MAXLEN = 4096;              // 塗り分けの長さの上限（超えたらエラーで停止）
constexpr int MAXK = 16;

int col[MAXLEN + 2];
int K, best;

// 4 色の中の相異なる色の数
inline int distinct4(int a, int b, int c, int e) {
    int s = 1;
    if (b != a) s++;
    if (c != a && c != b) s++;
    if (e != a && e != b && e != c) s++;
    return s;
}

// n に付けた色で、n で終わる 4 項等差数列がすべて 3 色以上か（事実 (3)）
bool check_last(int n) {
    for (int d = 1; n - 3 * d >= 1; d++)
        if (distinct4(col[n - 3 * d], col[n - 2 * d], col[n - d], col[n]) < 3) return false;
    return true;
}

// 事実 (4): 1..n が決まったとき、n+1 .. limit の各位置に使える色が残っているか
bool lookahead_ok(int n, int limit) {
    const int full = (1 << K) - 1;
    for (int x = n + 1; x <= limit; x++) {
        int forbid = 0;
        // x - d <= n、つまり d >= x - n
        for (int d = (x - n > 1 ? x - n : 1); x - 3 * d >= 1; d++) {
            int a = col[x - 3 * d], b = col[x - 2 * d], c = col[x - d];
            if (a == b && b == c) return false;          // 前の 3 項が 1 色
            if (a != b && b != c && a != c) continue;     // 3 色なら x は自由
            // ちょうど 2 色: その 2 色を禁止
            forbid |= (1 << a) | (1 << b) | (1 << c);
            if ((forbid & full) == full) return false;
        }
    }
    return true;
}

void dfs(int n, int used) {
    // 1..n-1 は決定済み。n に色を付ける。
    if (n - 1 > best) best = n - 1;
    if (n > MAXLEN) {
        std::fprintf(stderr, "\nLength limit %d reached; increase MAXLEN.\n", MAXLEN);
        std::exit(2);
    }
    int maxc = used < K ? used + 1 : K;                    // 事実 (3) の色の順序
    for (int c = 0; c < maxc; c++) {
        col[n] = c;
        if (!check_last(n)) continue;
        if (!lookahead_ok(n, best + 1)) continue;          // 事実 (4)
        dfs(n + 1, c == used ? used + 1 : used);
    }
}

bool parse_limit(const char *text, int *value) {
    if (!*text) return false;
    for (const char *p = text; *p; p++)
        if (*p < '0' || *p > '9') return false;
    errno = 0;
    char *end;
    long parsed = std::strtol(text, &end, 10);
    if (errno == ERANGE || *end || parsed < 1 || parsed > MAXK) return false;
    *value = static_cast<int>(parsed);
    return true;
}

}  // namespace

int main(int argc, char **argv) {
    int KMAX = 6;
    if (argc == 2 && (!std::strcmp(argv[1], "--help") || !std::strcmp(argv[1], "-h"))) {
        std::printf("Usage: %s [K] (1 <= K <= %d; default 6)\n", argv[0], MAXK);
        return 0;
    }
    if (argc > 2 || (argc == 2 && !parse_limit(argv[1], &KMAX))) {
        std::fprintf(stderr, "Usage: %s [K]; K must be a decimal integer in 1..%d.\n", argv[0], MAXK);
        return 1;
    }
    int printed = 0;                                       // h(1..printed) を出力済み
    for (K = 1; K <= KMAX; K++) {
        best = 0;
        dfs(1, 0);
        // M(K) = best。h(n) = K となるのは printed < n <= best（事実 (1)）
        for (int n = printed + 1; n <= best; n++) {
            if (std::printf(n == 1 ? "%d" : ", %d", K) < 0 || std::fflush(stdout) != 0) {
                std::perror("write standard output");
                return 1;
            }
        }
        if (best > printed) printed = best;
        std::fprintf(stderr, "[M(%d) = %d]\n", K, best);
    }
    if (std::printf("\n") < 0 || std::fflush(stdout) != 0) {
        std::perror("write standard output");
        return 1;
    }
    return 0;
}
