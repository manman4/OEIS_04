/*
 * Erdős Problem #160  (A402186)
 * a(n) = h(n) = {1, ..., n} を塗り分けて、どの 4 項等差数列にも 3 色以上が現れるように
 *        するのに必要な最小の色数。
 * n = 1..N の h(n) を、求まった順に "1, 1, 1, 3, ..." の形で標準出力に書き出す
 * （ファイルは作らない）。
 *
 * 使う事実（どれも証明つき、結果を変えない）:
 *  (1) h は n について単調非減少: {1..n} の塗り分けを {1..n-1} に制限しても条件を満たす。
 *      よって h(n) は h(n-1), h(n-1)+1, ... の順に「その色数で {1..n} を塗れるか」を調べ、
 *      最初に塗れた色数である。塗れない判定（全探索）は色数が増えるときだけ起こる。
 *  (2) n <= 3 では 4 項等差数列がないので h(n) = 1。n >= 4 では {1,2,3,4} 自体が
 *      4 項等差数列なので 3 色以上が必要（h(n) >= 3）。
 *  (3) 探索: 1, 2, 3, ... の順に色を決める。色は「まだ使っていない色のうち番号最小のもの」
 *      までしか使わない（色の付け替えで移り合う塗り分けを 1 つだけ調べる）。
 *      i に色を付けるとき、i で終わる 4 項等差数列 (i-3d, i-2d, i-d, i) がすべて 3 色以上か調べる
 *      （どの 4 項等差数列も最大の項に色を付けた時点で 1 度だけ調べられる）。
 *  (4) 先読みによる枝刈り: i まで色を決めたとき、i より後で n 以下の位置 x について、x で終わる
 *      4 項等差数列のうち前の 3 項がすべて決まっているもの（x - d <= i）を調べる。
 *        ・前の 3 項が 1 色なら、x の色によらず 2 色以下になるので行き詰まり。
 *        ・前の 3 項がちょうど 2 色なら、x はその 2 色以外でなければならない。
 *      x に使える色がなくなれば、その枝から {1..n} の塗り分けは作れない。
 *
 * 検証: 1 色ずつ増やして最長を求める素朴な探索（(4) なし）と、n <= 35 で一致することを確かめた
 *       （3 色で 12、4 色で 22、5 色で 35 まで塗れる）。
 *
 * コンパイル: g++ -O2 -std=c++17 -Wall -Wextra -Wpedantic -Werror 402186_01.cpp -o 402186_01
 * 実行:       ./402186_01 [N]   （N の既定値 40、1 <= N <= MAXLEN）
 */
#include <cerrno>
#include <cstdio>
#include <cstdlib>
#include <cstring>

namespace {

constexpr int MAXLEN = 2000;
constexpr int MAXK = 30;                  // 色の数の上限（ビット集合に収まる範囲）

int col[MAXLEN + 2];
int K, target;

// 4 色の中の相異なる色の数
inline int distinct4(int a, int b, int c, int e) {
    int s = 1;
    if (b != a) s++;
    if (c != a && c != b) s++;
    if (e != a && e != b && e != c) s++;
    return s;
}

// i に付けた色で、i で終わる 4 項等差数列がすべて 3 色以上か（事実 (3)）
bool check_last(int i) {
    for (int d = 1; i - 3 * d >= 1; d++)
        if (distinct4(col[i - 3 * d], col[i - 2 * d], col[i - d], col[i]) < 3) return false;
    return true;
}

// 事実 (4): 1..i が決まったとき、i+1 .. target の各位置に使える色が残っているか
bool lookahead_ok(int i) {
    const long long full = (1LL << K) - 1;
    for (int x = i + 1; x <= target; x++) {
        long long forbid = 0;
        for (int d = (x - i > 1 ? x - i : 1); x - 3 * d >= 1; d++) {
            int a = col[x - 3 * d], b = col[x - 2 * d], c = col[x - d];
            if (a == b && b == c) return false;          // 前の 3 項が 1 色
            if (a != b && b != c && a != c) continue;     // 3 色なら x は自由
            forbid |= (1LL << a) | (1LL << b) | (1LL << c);   // ちょうど 2 色: 禁止
            if ((forbid & full) == full) return false;
        }
    }
    return true;
}

// 1..i-1 が決定済み。i..target を K 色で塗れるか
bool feasible_dfs(int i, int used) {
    if (i > target) return true;
    int maxc = used < K ? used + 1 : K;                    // 事実 (3) の色の順序
    for (int c = 0; c < maxc; c++) {
        col[i] = c;
        if (!check_last(i)) continue;
        if (!lookahead_ok(i)) continue;                    // 事実 (4)
        if (feasible_dfs(i + 1, c == used ? used + 1 : used)) return true;
    }
    return false;
}

// {1..n} を k 色で塗れるか
bool feasible(int n, int k) {
    K = k;
    target = n;
    return feasible_dfs(1, 0);
}

bool parse_limit(const char *text, int *value) {
    if (!*text) return false;
    for (const char *p = text; *p; p++)
        if (*p < '0' || *p > '9') return false;
    errno = 0;
    char *end;
    long parsed = std::strtol(text, &end, 10);
    if (errno == ERANGE || *end || parsed < 1 || parsed > MAXLEN) return false;
    *value = static_cast<int>(parsed);
    return true;
}

}  // namespace

int main(int argc, char **argv) {
    int N = 40;
    if (argc == 2 && (!std::strcmp(argv[1], "--help") || !std::strcmp(argv[1], "-h"))) {
        std::printf("Usage: %s [N] (1 <= N <= %d; default 40)\n", argv[0], MAXLEN);
        return 0;
    }
    if (argc > 2 || (argc == 2 && !parse_limit(argv[1], &N))) {
        std::fprintf(stderr, "Usage: %s [N]; N must be a decimal integer in 1..%d.\n", argv[0], MAXLEN);
        return 1;
    }
    int h = 1;
    for (int n = 1; n <= N; n++) {
        if (n <= 3) h = 1;                                 // 事実 (2)
        else {
            if (h < 3) h = 3;                              // 事実 (2)
            while (!feasible(n, h)) {                      // 事実 (1)
                h++;
                if (h > MAXK) {
                    std::fprintf(stderr, "\nColor limit %d exceeded.\n", MAXK);
                    return 2;
                }
            }
        }
        if (std::printf(n == 1 ? "%d" : ", %d", h) < 0 || std::fflush(stdout) != 0) {
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
