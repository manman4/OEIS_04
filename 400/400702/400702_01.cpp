/*
 * Erdős Problem #819  (A400702)
 * a(N) = f(N) = max |(A+A) ∩ [1,N]|  over A ⊆ {1,...,N} with |A| = s = floor(sqrt(N)).
 *   A+A = {a+b : a, b ∈ A}（a = b の和 2a も含む）。
 * N = 1..NMAX を計算し、b400702_01.txt に "N a(N)" 形式で保存する。
 *
 * 使う数学的事実（どれも証明つき、結果を変えない）:
 *  (1) 上限: 和は 2..N の範囲にあり、a <= b の組は s(s+1)/2 個なので
 *      f(N) <= min(N-1, s(s+1)/2)。（N = 1 では f(1) = 0）
 *  (2) f(N-1) <= f(N)（N >= 2）。
 *      N-1 で最適な A をとる。floor(sqrt(N)) = floor(sqrt(N-1)) なら A がそのまま使え、
 *      [1,N-1] の和は [1,N] に入る。N が平方数なら A に N を加える（A ⊆ [1,N-1] なので
 *      N ∉ A）。和の集合は増えるだけなので個数は減らない。
 *      よって f(N-1) が (1) の上限に達していれば f(N) = f(N-1)。そうでなければ
 *      「f(N-1) より多くの和をもつ A」だけを探せばよい。
 *  (3) min A = 1 としてよい。min A = m >= 2 なら A' = A - (m-1) とおくと、
 *      和 σ は σ - 2(m-1) に一対一に写り、σ <= N なら 2 <= σ - 2(m-1) <= N。
 *      よって A' ⊆ [1,N] は同じ大きさで、[1,N] に入る和の個数は減らない。
 *  (4) max A <= N-1 としてよい（N >= 2）。(3) で min A = 1 にした A が N を含むとき、
 *      N は 1+N > N なのでどの和にも寄与しない。[2, N-1] の N-2 個の値のうち
 *      A \ {1, N} が使うのは s-2 個 < N-2 個なので、未使用の値 v ∈ [2, N-1] があり、
 *      N を v に替えても和は増えるだけで、min A = 1 も保たれる。
 *  (5) floor(sqrt(N)) = floor(sqrt(N-1)) なら f(N) <= f(N-1) + 1。
 *      (4) の最適な A ⊆ [1, N-1] は N-1 の候補でもあるので、[1, N-1] に入る和は
 *      f(N-1) 個以下。[1, N] ではさらに和 N の 1 個が増えうるだけ。
 *      よって (2) と合わせて f(N) は f(N-1) か f(N-1)+1 で、f(N-1)+1 を達成する
 *      集合が見つかった時点で探索を終えてよい。
 *  (6) 枝刈り: 要素を小さい順に選ぶ。k 個（A_k）選び最後が x のとき、残り r = s-k 個の
 *      新しい要素 y_0 < ... < y_{r-1}（x < y_j <= N-1）が作る新しい和（まだ出ていない値）
 *      の個数を、次の 3 通りで上から抑え、現在の個数 + 最小の上限 <= best なら打ち切る。
 *      (a) 新しい和はすべて 1 + (x+1) = x+2 以上なので、[x+2, N] のまだ出ていない値の個数。
 *      (b) 新しい和は「既存の a と y の和」か「新要素どうしの和（自分自身を含む）」。
 *          前者: y ごとに g(y) = #{a ∈ A_k : a+y <= N, a+y はまだ出ていない} 個以下で、
 *          y_j は相異なるので合計は、x < y <= N-1 での g(y) の大きい方から r 個の和以下。
 *          後者: y_i + y_j >= (x+1+i) + (x+1+j)（y_j >= x+1+j）なので、
 *          2x+2+i+j <= N を満たす組 0 <= i <= j < r の個数以下。
 *      (c) y_j >= x+1+j なので、y_j が作る和は
 *          #{a ∈ A_k : a + x+1+j <= N} + #{i < j : 2x+2+i+j <= N} + [2(x+1+j) <= N] 個以下。
 *      (d) 次の要素の候補 y を小さい順に試すとき、次の要素を y にすると以後の新しい和は
 *          すべて 1+y 以上のまだ出ていない値なので、その個数 #([1+y, N] の未出の値) と、
 *          (c) で x を y-1 に替えた値は、どちらも y について増えない。
 *          よって現在の個数 + どちらか <= best となった y で、それ以降の y をすべて打ち切ってよい。
 *      上限は安いもの（(c)、(a)）から順に調べ、(b) は両方で打ち切れないときだけ計算する。
 *
 * 検証: N <= 36 を、全部分集合を調べる独立な総当たりと照合した（コメント末尾の値）。
 *       N <= 100 を、(4)〜(6)(b)(c) を使わない旧版の出力と照合した。
 *
 * コンパイル: g++ -O2 -std=c++17 -Wall -Wextra -Wpedantic -Werror 400702_01.cpp -o 400702_01
 * 実行:       ./400702_01 [N]   （N の既定値は 100、上限 MAXN）
 * 保存値は N = 1 から再計算して照合してから利用する（再開しても時間は節約できない）。
 * 指定した N より後ろの保存行は消さずに残す。排他ロックを取り、一時ファイルを
 * 同期してから置き換える。
 *
 * 総当たりの値（N = 1..36）:
 *   0,1,1,3,3,3,3,3,6,6,6,6,6,6,6,10,10,10,10,10,10,10,10,10,
 *   15,15,15,15,15,15,15,15,15,15,15,21
 */
#ifndef _DEFAULT_SOURCE
#define _DEFAULT_SOURCE
#endif
#include <cctype>
#include <cerrno>
#include <climits>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>

namespace {

constexpr int MAXN = 400;                 // s <= 20、和 <= 2*MAXN
constexpr int MAXS = 20;
static_assert(MAXS * MAXS <= MAXN && (MAXS + 1) * (MAXS + 1) > MAXN, "MAXS must be floor(sqrt(MAXN))");

const char result_path[] = "b400702_01.txt";
const char lock_path[] = "b400702_01.txt.lock";

int fval[MAXN + 1];                       // この実行で計算した f(N)

// ---------------- 探索 ----------------
int curN, curS, best;
int elems[MAXS];
int cnt[2 * MAXN + 2];                    // cnt[v] = v を作る (a<=b) の組の数（v <= curN のみ記録）

int isqrt_int(int n) {
    int r = 0;
    while ((r + 1) * (r + 1) <= n) r++;
    return r;
}

int upper_bound_of(int n) {               // 事実 (1)
    int s = isqrt_int(n);
    int pairs = s * (s + 1) / 2;
    return pairs < n - 1 ? pairs : n - 1;
}

int cap;                                  // best がこの値に達したら探索終了（事実 (1)(5)）
bool done_flag;

// 新要素どうしの和（自分自身を含む）の個数の上限: 2x+2+i+j <= N を満たす 0 <= i <= j < r の組
long new_pair_bound(int x, int r) {
    long c = 0;
    for (int j = 0; j < r; j++)
        for (int i = 0; i <= j; i++)
            if (2 * x + 2 + i + j <= curN) c++;
    return c;
}

// 事実 (6)(c): elems[0..k-1] を選び、残り r 個が y_j >= x+1+j のとき、新しい和の個数の上限
long pos_bound(int k, int x, int r) {
    long total = 0;
    for (int j = 0; j < r; j++) {
        int ymin = x + 1 + j;
        int c = 0;
        for (int i = 0; i < k && elems[i] + ymin <= curN; i++) c++;   // elems は昇順
        for (int i = 0; i < j; i++) if (2 * x + 2 + i + j <= curN) c++;
        if (2 * ymin <= curN) c++;
        total += c;
    }
    return total;
}

// k 個選び（最後の要素 x、elems[0..k-1] は昇順）、[1,N] に入る相異なる和が cur 個
void dfs(int k, int x, int cur) {
    if (done_flag) return;
    if (k == curS) {
        if (cur > best) {
            best = cur;
            if (best >= cap) done_flag = true;
        }
        return;
    }
    const int r = curS - k;
    const int ymax = curN - 1;            // 事実 (4)
    if (ymax - x < r) return;             // 要素が足りない

    // 安い上限から順に調べる。
    // (c) y_j >= x+1+j による位置の上限
    if (cur + pos_bound(k, x, r) <= best) return;

    // (a) [x+2, N] のまだ出ていない値の個数。free_from[v] = [v, N] のまだ出ていない値の個数
    int free_from[MAXN + 2];
    free_from[curN + 1] = 0;
    for (int v = curN; v >= x + 1; v--) free_from[v] = free_from[v + 1] + (cnt[v] == 0 ? 1 : 0);
    if (cur + free_from[x + 2 <= curN + 1 ? x + 2 : curN + 1] <= best) return;

    // (b) g(y) の大きい方から r 個の和 + 新要素どうしの和の上限
    int bucket[MAXS + 1] = {0};           // g(y) <= k <= MAXS
    for (int y = x + 1; y <= ymax; y++) {
        int g = 0;
        for (int i = 0; i < k; i++) {
            int v = elems[i] + y;
            if (v > curN) break;          // elems は昇順
            if (cnt[v] == 0) g++;
        }
        bucket[g]++;
    }
    long top = 0;
    int need = r;
    for (int g = k; g >= 0 && need > 0; g--) {
        int take = bucket[g] < need ? bucket[g] : need;
        top += static_cast<long>(take) * g;
        need -= take;
    }
    if (cur + top + new_pair_bound(x, r) <= best) return;

    for (int y = x + 1; y <= ymax - (r - 1); y++) {
        // 次の要素を y にすると、以後の新しい和はすべて 1 + y 以上の、いまはまだ出ていない値。
        // また残りの要素は y, y+1, ... 以上なので (c) の上限は pos_bound(k, y-1, r)。
        // どちらも y について増えないので、成り立たなくなったら以後の y もすべて不要（打ち切り）。
        if (cur + free_from[y + 1 <= curN + 1 ? y + 1 : curN + 1] <= best) break;
        if (cur + pos_bound(k, y - 1, r) <= best) break;
        int add = 0;
        for (int i = 0; i < k; i++) {
            int v = elems[i] + y;
            if (v <= curN && cnt[v]++ == 0) add++;
        }
        if (2 * y <= curN && cnt[2 * y]++ == 0) add++;
        elems[k] = y;
        dfs(k + 1, y, cur + add);
        for (int i = 0; i < k; i++) {
            int v = elems[i] + y;
            if (v <= curN) cnt[v]--;
        }
        if (2 * y <= curN) cnt[2 * y]--;
        if (done_flag) return;
    }
}

int next_value(int n) {
    if (n == 1) return 0;                 // A = {1}、和 2 > 1
    int ub = upper_bound_of(n);
    int lower = fval[n - 1];              // 事実 (2)
    if (lower >= ub) return ub;
    curN = n;
    curS = isqrt_int(n);
    cap = ub;
    if (isqrt_int(n - 1) == curS && lower + 1 < cap) cap = lower + 1;   // 事実 (5)
    best = lower;
    done_flag = false;
    std::memset(cnt, 0, sizeof cnt);
    elems[0] = 1;                         // 事実 (3)
    cnt[2]++;                             // 和 1+1 = 2（n >= 2）
    dfs(1, 1, 1);
    return best;
}

// ---------------- 保存・再開（安全な I/O） ----------------

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

// 結果ファイルを原子的に置き換えても有効な、別ファイルの排他ロック
int acquire_lock() {
    int fd = open(lock_path, O_RDWR | O_CREAT | O_NOFOLLOW | O_NONBLOCK, 0600);
    if (fd < 0) { std::perror("open result lock"); return -1; }
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode) || st.st_nlink != 1) {
        std::fprintf(stderr, "Result lock must be a regular file with one link.\n");
        close(fd); return -1;
    }
    if (flock(fd, LOCK_EX | LOCK_NB) != 0) {
        std::fprintf(stderr, "Cannot acquire result lock; another process may be using it.\n");
        close(fd); return -1;
    }
    return fd;
}

// 保存行の形式: 番号が 1 から連続、0 <= a(N) <= 事実 (1) の上限、前の値以上（事実 (2)）
bool parse_saved_line(char *line, int expected, int previous, int *value) {
    char *p = line, *end;
    while (std::isspace(static_cast<unsigned char>(*p))) p++;
    if (!std::isdigit(static_cast<unsigned char>(*p))) return false;
    errno = 0;
    long index = std::strtol(p, &end, 10);
    if (errno == ERANGE || index != expected || index > MAXN ||
        !std::isspace(static_cast<unsigned char>(*end))) return false;
    p = end;
    while (std::isspace(static_cast<unsigned char>(*p))) p++;
    if (!std::isdigit(static_cast<unsigned char>(*p))) return false;
    errno = 0;
    long parsed = std::strtol(p, &end, 10);
    if (errno == ERANGE || parsed < 0 || parsed > upper_bound_of(expected)) return false;
    while (std::isspace(static_cast<unsigned char>(*end))) end++;
    if (*end) return false;
    if (expected > 1 && parsed < previous) return false;
    *value = static_cast<int>(parsed);
    return true;
}

bool load_saved(int saved[], int *count) {
    *count = 0;
    int fd = open(result_path, O_RDONLY | O_NOFOLLOW | O_NONBLOCK);
    if (fd < 0) {
        if (errno == ENOENT) return true;
        std::perror("open saved result"); return false;
    }
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode) || st.st_nlink != 1) {
        std::fprintf(stderr, "Saved result must be a regular file with one link.\n");
        close(fd); return false;
    }
    FILE *in = fdopen(fd, "r");
    if (!in) { std::perror("read saved result"); close(fd); return false; }
    char line[128];
    int previous = 0;
    bool ok = true;
    while (std::fgets(line, sizeof line, in)) {
        size_t length = std::strlen(line);
        int value;
        if (*count >= MAXN || !length || line[length - 1] != '\n' ||
            !parse_saved_line(line, *count + 1, previous, &value)) {
            std::fprintf(stderr, "Invalid or incomplete saved row %d; file unchanged.\n", *count + 1);
            ok = false; break;
        }
        saved[++*count] = value;
        previous = value;
    }
    if (std::ferror(in)) { std::perror("read saved result"); ok = false; }
    if (std::fclose(in) != 0) { std::perror("close saved result"); ok = false; }
    return ok;
}

// 1..count を一時ファイルに書き、同期してから置き換える
bool save_prefix(int count) {
    struct stat st;
    if (lstat(result_path, &st) == 0) {
        if (!S_ISREG(st.st_mode) || st.st_nlink != 1) {
            std::fprintf(stderr, "Refusing to replace a linked or nonregular result file.\n");
            return false;
        }
    } else if (errno != ENOENT) {
        std::perror("inspect result path"); return false;
    }
    char temporary[] = ".b400702_01.txt.tmp.XXXXXX";
    int fd = mkstemp(temporary);
    if (fd < 0) { std::perror("create result temporary file"); return false; }
    FILE *out = fdopen(fd, "w");
    if (!out) {
        int error = errno;
        close(fd); unlink(temporary); errno = error;
        std::perror("open result temporary file"); return false;
    }
    int error = 0;
    for (int n = 1; n <= count; n++) {
        if (std::fprintf(out, "%d %d\n", n, fval[n]) < 0) {
            error = errno ? errno : EIO; break;
        }
    }
    if (!error && std::fflush(out) != 0) error = errno ? errno : EIO;
    if (!error && fsync(fd) != 0) error = errno ? errno : EIO;
    if (std::fclose(out) != 0 && !error) error = errno ? errno : EIO;
    if (error) {
        unlink(temporary); errno = error;
        std::perror("save result; previous file unchanged"); return false;
    }
    if (std::rename(temporary, result_path) != 0) {
        error = errno; unlink(temporary); errno = error;
        std::perror("replace result; previous file unchanged"); return false;
    }
    return true;
}

}  // namespace

int main(int argc, char **argv) {
    int N = 100;
    if (argc == 2 && (!std::strcmp(argv[1], "--help") || !std::strcmp(argv[1], "-h"))) {
        std::printf("Usage: %s [N] (N is 1..%d; default 100)\n", argv[0], MAXN);
        return 0;
    }
    if (argc > 2 || (argc == 2 && !parse_limit(argv[1], &N))) {
        std::fprintf(stderr, "Usage: %s [N]; N must be a decimal integer in 1..%d.\n", argv[0], MAXN);
        return 1;
    }
    int lock_fd = acquire_lock();
    if (lock_fd < 0) return 1;
    int status = 1, count = 0;
    static int saved[MAXN + 1];
    if (load_saved(saved, &count)) {
        int check_to = count < N ? count : N;
        if (check_to)
            std::fprintf(stderr, "Checking saved N=1..%d from the definition...\n", check_to);
        bool ok = true;
        for (int n = 1; n <= N && ok; n++) {
            int value = next_value(n);
            if (n <= count && value != saved[n]) {
                std::fprintf(stderr, "Saved value at N=%d is incorrect; file unchanged.\n", n);
                ok = false; break;
            }
            fval[n] = value;
            if (n <= count) {
                if (n == check_to)
                    std::fprintf(stderr, "Saved range N=1..%d verified.\n", check_to);
            } else {
                if (!save_prefix(n)) { ok = false; break; }
                if (std::printf("%d %d\n", n, value) < 0 || std::fflush(stdout) != 0) {
                    std::perror("write standard output; result file was saved");
                    ok = false; break;
                }
            }
        }
        if (ok) {
            if (N <= count)
                std::fprintf(stderr, "No new rows needed; all %d saved rows were retained.\n", count);
            status = 0;
        }
    }
    close(lock_fd);
    return status;
}
