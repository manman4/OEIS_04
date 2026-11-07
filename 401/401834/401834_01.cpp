/*
 * Erdős Problem #796  (A401834)
 * a(n) = g_3(n) = A ⊆ {1,...,n} で、どの m についても m = a1*a2（a1 < a2, a1, a2 ∈ A）の
 *        表し方が 3 通り未満（2 通り以下）であるもののうち、最大の |A|。
 * n = 1..N を計算し、b401834_01.txt に "n a(n)" 形式で保存する。
 *
 * 使う数学的事実（どれも証明つき、結果を変えない）:
 *  (1) 条件を満たす集合の部分集合も条件を満たす（表し方の数は減るだけ）。
 *  (2) a(n-1) <= a(n) <= a(n-1) + 1（n >= 2）。
 *      下側: {1..n-1} の集合は {1..n} の集合でもある。
 *      上側: {1..n} の集合から n を除くと {1..n-1} の集合になる（(1)）。
 *      さらに a(n) = a(n-1) + 1 なら、大きさ a(n-1)+1 の集合は必ず n を含む
 *      （含まなければ {1..n-1} の集合で a(n-1) を超える）。
 *      よって「n を含む大きさ a(n-1)+1 の集合」があるかだけを調べればよい。
 *  (3) n が素数なら a(n) = a(n-1) + 1。
 *      {1..n-1} の最適な集合に n を加える。n を含む積 n*a は n で割り切れ、
 *      n 未満の数どうしの積は n で割り切れない。n*a どうしも a が違えば値が違う。
 *      よって新しい積はどれも表し方が 1 通りで、既存の積の表し方も増えない。
 *  (4) 枝刈り: x, x-1, ..., 1 から選ぶとき、{1..x} から選べるのは (1) より高々 a(x) 個
 *      （この実行で計算した値）。選んだ個数 + a(x) < 目標 なら打ち切る。
 *  (5) 「自由な素数」: 探索で素数 x に来たとき、それまでに選んだ要素（すべて x より大きい）
 *      に x の倍数がなければ、これから選ぶ要素（x 未満）も x の倍数ではないので、
 *      最終的な集合で x の倍数は x だけ。(3) と同じ理由で、x を含む積はどれも
 *      表し方が 1 通りで、x を含まない積の表し方には影響しない。
 *      よって x は必ず選んでよく（選ばない解があれば x を加えても解）、
 *      その積は記録せずに個数だけ数えればよい。
 *
 * 探索: cnt[m] = 選んだ集合で m = a1*a2（a1 < a2）となる組の数。
 *   x を加えられるのは、選んだ各 a について cnt[a*x] <= 1 のとき
 *   （a*x は a ごとに値が異なるので、x を加えると各 cnt[a*x] は 1 だけ増える）。
 *
 * 検証: n <= 20 を、全部分集合を調べる独立な総当たりと照合した（コメント末尾の値）。
 *       n <= 40 を、(3)(5) を使わない別の探索プログラムと照合した。
 *
 * コンパイル: g++ -O2 -std=c++17 -Wall -Wextra -Wpedantic -Werror 401834_01.cpp -o 401834_01
 * 実行:       ./401834_01 [N]   （N の既定値は 100、上限 MAXN）
 * 保存値は n = 1 から再計算して照合してから利用する（再開しても時間は節約できない）。
 * 指定した N より後ろの保存行は消さずに残す。排他ロックを取り、一時ファイルを
 * 同期してから置き換える。
 *
 * 総当たりの値（n = 1..20）: 1,2,3,4,5,6,7,8,9,10,11,11,12,13,14,15,16,16,17,17
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
#include <vector>
#include <fcntl.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>

namespace {

constexpr int MAXN = 1000;                // 積は MAXN^2 = 10^6 以下
static_assert(static_cast<long>(MAXN) * MAXN < INT_MAX, "products must fit in int");

const char result_path[] = "b401834_01.txt";
const char lock_path[] = "b401834_01.txt.lock";

int fval[MAXN + 1];                       // この実行で計算した a(n)

// ---------------- 探索 ----------------
std::vector<unsigned char> cnt;           // cnt[m] <= 2
int spf[MAXN + 1];                        // 最小素因数
int cntp[MAXN + 1];                       // cntp[p] = 選んだ要素のうち p の倍数の個数
int chosen[MAXN];
int k_chosen, target;
bool found;

bool is_prime(int x) { return x >= 2 && spf[x] == x; }

void count_factors(int x, int d) {        // x の相異なる素因数 p について cntp[p] += d
    while (x > 1) {
        int p = spf[x];
        cntp[p] += d;
        while (x % p == 0) x /= p;
    }
}

// x, x-1, ..., 1 から選ぶ。選んだ個数は k_chosen（記録した要素）+ fr（自由な素数）
void dfs(int x, int fr) {
    if (found) return;
    if (k_chosen + fr >= target) { found = true; return; }
    if (x < 1) return;
    if (k_chosen + fr + fval[x] < target) return;          // 事実 (4)
    if (is_prime(x) && cntp[x] == 0) {                       // 事実 (5)
        dfs(x - 1, fr + 1);
        return;
    }
    bool ok = true;
    for (int i = 0; i < k_chosen; i++)
        if (cnt[static_cast<size_t>(chosen[i]) * x] >= 2) { ok = false; break; }
    if (ok) {
        for (int i = 0; i < k_chosen; i++) cnt[static_cast<size_t>(chosen[i]) * x]++;
        chosen[k_chosen++] = x;
        count_factors(x, +1);
        dfs(x - 1, fr);
        count_factors(x, -1);
        k_chosen--;
        for (int i = 0; i < k_chosen; i++) cnt[static_cast<size_t>(chosen[i]) * x]--;
        if (found) return;
    }
    dfs(x - 1, fr);
}

int next_value(int n) {
    if (n == 1) return 1;                 // A = {1}（積の組がない）
    if (is_prime(n)) return fval[n - 1] + 1;                 // 事実 (3)
    // 事実 (2): n を含む大きさ a(n-1)+1 の集合があるか
    std::fill(cnt.begin(), cnt.end(), 0);
    std::memset(cntp, 0, sizeof cntp);
    k_chosen = 0;
    chosen[k_chosen++] = n;
    count_factors(n, +1);
    target = fval[n - 1] + 1;
    found = false;
    dfs(n - 1, 0);
    return found ? target : fval[n - 1];
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

// 保存行の形式: 番号が 1 から連続、1 <= a(n) <= n、a(1) = 1、隣の差が 0 か 1（事実 (2)）
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
    if (errno == ERANGE || parsed < 1 || parsed > expected) return false;
    while (std::isspace(static_cast<unsigned char>(*end))) end++;
    if (*end) return false;
    if (expected == 1 && parsed != 1) return false;
    if (expected > 1 && (parsed < previous || parsed > previous + 1)) return false;
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
    char temporary[] = ".b401834_01.txt.tmp.XXXXXX";
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

    for (int i = 2; i <= N; i++)
        if (spf[i] == 0)
            for (int j = i; j <= N; j += i)
                if (spf[j] == 0) spf[j] = i;
    cnt.assign(static_cast<size_t>(N) * N + 1, 0);

    int status = 1, count = 0;
    static int saved[MAXN + 1];
    if (load_saved(saved, &count)) {
        int check_to = count < N ? count : N;
        if (check_to)
            std::fprintf(stderr, "Checking saved n=1..%d from the definition...\n", check_to);
        bool ok = true;
        for (int n = 1; n <= N && ok; n++) {
            int value = next_value(n);
            if (n <= count && value != saved[n]) {
                std::fprintf(stderr, "Saved value at n=%d is incorrect; file unchanged.\n", n);
                ok = false; break;
            }
            fval[n] = value;
            if (n <= count) {
                if (n == check_to)
                    std::fprintf(stderr, "Saved range n=1..%d verified.\n", check_to);
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
