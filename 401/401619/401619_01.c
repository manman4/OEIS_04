/*
 * Erdős Problem #771
 * a(n) = f(n) = 次を満たす最大の k:
 *   どの m >= 1 に対しても、|S| = k の S ⊆ {1,...,n} で、S のどの部分集合の和も m に
 *   ならないものが存在する。
 * n = 1..N について計算し b401619_01.txt に "n a(n)" 形式で保存する。
 * （A401619）
 *
 * 記号: T(n) = n(n+1)/2。g(n,m) = max{|S| : S ⊆ {1..n}, m は S の部分和でない}。
 *   f(n) = min_{m >= 1} g(n,m)。
 *
 * 使う数学的事実（どれも証明つき、結果を変えない）:
 *  (1) m > T(n) なら S = {1..n} の部分和は T(n) 以下なので g(n,m) = n。
 *      よって f(n) = min_{1 <= m <= T(n)} g(n,m)（n >= 1 では g(n,1) = n-1 < n）。
 *  (2) 正の数だけを足すので、m より大きい x は和が m の部分集合に入らない。
 *      よって x > m の要素はいつでも加えてよく、
 *      g(n,m) = max(0, n-m) + g(min(n,m), m)。探索は {1..min(n,m)} だけでよい。
 *  (3) f(n-1) <= f(n) <= f(n-1) + 1（n >= 2）。
 *      下側: m <= T(n-1) では S ⊆ {1..n-1} がそのまま使えるので g(n,m) >= g(n-1,m) >= f(n-1)。
 *            T(n-1) < m <= T(n) では S = {1..n-1} が m を避けるので g(n,m) >= n-1 >= f(n-1)
 *            （f(n-1) <= g(n-1,1) = n-2）。
 *      上側: m を避ける S ⊆ {1..n} から n を除いても m を避けるので g(n,m) <= g(n-1,m)+1、
 *            m = 1 では g(n,1) = n-1 = g(n-1,1)+1。両辺の最小をとる。
 *     よって f(n) = f(n-1)+1 となるのは、1 <= m <= T(n) のすべての m で
 *     「大きさ t = f(n-1)+1 で m を避ける S」が見つかるときに限る。
 *  (4) 部分和の集合は要素を加えると増える一方なので、途中で m が部分和に入ったら、
 *      その枝からは m を避ける集合は作れない（枝刈り）。
 *
 * 探索: 各 m について、x = min(n,m), ..., 1 を「入れる/入れない」で深さ優先に調べる。
 *   部分和は 0..m だけをビット集合で持つ（m より大きい和は判定に不要）。
 *
 * 検証: n <= 20 を、全部分集合を調べる独立な総当たりと照合する（コメント末尾の値）。
 *
 * コンパイル: cc -O2 -std=c17 -Wall -Wextra -Wpedantic -Werror 401619_01.c -o 401619_01
 * 実行:       ./401619_01 [N]   （N の既定値は 30、上限 MAXN）
 * 保存値は 1 から再計算して照合してから利用する（再開しても時間は節約できない）。
 * N より後ろの保存行は消さずに残す。排他ロックを取り、一時ファイルを同期してから置き換える。
 *
 * 総当たりの値（n = 1..20）: 0,1,1,2,2,3,3,4,4,5,5,6,6,6,7,7,7,7,8,8
 */
#define _POSIX_C_SOURCE 200809L
#define _DARWIN_C_SOURCE
#define _DEFAULT_SOURCE
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>

#define MAXN 200
/* m <= T(MAXN) = 20100。部分和 0..m のビット集合に必要な語数 */
#define MAXM (MAXN * (MAXN + 1) / 2)
#define WORDS (MAXM / 64 + 1)
_Static_assert(MAXM < INT_MAX / 2, "T(MAXN) must fit in int.");

static const char result_path[] = "b401619_01.txt";
static const char lock_path[] = "b401619_01.txt.lock";

static int fval[MAXN + 1];           /* この実行で計算した f(n) */

/* 部分和集合（0..m のビット）: 深さごとの作業領域 */
static uint64_t stackbits[MAXN + 2][WORDS];
static int cur_m, cur_words;

static inline int has_bit(const uint64_t *b, int i) { return (int)((b[i >> 6] >> (i & 63)) & 1u); }

/* dst = src | (src << x)、ただし 0..cur_m のビットだけ残す */
static void shift_or(uint64_t *dst, const uint64_t *src, int x) {
    int q = x >> 6, r = x & 63;
    for (int i = 0; i < cur_words; i++) {
        uint64_t v = 0;
        if (i - q >= 0) {
            v = src[i - q] << r;
            if (r && i - q - 1 >= 0) v |= src[i - q - 1] >> (64 - r);
        }
        dst[i] = src[i] | v;
    }
    int top = cur_m & 63;                 /* 最上位語の cur_m より上のビットを消す */
    if (top != 63) dst[cur_words - 1] &= ((uint64_t)1 << (top + 1)) - 1;
}

/* {1..x} から need 個を選んで、部分和に cur_m が現れないようにできるか。
   depth の部分和集合は stackbits[depth]（cur_m を含まない）。 */
static int dfs(int x, int need, int depth) {
    if (need == 0) return 1;
    if (x < need) return 0;               /* 残りは 1..x の x 個しかない */
    uint64_t *cur = stackbits[depth], *nxt = stackbits[depth + 1];
    shift_or(nxt, cur, x);
    if (!has_bit(nxt, cur_m) && dfs(x - 1, need - 1, depth + 1)) return 1;   /* x を入れる */
    return dfs(x - 1, need, depth);                                          /* x を入れない */
}

/* 大きさ t で m を避ける S ⊆ {1..n} があるか（事実 (2) で x > m の要素は無条件に入れる） */
static int avoidable(int n, int m, int t) {
    int free_count = n > m ? n - m : 0;
    int need = t - free_count;
    if (need <= 0) return 1;
    int lim = n < m ? n : m;
    cur_m = m;
    cur_words = m / 64 + 1;
    memset(stackbits[0], 0, sizeof(uint64_t) * (size_t)cur_words);
    stackbits[0][0] = 1;                  /* 空集合の和 0 */
    return dfs(lim, need, 0);
}

static int next_value(int n) {
    if (n == 1) return 0;                 /* m = 1 を避けるには S = ∅ しかない */
    int t = fval[n - 1] + 1;              /* 事実 (3): f(n) は f(n-1) か f(n-1)+1 */
    int T = n * (n + 1) / 2;
    for (int m = 1; m <= T; m++)
        if (!avoidable(n, m, t)) return fval[n - 1];
    return t;
}

/* ---------------- ここから保存・再開（安全な I/O） ---------------- */

static int parse_limit(const char *text, int *value) {
    if (!*text) return 0;
    for (const char *p = text; *p; p++)
        if (*p < '0' || *p > '9') return 0;
    errno = 0;
    char *end;
    long parsed = strtol(text, &end, 10);
    if (errno == ERANGE || *end || parsed < 1 || parsed > MAXN) return 0;
    *value = (int)parsed;
    return 1;
}

/* A stable sidecar lock survives atomic replacements of the result inode. */
static int acquire_lock(void) {
    int fd = open(lock_path, O_RDWR | O_CREAT | O_NOFOLLOW | O_NONBLOCK, 0600);
    if (fd < 0) { perror("open result lock"); return -1; }
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode) || st.st_nlink != 1) {
        fprintf(stderr, "Result lock must be a regular file with one link.\n");
        close(fd); return -1;
    }
    if (flock(fd, LOCK_EX | LOCK_NB) != 0) {
        fprintf(stderr, "Cannot acquire result lock; another process may be using it.\n");
        close(fd); return -1;
    }
    return fd;
}

/* 保存行の形式: 番号が連続、0 <= a(n) <= n-1、隣の差が 0 か 1（事実 (3)） */
static int parse_saved_line(char *line, int expected, int previous, int *value) {
    char *p = line, *end;
    while (isspace((unsigned char)*p)) p++;
    if (!isdigit((unsigned char)*p)) return 0;
    errno = 0;
    long index = strtol(p, &end, 10);
    if (errno == ERANGE || index != expected || index > MAXN ||
        !isspace((unsigned char)*end)) return 0;
    p = end;
    while (isspace((unsigned char)*p)) p++;
    if (!isdigit((unsigned char)*p)) return 0;
    errno = 0;
    long parsed = strtol(p, &end, 10);
    if (errno == ERANGE || parsed < 0 || parsed > expected - 1) return 0;
    while (isspace((unsigned char)*end)) end++;
    if (*end) return 0;
    if (expected > 1 && (parsed < previous || parsed > previous + 1)) return 0;
    *value = (int)parsed;
    return 1;
}

static int load_saved(int saved[MAXN + 1], int *count) {
    *count = 0;
    int fd = open(result_path, O_RDONLY | O_NOFOLLOW | O_NONBLOCK);
    if (fd < 0) {
        if (errno == ENOENT) return 1;
        perror("open saved result"); return 0;
    }
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode) || st.st_nlink != 1) {
        fprintf(stderr, "Saved result must be a regular file with one link.\n");
        close(fd); return 0;
    }
    FILE *in = fdopen(fd, "r");
    if (!in) { perror("read saved result"); close(fd); return 0; }
    char line[128];
    int previous = 0, ok = 1;
    while (fgets(line, sizeof line, in)) {
        size_t length = strlen(line);
        int value;
        if (*count >= MAXN || !length || line[length - 1] != '\n' ||
            !parse_saved_line(line, *count + 1, previous, &value)) {
            fprintf(stderr, "Invalid or incomplete saved row %d; file unchanged.\n", *count + 1);
            ok = 0; break;
        }
        saved[++*count] = value;
        previous = value;
    }
    if (ferror(in)) { perror("read saved result"); ok = 0; }
    if (fclose(in) != 0) { perror("close saved result"); ok = 0; }
    return ok;
}

/* 1..count を一時ファイルに書き、同期してから置き換える。 */
static int save_prefix(int count) {
    struct stat st;
    if (lstat(result_path, &st) == 0) {
        if (!S_ISREG(st.st_mode) || st.st_nlink != 1) {
            fprintf(stderr, "Refusing to replace a linked or nonregular result file.\n");
            return 0;
        }
    } else if (errno != ENOENT) {
        perror("inspect result path"); return 0;
    }
    char temporary[] = ".b401619_01.txt.tmp.XXXXXX";
    int fd = mkstemp(temporary);
    if (fd < 0) { perror("create result temporary file"); return 0; }
    FILE *out = fdopen(fd, "w");
    if (!out) {
        int error = errno;
        close(fd); unlink(temporary); errno = error;
        perror("open result temporary file"); return 0;
    }
    int error = 0;
    for (int n = 1; n <= count; n++) {
        if (fprintf(out, "%d %d\n", n, fval[n]) < 0) {
            error = errno ? errno : EIO; break;
        }
    }
    if (!error && fflush(out) != 0) error = errno ? errno : EIO;
    if (!error && fsync(fd) != 0) error = errno ? errno : EIO;
    if (fclose(out) != 0 && !error) error = errno ? errno : EIO;
    if (error) {
        unlink(temporary); errno = error;
        perror("save result; previous file unchanged"); return 0;
    }
    if (rename(temporary, result_path) != 0) {
        error = errno; unlink(temporary); errno = error;
        perror("replace result; previous file unchanged"); return 0;
    }
    /* The new file is already in place. Sync its directory entry before
       reporting success; on failure keep the valid result for a later run. */
    int directory_fd = open(".", O_RDONLY | O_DIRECTORY);
    if (directory_fd < 0) {
        perror("result replaced; cannot open output directory for synchronization");
        return 0;
    }
    int sync_result;
    do {
        sync_result = fsync(directory_fd);
    } while (sync_result != 0 && errno == EINTR);
    error = sync_result != 0 ? (errno ? errno : EIO) : 0;
    if (close(directory_fd) != 0 && !error) error = errno ? errno : EIO;
    if (error) {
        errno = error;
        perror("result replaced; directory synchronization not confirmed");
        return 0;
    }
    return 1;
}

int main(int argc, char **argv) {
    int N = 30;
    if (argc == 2 && (!strcmp(argv[1], "--help") || !strcmp(argv[1], "-h"))) {
        printf("Usage: %s [N] (N is 1..%d; default 30)\n", argv[0], MAXN);
        return 0;
    }
    if (argc > 2 || (argc == 2 && !parse_limit(argv[1], &N))) {
        fprintf(stderr, "Usage: %s [N]; N must be a decimal integer in 1..%d.\n", argv[0], MAXN);
        return 1;
    }
    int lock_fd = acquire_lock();
    if (lock_fd < 0) return 1;
    int status = 1, count = 0, saved[MAXN + 1] = {0};
    if (!load_saved(saved, &count)) goto done;
    memset(fval, 0, sizeof fval);
    int check_to = count < N ? count : N;
    if (check_to)
        fprintf(stderr, "Checking saved n=1..%d from the definition...\n", check_to);
    for (int n = 1; n <= N; n++) {
        int value = next_value(n);
        if (n <= count && value != saved[n]) {
            fprintf(stderr, "Saved value at n=%d is incorrect; file unchanged.\n", n);
            goto done;
        }
        fval[n] = value;
        if (n <= count) {
            if (n == check_to)
                fprintf(stderr, "Saved range n=1..%d verified.\n", check_to);
        } else {
            if (!save_prefix(n)) goto done;
            if (printf("%d %d\n", n, value) < 0 || fflush(stdout) != 0) {
                perror("write standard output; result file was saved"); goto done;
            }
        }
    }
    if (N <= count)
        fprintf(stderr, "No new rows needed; all %d saved rows were retained.\n", count);
    status = 0;
done:
    close(lock_fd);
    return status;
}
