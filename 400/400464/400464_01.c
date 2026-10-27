/*
 * Erdős Problem #425
 * a(n) = F(n) = A ⊆ {1,...,n} で、積 ab（a < b, a, b ∈ A）がすべて異なるもののうち
 *        最大の |A|（乗法的 Sidon 集合の最大の大きさ）
 * n = 1..N について計算し b400464_01.txt に "n a(n)" 形式で保存
 *
 * 方針:
 *   選んだ集合 A の積 ab (a < b) を used[] に記録する。x を加えられるのは
 *   すべての a ∈ A について a*x が未使用のとき（a*x どうしは a が異なれば異なる）。
 *   F(n) は F(n-1) か F(n-1)+1（n を除いても条件は保たれるので F(n) <= F(n-1)+1）。
 *   よって n を必ず含む大きさ F(n-1)+1 の集合が {1,...,n} にあるかを
 *   深さ優先探索で調べる。
 * 高速化（どれも結果を変えない）:
 *   - n が素数なら F(n) = F(n-1) + 1（n を含む積はすべて n で割り切れ、
 *     n 未満の数どうしの積は n で割り切れないので、新しい積は既存の積と重ならない）。
 *   - 探索中、{1,...,x} から追加で選べる個数は高々 F(x)（計算済み）なので、
 *     選んだ個数 + F(x) < 目標 なら枝刈りする。
 *   - 「自由な素数」: 探索で素数 x に来たとき、それまでに選んだ要素（すべて x より大きい）に
 *     x の倍数がなければ、x を含む積は他のどの積とも一致しない。よって x は必ず選び
 *     （選ばない枝は調べない）、その積は記録せずに個数だけ数える。
 *
 * コンパイル: cc -O2 -std=c17 -Wall -Wextra -Wpedantic -Werror 400464_01.c -o 400464_01
 * 実行:       ./400464_01 [N]   （N の既定値は 60、上限 MAXN）
 * 1 項ごとに b400464_01.txt へ書き出し（標準出力にも表示）。
 * 保存値は1から再計算して照合してから利用する。新しい確定項だけを表示する。
 * 小さいNではNまでだけ検証し、Nより後の保存行もそのまま保持する。
 * 排他ロックを取得し、固有の一時ファイルを同期してから結果を置き換える。
 * 詳細な範囲と検証方法は 400464_c_safety.md を参照。
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

#define MAXN 1000
_Static_assert(INT_MAX >= 2147483647L, "The search requires at least 32-bit int.");
static const char result_path[] = "b400464_01.txt";
static size_t used_bytes;

static unsigned char *used;          /* used[m] = 1 なら積 m が既出 */
static int A[MAXN + 1], k;           /* 選んだ集合 */
static int target, found;
static int fval[MAXN + 1];           /* 計算済みの F(m) */
static int spf[MAXN + 1];            /* 最小素因数 */
static int cntp[MAXN + 1];           /* cntp[p] = A の要素のうち p の倍数の個数 */

static void count_factors(int x, int d) {     /* x の相異なる素因数 p について cntp[p] += d */
    while (x > 1) {
        int p = spf[x];
        cntp[p] += d;
        while (x % p == 0) x /= p;
    }
}

/* x, x-1, ..., 1 から選び、選んだ個数（A の要素 k 個 + 自由な素数 fr 個）が target に達するか */
static void dfs(int x, int fr) {
    if (found) return;
    if (k + fr == target) { found = 1; return; }
    if (x < 1) return;
    if (k + fr + fval[x] < target) return;   /* {1..x} からは高々 F(x) 個しか選べない */
    if (x >= 2 && spf[x] == x && cntp[x] == 0) {
        /* 「自由な素数」: x は素数で、これまでに選んだ要素（すべて x より大きい）に x の倍数がない。
           これから選ぶ要素は x 未満なので x の倍数ではない。よって最終的な集合で x の倍数は x だけで、
           x を含む積 a*x はすべて x で割り切れ、x を含まない積はどれも x で割り切れない。
           a*x どうしも a が異なれば異なる。したがって
           (1) x を加えても条件は崩れない → x を選ばない枝は調べなくてよい
               （x を選ばない解があれば、x を加えたものも解で、要素数は target 以上）。
           (2) x を含む積は以後どの積とも一致しない → x の積を記録せず、個数だけ数えればよい。 */
        dfs(x - 1, fr + 1);
        return;
    }
    int ok = 1;
    for (int i = 0; i < k; i++) if (used[A[i] * x]) { ok = 0; break; }
    if (ok) {
        for (int i = 0; i < k; i++) used[A[i] * x] = 1;
        A[k++] = x;
        count_factors(x, +1);
        dfs(x - 1, fr);
        count_factors(x, -1);
        k--;
        for (int i = 0; i < k; i++) used[A[i] * x] = 0;
        if (found) return;
    }
    dfs(x - 1, fr);
}

static int is_prime(int n) {
    if (n < 2) return 0;
    for (int q = 2; q * q <= n; q++) if (n % q == 0) return 0;
    return 1;
}

static int initialize_search(int limit) {
    if (limit < 1 || limit > MAXN) return 0;
    size_t side = (size_t)limit + 1;
    if (side > SIZE_MAX / side) {
        fprintf(stderr, "Product table size exceeds size_t.\n");
        return 0;
    }
    used_bytes = side * side;
    used = calloc(used_bytes, sizeof *used);
    if (!used) {
        fprintf(stderr, "Out of memory; previous results are unchanged.\n");
        return 0;
    }
    memset(spf, 0, sizeof spf);
    for (int i = 2; i <= limit; i++)
        if (!spf[i])
            for (int j = i; j <= limit; j += i)
                if (!spf[j]) spf[j] = i;
    return 1;
}

/* fval contains only optima proved earlier in this run, never saved inputs. */
static int next_value(int n) {
    int previous = fval[n - 1];
    if (n == 1 || is_prime(n)) return previous + 1;
    memset(used, 0, used_bytes);
    memset(cntp, 0, sizeof cntp);
    k = 1;
    A[0] = n;
    count_factors(n, +1);
    target = previous + 1;
    found = 0;
    dfs(n - 1, 0);
    return previous + found;
}

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
    const char lock_path[] = "b400464_01.txt.lock";
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
    if (errno == ERANGE || parsed < 1 || parsed > expected) return 0;
    while (isspace((unsigned char)*end)) end++;
    if (*end || parsed < previous || parsed > previous + 1) return 0;
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
    char temporary[] = ".b400464_01.txt.tmp.XXXXXX";
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
    return 1;
}

int main(int argc, char **argv) {
    int N = 60;
    if (argc == 2 && (!strcmp(argv[1], "--help") || !strcmp(argv[1], "-h"))) {
        printf("Usage: %s [N] (N is 1..%d; default 60)\n", argv[0], MAXN);
        return 0;
    }
    if (argc > 2 || (argc == 2 && !parse_limit(argv[1], &N))) {
        fprintf(stderr, "Usage: %s [N]; N must be a decimal integer in 1..%d.\n", argv[0], MAXN);
        return 1;
    }
    int lock_fd = acquire_lock();
    if (lock_fd < 0) return 1;
    int status = 1, count = 0, saved[MAXN + 1] = {0};
    if (!load_saved(saved, &count) || !initialize_search(N)) goto done;
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
    free(used);
    close(lock_fd);
    return status;
}
