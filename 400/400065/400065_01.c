/*
 * Erdős Problem #360  (A400065)
 * a(n) = f(n) = {1, ..., n-1} を f(n) 個の組に分けて、どの組からも相異なる要素の和で
 *        n を作れないようにするときの、組の数の最小値。
 * n = 1..N を計算し、b400065_01.txt に "n a(n)" 形式で 1 項ずつ保存する（標準出力にも表示）。
 * 既存の b400065_01.txt があれば、形式を検査し、n = 1 から計算し直して照合してから続きを計算する
 * （再開しても時間は節約できない）。指定した N より後ろの保存行は消さずに残す。
 * 排他ロックを取り、一時ファイルを同期してから置き換える。
 *
 * 使う事実（どれも証明つき、結果を変えない）:
 *  (1) f(1) = 0（要素がない）、f(2) = 1（{1} の部分和 0, 1 は 2 にならない）。
 *      n >= 3 では 1 と n-1 が同じ組だと 1 + (n-1) = n なので f(n) >= 2。
 *      f(42) = 4、f(43) = 3 なので f は単調非減少ではない。各 n で組の数 2, 3, ... を順に試す
 *      （最初に分けられた組の数が f(n)）。
 *  (2) 組の部分和: 組 c の部分和の集合を S_c（0 を含み、n 以下だけ記録）とする。
 *      y を組 c に加えると部分和は S_c ∪ (S_c + y) になり、n が作れるようになるのは
 *      n - y ∈ S_c のときだけ（もともと n ∉ S_c に保つ）。
 *      実装では反転した集合 R_c[t] = S_c[n-t]（0 <= t <= n）を持つ。y を加えられるのは
 *      R_c[y] = 0 のときで、加えた後は R_c |= (R_c を y だけ右にずらしたもの)。
 *  (3) 色の付け替え: 組の名前を入れ替えた分け方は同じなので、まだ空の組は 1 つだけ試す。
 *  (4) 部分和は増える一方なので、ある時点で組 c に入れられない値は、その枝ではずっと入れられない。
 *      よって、すべての組が使われていて、まだ組の決まっていない値 y がどの組にも入れられなければ
 *      打ち切る。また、y が入れられる組がちょうど 1 つなら、その組に入れるしかない。
 *      実装では (5) の順序でこのような y が優先して選ばれ、試す組が 1 通りだけになる
 *      （実質的に分岐せずに決まる）。
 *  (5) 変数の順序: 入れられる組の数が最も少ない値から決める（同数なら小さい値から）。
 *      小さい値を先に決めると部分和がすぐ広がり、行き詰まりが早く見つかる（実測で数百倍速い）。
 *      どの順で決めても調べ尽くすので、結果は変わらない。
 *  (6) 大きい値は分岐しない: y >= ceil(n/2) の 2 つの値の和は n を超えるので、組の中で n を作る
 *      部分集合に大きい値は高々 1 つしか入らない。よって大きい値 y を組 c に入れてよいのは
 *      「c の小さい値（< ceil(n/2)）の部分和に n - y がない」ときで、これは他の大きい値に依らない。
 *      そこで小さい値だけを探索で組に分け（部分和 S_c は小さい値だけから作る）、各大きい値 y に
 *      n - y ∉ S_c となる組 c があればよい。S_c は増える一方なので、すべての組が使われていて
 *      どの組にも入れられない大きい値があれば、その時点で打ち切る。
 *      最後に大きい値を入れられる最初の組に入れ、各組の部分和を直接計算して n が作れないことを
 *      検算する（失敗したら内部エラーで停止）。
 *
 * 検証: n <= 41 を、大きい値から順に決めるだけの素朴な探索（(4)(5) なし）と照合した。
 *       n = 42..79（43, 47 を除く）の「3 組では無理」と n = 42..81 の「4 組で可能」を、小さい値から順に
 *       決めるだけの素朴な探索（(4)(5)(6) なし）で独立に確かめた。f(43) = f(47) = 3 の分け方は
 *       Python で直接検算した（f は単調でない）。
 *       分けられたと判定したときは、毎回その分け方を部分和の直接計算で検算している（事実 (6)）。
 *
 * コンパイル: gcc -O2 -std=c11 -Wall -Wextra -Wpedantic -Werror 400065_01.c -o 400065_01
 * 実行:       ./400065_01 [N]   （N の既定値 60、1 <= N <= MAXN）
 */
#define _DEFAULT_SOURCE
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 1023                 /* ビット列は 0..MAXN を表す */
#define W ((MAXN + 1 + 63) / 64)
#define MAXK 16

typedef struct { uint64_t w[W]; } bits;

static int n, K, nw;              /* nw = 使う語数（0..n を表すのに必要な分） */

static inline int getb(const bits *b, int i) { return (int)((b->w[i >> 6] >> (i & 63)) & 1u); }
static inline void setb(bits *b, int i) { b->w[i >> 6] |= (uint64_t)1 << (i & 63); }
static inline void clrb(bits *b, int i) { b->w[i >> 6] &= ~((uint64_t)1 << (i & 63)); }

/* dst |= (src を s ビット右にずらしたもの)。0..n の範囲だけ意味をもつ（それより上は 0 に保つ） */
static void or_shift_right(bits *dst, const bits *src, int s) {
    int ws = s >> 6, bs = s & 63;
    for (int i = 0; i < nw; i++) {
        uint64_t v = 0;
        int j = i + ws;
        if (j < nw) {
            v = src->w[j] >> bs;
            if (bs && j + 1 < nw) v |= src->w[j + 1] << (64 - bs);
        }
        dst->w[i] |= v;
    }
}

static bits LARGE;                 /* 大きい値 ceil(n/2)..n-1（事実 (6)） */
static int col[MAXN + 1];          /* 小さい値に割り当てた組（検算用） */

/* DFS の状態: R[c]（反転した部分和、小さい値だけから作る）、U（組の決まっていない小さい値）、
   used（使った組の数） */
static int dfs(bits *R, bits *U, int used) {
    int best_y = -1, best_cnt = MAXK + 1;
    int fresh = used < K;                       /* 空の組が残っていれば必ず入れられる */
    if (!fresh) {
        /* 事実 (6): 大きい値 y で、どの組にも入れられないもの（すべての c で R_c[y] = 1）があれば打ち切る */
        for (int i = 0; i < nw; i++) {
            uint64_t m = LARGE.w[i];
            for (int c = 0; c < K && m; c++) m &= R[c].w[i];
            if (m) return 0;
        }
    }
    for (int i = nw - 1; i >= 0; i--) {
        uint64_t u = U->w[i];
        while (u) {
            int b = 63 - __builtin_clzll(u);
            u &= ~((uint64_t)1 << b);
            int y = i * 64 + b;
            int cnt = fresh;
            for (int c = 0; c < used; c++) if (!getb(&R[c], y)) cnt++;
            if (cnt == 0) return 0;               /* 事実 (4): どの組にも入れられない */
            if (cnt <= best_cnt) { best_cnt = cnt; best_y = y; }  /* 同数なら小さい y（後に見た方） */
        }
    }
    if (best_y < 0) return 1;                   /* 小さい値がすべて決まった */
    int y = best_y;
    clrb(U, y);
    bits saved;
    for (int c = 0; c < used + fresh; c++) {    /* 事実 (3): 空の組は番号 used の 1 つだけ */
        if (c < used && getb(&R[c], y)) continue;
        saved = R[c];
        or_shift_right(&R[c], &saved, y);       /* 事実 (2) */
        col[y] = c;
        int ok = dfs(R, U, c == used ? used + 1 : used);
        if (ok) { setb(U, y); return 1; }       /* R は検算で使うので戻さない */
        R[c] = saved;
    }
    setb(U, y);
    return 0;
}

/* 見つかった分け方（大きい値は入れられる最初の組へ）を、部分和を直接計算して検算する */
static void verify_partition(const bits *R) {
    static unsigned char reach[MAXN + 1];
    int half = (n + 1) / 2;
    for (int y = half; y <= n - 1; y++) {
        int c = 0;
        while (c < K && getb(&R[c], y)) c++;
        if (c == K) { fprintf(stderr, "\nInternal error: no class for %d (n=%d).\n", y, n); exit(3); }
        col[y] = c;
    }
    for (int c = 0; c < K; c++) {
        memset(reach, 0, (size_t)n + 1);
        reach[0] = 1;
        for (int x = 1; x <= n - 1; x++) {
            if (col[x] != c) continue;
            for (int t = n; t >= x; t--) if (reach[t - x]) reach[t] = 1;
        }
        if (reach[n]) { fprintf(stderr, "\nInternal error: verification failed (n=%d).\n", n); exit(3); }
    }
}

/* {1..n-1} を k 組に分けられるか */
static int feasible(int k) {
    static bits R[MAXK];
    bits U;
    K = k;
    memset(&U, 0, sizeof U);
    memset(&LARGE, 0, sizeof LARGE);
    int half = (n + 1) / 2;                     /* ceil(n/2) */
    for (int y = 1; y < half; y++) setb(&U, y);
    for (int y = half; y <= n - 1; y++) setb(&LARGE, y);
    for (int c = 0; c < K; c++) { memset(&R[c], 0, sizeof R[c]); setb(&R[c], n); }   /* S_c = {0} */
    int ok = dfs(R, &U, 0);
    if (ok) verify_partition(R);
    return ok;
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

/* f(n) を計算する（事実 (1)） */
static int compute_f(int nn) {
    n = nn;
    nw = n / 64 + 1;
    if (n == 1) return 0;
    if (n == 2) return 1;
    int f = 2;
    while (!feasible(f)) {
        f++;
        if (f > MAXK) { fprintf(stderr, "\nToo many classes needed (n=%d).\n", n); exit(2); }
    }
    return f;
}

/* ---------------- 保存・再開（安全な I/O） ---------------- */

static const char result_path[] = "b400065_01.txt";
static const char lock_path[] = "b400065_01.txt.lock";
static int fval[MAXN + 1];

/* 結果ファイルを原子的に置き換えても有効な、別ファイルの排他ロック */
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

/* 保存行の形式: 番号が 1 から連続、a(1) = 0、a(2) = 1、n >= 3 では 2 <= a(n) <= MAXK */
static int parse_saved_line(char *line, int expected, int *value) {
    char *p = line, *end;
    while (isspace((unsigned char)*p)) p++;
    if (!isdigit((unsigned char)*p)) return 0;
    errno = 0;
    long index = strtol(p, &end, 10);
    if (errno == ERANGE || index != expected || index > MAXN || !isspace((unsigned char)*end)) return 0;
    p = end;
    while (isspace((unsigned char)*p)) p++;
    if (!isdigit((unsigned char)*p)) return 0;
    errno = 0;
    long parsed = strtol(p, &end, 10);
    if (errno == ERANGE) return 0;
    while (isspace((unsigned char)*end)) end++;
    if (*end) return 0;
    if (expected == 1 ? parsed != 0 : expected == 2 ? parsed != 1 : (parsed < 2 || parsed > MAXK)) return 0;
    *value = (int)parsed;
    return 1;
}

static int load_saved(int saved[], int *count) {
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
    int ok = 1;
    while (fgets(line, sizeof line, in)) {
        size_t length = strlen(line);
        int value;
        if (*count >= MAXN || !length || line[length - 1] != '\n' ||
            !parse_saved_line(line, *count + 1, &value)) {
            fprintf(stderr, "Invalid or incomplete saved row %d; file unchanged.\n", *count + 1);
            ok = 0; break;
        }
        saved[++*count] = value;
    }
    if (ferror(in)) { perror("read saved result"); ok = 0; }
    if (fclose(in) != 0) { perror("close saved result"); ok = 0; }
    return ok;
}

/* 1..count を一時ファイルに書き、同期してから置き換える */
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
    char temporary[] = ".b400065_01.txt.tmp.XXXXXX";
    int fd = mkstemp(temporary);
    if (fd < 0) { perror("create result temporary file"); return 0; }
    FILE *out = fdopen(fd, "w");
    if (!out) {
        int error = errno;
        close(fd); unlink(temporary); errno = error;
        perror("open result temporary file"); return 0;
    }
    int error = 0;
    for (int i = 1; i <= count; i++)
        if (fprintf(out, "%d %d\n", i, fval[i]) < 0) { error = errno ? errno : EIO; break; }
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
        printf("Usage: %s [N] (1 <= N <= %d; default 60)\n", argv[0], MAXN);
        return 0;
    }
    if (argc > 2 || (argc == 2 && !parse_limit(argv[1], &N))) {
        fprintf(stderr, "Usage: %s [N]; N must be a decimal integer in 1..%d.\n", argv[0], MAXN);
        return 1;
    }
    int lock_fd = acquire_lock();
    if (lock_fd < 0) return 1;
    int status = 1, count = 0;
    static int saved[MAXN + 1];
    if (load_saved(saved, &count)) {
        int check_to = count < N ? count : N;
        if (check_to) fprintf(stderr, "Checking saved n=1..%d by recomputation...\n", check_to);
        int ok = 1;
        for (int i = 1; i <= N && ok; i++) {
            int value = compute_f(i);
            if (i <= count && value != saved[i]) {
                fprintf(stderr, "Saved value at n=%d is incorrect; file unchanged.\n", i);
                ok = 0; break;
            }
            fval[i] = value;
            if (i <= count) {
                if (i == check_to) fprintf(stderr, "Saved range n=1..%d verified.\n", check_to);
            } else {
                if (!save_prefix(i)) { ok = 0; break; }      /* 1 項ごとに保存 */
                if (printf("%d %d\n", i, value) < 0 || fflush(stdout) != 0) {
                    perror("write standard output; result file was saved");
                    ok = 0; break;
                }
            }
        }
        if (ok) {
            if (N <= count) fprintf(stderr, "No new rows needed; all %d saved rows were retained.\n", count);
            status = 0;
        }
    }
    close(lock_fd);
    return status;
}
