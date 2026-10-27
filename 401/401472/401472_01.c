/*
 * Erdős Problem #795
 * a(n) = g(n) = A ⊆ {1,...,n} で、A のすべての部分集合（空集合を含む）の
 *        積が互いに異なるもののうち、最大の |A|
 * n = 1..N について計算し b401472_01.txt に "n a(n)" 形式で保存
 * （g(1) = 0: 空集合の積 1 と {1} の積 1 が等しいので 1 は使えない）
 *
 * 方針:
 *   各 m を素因数の指数ベクトル vec[m] とみなし、1 つの 64 bit 整数に詰める。
 *   素数 p の成分の幅は v_p(N!) が入るビット数（部分和の指数は v_p(N!) 以下なので
 *   足し算で桁あふれしない）。N = 64 でも幅の合計は 42 bit。
 *   （旧版は素数ごと 6 bit 固定で、11 番目以降の素数（37 以上）が 64 bit を
 *    はみ出していたため、n >= 38 の結果は信頼できない。）
 *   選んだ集合の部分和ベクトルの集合 P を保持し、x を加えられるのは
 *   (P + vec[x]) ∩ P = ∅ のときだけ（このとき P は P ∪ (P + vec[x]) に倍増）。
 *   g(n) は g(n-1) か g(n-1)+1 なので、n を必ず含む大きさ g(n-1)+1 の集合が
 *   {2,...,n} にあるかを枝刈り付き深さ優先探索で調べる。
 * 高速化（どれも結果を変えない）:
 *   - n が素数なら g(n) = g(n-1) + 1（n の成分は n 自身にしか現れない）。
 *   - 探索中、{2,...,x} から追加で選べる個数は高々 g(x)（計算済み）なので
 *     chosen + g(x) < target なら枝刈りする（以前は x - 1 で抑えていた）。
 *   - 「自由な素数」: 探索で x に来たとき、x が素数で、それまでに選んだ要素
 *     （すべて x より大きい）に x の倍数がなければ、x の成分は最終的な集合で
 *     x 自身にしか現れない。よって x は必ず選んでよく（選ばない枝は調べない）、
 *     しかも以後の判定に影響しないので P に加えず個数だけ数える（P が倍増しない）。
 *     n/2 < x < n の素数は常にこれに当たる。
 *   - ハッシュ表の大きさを n ごとに |P| の上限 2^target に合わせて決める
 *     （小さい表はキャッシュに乗るので速い）。空きは番兵値で表し、別配列を使わない。
 *
 * 安全装置:
 *   - 指数ベクトルが 63 bit に収まらない N では起動時にエラーで止まる。
 *   - 必要な表の大きさが 2^MAXHB を超える n ではエラーで止まる
 *     （そこまでに b401472_01.txt へ書いた項は正しい）。
 *
 * コンパイル: gcc -O2 -o 401472_01 401472_01.c
 *            （表の上限を上げるなら gcc -O2 -DMAXHB=28 -o 401472_01 401472_01.c）
 * 実行:       ./401472_01 [N]   （N の既定値は 30、上限 64）
 * 再開時は、利用する保存値を n = 1 から再計算して照合する。誤りや不完全な行を
 * 見つけた場合は、保存ファイルを変更せず停止する。既存の行を上界として信用しない。
 * 1 項ごとに b401472_01.txt へ書き出し（標準出力にも表示）。
 * 検証後に続きを計算する。保存は固有の一時ファイルからの原子的な置換とし、
 * 書込み失敗・同時実行・シンボリックリンクへの出力を拒否する。
 * 詳細な範囲と検証方法は 401472_c_safety.md を参照。
 */
#define _POSIX_C_SOURCE 200809L
#ifdef __APPLE__
#define _DARWIN_C_SOURCE
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>

#define MAXN 64
typedef uint64_t u64;

static int primes[20], np;
static u64 vec[MAXN + 1];
static int target, found;
static int isprime_[MAXN + 1];   /* isprime_[x] = 1: x は素数 */
static int pf[MAXN + 1][8], npf[MAXN + 1];  /* x の相異なる素因数 */
static int cntp[MAXN + 1];       /* cntp[p] = 選んだ要素のうち p の倍数の個数 */
static int gval[MAXN + 1];   /* 計算済みの g(m) */

/* 部分和ベクトルの集合 P（線形探索法のハッシュ表）
   空きは EMPTY（全ビット 1）で表す。指数ベクトルは高々 63 bit なので EMPTY と衝突しない。
   表の大きさは n ごとに、その n で P がとりうる最大の大きさ 2^target の 4 倍
   （埋まり具合 25% 以下）に合わせて決める。小さい表はキャッシュに乗るので速い。
   必要な大きさだけ確保し、MAXHB で上限を決める（26で最大512 MiB + 128 MiB）。 */
#ifndef MAXHB
#define MAXHB 26
#endif
#if MAXHB < 10 || MAXHB > 30
#error "MAXHB must be in 10..30"
#endif
_Static_assert(sizeof(unsigned) * CHAR_BIT >= 32, "32-bit unsigned required");
_Static_assert(SIZE_MAX >= UINT32_MAX, "32-bit size_t required");
#define EMPTY (~(u64)0)
static u64 *tab;
static unsigned mask;      /* 表の大きさ - 1 */
static u64 *list;          /* P の要素の一覧（追加順） */
static long cap;           /* list に入る最大要素数 */
static long top;
static int allocated_hb;
static int vector_bits;
static const char result_path[] = "b401472_01.txt";

/* The hash multiplication deliberately wraps modulo 2^64. */
#ifdef __clang__
__attribute__((no_sanitize("unsigned-integer-overflow")))
#endif
static inline unsigned hsh(u64 x) {
    x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33;
    return (unsigned)x & mask;
}
static inline int has(u64 x) {
    unsigned i = hsh(x);
    while (tab[i] != EMPTY) { if (tab[i] == x) return 1; i = (i + 1) & mask; }
    return 0;
}
static inline void ins(u64 x) {
    unsigned i = hsh(x);
    while (tab[i] != EMPTY) { if (tab[i] == x) return; i = (i + 1) & mask; }
    tab[i] = x;
}
/* 削除（後方シフトで探索列を保つ） */
static void del(u64 x) {
    unsigned i = hsh(x);
    while (tab[i] != x) i = (i + 1) & mask;
    tab[i] = EMPTY;
    unsigned j = i;
    for (;;) {
        j = (j + 1) & mask;
        if (tab[j] == EMPTY) break;
        unsigned k = hsh(tab[j]);
        if ((j > i && (k <= i || k > j)) || (j < i && (k <= i && k > j))) {
            tab[i] = tab[j]; tab[j] = EMPTY; i = j;
        }
    }
}

/* x を加えられれば P を更新して 1、できなければ 0 */
static int add(u64 x) {
    long base = top;
    /* P は倍増する。容量を超えるなら中止する（範囲外書き込み・無限ループの防止）。
       target 個まで選ぶので |P| <= 2^target で、表はそれに合わせて確保してある。 */
    if (base * 2 > cap) {
        fprintf(stderr, "internal error: |P| would be %ld > capacity %ld\n", base * 2, cap);
        exit(1);
    }
    for (long i = 0; i < base; i++) if (has(list[i] + x)) return 0;
    for (long i = 0; i < base; i++) { list[top] = list[i] + x; ins(list[top]); top++; }
    return 1;
}
static void undo(long base) { while (top > base) { top--; del(list[top]); } }

/* x, x-1, ..., 2 から選び、選んだ個数が target に達するか */
static void dfs(int x, int chosen) {
    if (found) return;
    if (chosen == target) { found = 1; return; }
    if (x < 2) return;
    /* {2,...,x} から追加で選べるのは、それ自身が条件を満たす集合なので高々 g(x) 個 */
    if (chosen + gval[x] < target) return;
    if (isprime_[x] && cntp[x] == 0) {
        /* 「自由な素数」: x は素数で、これまでに選んだ要素（すべて x より大きい）に
           x の倍数がない。これから選ぶ要素は x 未満なので x の倍数ではない。
           よって x の成分は最終的な集合の中で x 自身にしか現れず、
           (1) x を加えても適格性は崩れない → x を選ばない枝は調べなくてよい
               （x を選ばない解があれば、x を加えたものも解で、要素数は target 以上）。
           (2) 以後の判定にも影響しない: P は x 成分 0 の層と 1 の層に分かれ、
               以後の要素は x 成分 0 なので、各層で同じ判定になる。
               よって P に x を加えず、個数だけ数えればよい（P が倍増しない）。 */
        dfs(x - 1, chosen + 1);
        return;
    }
    long base = top;
    if (add(vec[x])) {
        for (int i = 0; i < npf[x]; i++) cntp[pf[x][i]]++;
        dfs(x - 1, chosen + 1);
        for (int i = 0; i < npf[x]; i++) cntp[pf[x][i]]--;
        undo(base);
        if (found) return;
    }
    dfs(x - 1, chosen);
}

/* Rebuild the layout independently of any saved numerical results. */
static int initialize_vectors(int N) {
    if (N < 1 || N > MAXN) return 0;
    np = 0;
    memset(vec, 0, sizeof vec);
    memset(npf, 0, sizeof npf);
    memset(isprime_, 0, sizeof isprime_);
    for (int p = 2; p <= N; p++) {
        int prime = 1;
        for (int q = 2; q <= p / q; q++)
            if (p % q == 0) { prime = 0; break; }
        if (prime) primes[np++] = p;
    }
    int shift[20], total = 0;
    for (int i = 0; i < np; i++) {
        int p = primes[i], vmax = 0;
        for (int q = p; q <= N;) {
            vmax += N / q;
            if (q > N / p) break;
            q *= p;
        }
        int width = 0;
        while ((1u << width) <= (unsigned)vmax) width++;
        shift[i] = total;
        total += width;
    }
    if (total > 63) {
        fprintf(stderr, "Exponent vectors need %d bits; limit is 63.\n", total);
        return 0;
    }
    vector_bits = total;
    for (int m = 2; m <= N; m++) {
        int x = m;
        for (int i = 0; i < np; i++) {
            int exponent = 0;
            while (x % primes[i] == 0) { x /= primes[i]; exponent++; }
            vec[m] |= (u64)exponent << shift[i];
            if (exponent) pf[m][npf[m]++] = primes[i];
        }
        isprime_[m] = npf[m] == 1 && pf[m][0] == m;
    }
    return 1;
}

static void release_tables(void) {
    free(tab); free(list);
    tab = NULL; list = NULL; allocated_hb = 0;
}

static int prepare_table(void) {
    int hb = target + 2;
    if (hb < 10) hb = 10;
    if (hb > MAXHB) {
        fprintf(stderr, "Search needs 2^%d table entries; MAXHB=%d. "
                        "No unproved value was saved.\n", hb, MAXHB);
        return 0;
    }
    size_t entries = (size_t)1 << hb;
    long new_cap = 1L << (hb - 2);
    if (entries > SIZE_MAX / sizeof *tab ||
        (size_t)new_cap > SIZE_MAX / sizeof *list) {
        fprintf(stderr, "Table byte count exceeds size_t.\n");
        return 0;
    }
    if (allocated_hb != hb) {
        release_tables();
        tab = malloc(entries * sizeof *tab);
        list = malloc((size_t)new_cap * sizeof *list);
        if (!tab || !list) {
            fprintf(stderr, "Out of memory; previous results are unchanged.\n");
            release_tables();
            return 0;
        }
        allocated_hb = hb;
    }
    mask = (1u << hb) - 1;
    cap = new_cap;
    for (size_t i = 0; i < entries; i++) tab[i] = EMPTY;
    memset(cntp, 0, sizeof cntp);
    top = 1; list[0] = 0; ins(0);
    return 1;
}

static int next_value(int n, int *value) {
    if (n == 1) { *value = 0; return 1; }
    int previous = gval[n - 1];
    if (isprime_[n]) { *value = previous + 1; return 1; }
    target = previous + 1;
    found = 0;
    if (!prepare_table()) return 0;
    if (add(vec[n])) {
        for (int i = 0; i < npf[n]; i++) cntp[pf[n][i]]++;
        dfs(n - 1, 1);
    }
    *value = previous + found;
    return 1;
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
    const char lock_path[] = "b401472_01.txt.lock";
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
    if (errno == ERANGE || parsed < 0 || parsed >= expected) return 0;
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
    char temporary[] = ".b401472_01.txt.tmp.XXXXXX";
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
        if (fprintf(out, "%d %d\n", n, gval[n]) < 0) {
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
    if (!load_saved(saved, &count) || !initialize_vectors(N)) goto done;
    memset(gval, 0, sizeof gval);
    int check_to = count < N ? count : N;
    if (check_to)
        fprintf(stderr, "Checking saved n=1..%d from the definition...\n", check_to);
    for (int n = 1; n <= N; n++) {
        int value;
        if (!next_value(n, &value)) goto done;
        if (n <= count && value != saved[n]) {
            fprintf(stderr, "Saved value at n=%d is incorrect; file unchanged.\n", n);
            goto done;
        }
        gval[n] = value;
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
    release_tables();
    close(lock_fd);
    return status;
}
