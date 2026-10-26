/*
 * Erdős Problem #795
 * a(n) = g(n) = A ⊆ {1,...,n} で、A のすべての部分集合（空集合を含む）の
 *        積が互いに異なるもののうち、最大の |A|
 * n = 1..N について計算し b401472_01.txt に "n a(n)" 形式で保存
 * （g(1) = 0: 空集合の積 1 と {1} の積 1 が等しいので 1 は使えない）
 *
 * 方針:
 *   各 m を素因数の指数ベクトル vec[m] とみなし、1 つの 64 bit 整数に
 *   素数ごと 6 bit で詰める（N <= 64 なら指数の和は 63 を超えない）。
 *   選んだ集合の部分和ベクトルの集合 P を保持し、x を加えられるのは
 *   (P + vec[x]) ∩ P = ∅ のときだけ（このとき P は P ∪ (P + vec[x]) に倍増）。
 *   g(n) は g(n-1) か g(n-1)+1 なので、n を必ず含む大きさ g(n-1)+1 の集合が
 *   {2,...,n} にあるかを枝刈り付き深さ優先探索で調べる。
 * 高速化（どれも結果を変えない）:
 *   - n が素数なら g(n) = g(n-1) + 1（n の成分は n 自身にしか現れない）。
 *   - 探索中、{2,...,x} から追加で選べる個数は高々 g(x)（計算済み）なので
 *     chosen + g(x) < target なら枝刈りする（以前は x - 1 で抑えていた）。
 *
 * コンパイル: gcc -O2 -o 401272_01 401272_01.c
 * 実行:       ./401272_01 [N]   （N の既定値は 30、上限 64）
 * 1 項ごとに b401272_01.txt へ書き出し（標準出力にも表示）。
 * 既存の b401272_01.txt があれば、その続きから計算を再開して追記する。
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 64
typedef uint64_t u64;

static int primes[20], np;
static u64 vec[MAXN + 1];
static int target, found;
static int gval[MAXN + 1];   /* 計算済みの g(m) */

/* 部分和ベクトルの集合 P（線形探索法のハッシュ表） */
#define HB 22
#define HS (1u << HB)
static u64 *tab;
static unsigned char *used;
static u64 *list;   /* P の要素の一覧（追加順） */
static int top;

static inline unsigned hsh(u64 x) {
    x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33;
    return (unsigned)x & (HS - 1);
}
static int has(u64 x) {
    unsigned i = hsh(x);
    while (used[i]) { if (tab[i] == x) return 1; i = (i + 1) & (HS - 1); }
    return 0;
}
static void ins(u64 x) {
    unsigned i = hsh(x);
    while (used[i]) { if (tab[i] == x) return; i = (i + 1) & (HS - 1); }
    used[i] = 1; tab[i] = x;
}
/* 削除（後方シフトで探索列を保つ） */
static void del(u64 x) {
    unsigned i = hsh(x);
    while (!(used[i] && tab[i] == x)) i = (i + 1) & (HS - 1);
    used[i] = 0;
    unsigned j = i;
    for (;;) {
        j = (j + 1) & (HS - 1);
        if (!used[j]) break;
        unsigned k = hsh(tab[j]);
        if ((j > i && (k <= i || k > j)) || (j < i && (k <= i && k > j))) {
            used[i] = 1; tab[i] = tab[j]; used[j] = 0; i = j;
        }
    }
}

/* x を加えられれば P を更新して 1、できなければ 0 */
static int add(u64 x) {
    int base = top;
    for (int i = 0; i < base; i++) if (has(list[i] + x)) return 0;
    for (int i = 0; i < base; i++) { list[top] = list[i] + x; ins(list[top]); top++; }
    return 1;
}
static void undo(int base) { while (top > base) { top--; del(list[top]); } }

/* x, x-1, ..., 2 から選び、選んだ個数が target に達するか */
static void dfs(int x, int chosen) {
    if (found) return;
    if (chosen == target) { found = 1; return; }
    if (x < 2) return;
    /* {2,...,x} から追加で選べるのは、それ自身が条件を満たす集合なので高々 g(x) 個 */
    if (chosen + gval[x] < target) return;
    int base = top;
    if (add(vec[x])) { dfs(x - 1, chosen + 1); undo(base); if (found) return; }
    dfs(x - 1, chosen);
}

int main(int argc, char **argv) {
    int N = argc > 1 ? atoi(argv[1]) : 30;
    if (N < 1 || N > MAXN) { fprintf(stderr, "N must be 1..%d\n", MAXN); return 1; }

    for (int p = 2; p <= N; p++) {
        int ip = 1;
        for (int q = 2; q * q <= p; q++) if (p % q == 0) { ip = 0; break; }
        if (ip) primes[np++] = p;
    }
    for (int m = 1; m <= N; m++) {
        u64 v = 0; int x = m;
        for (int i = 0; i < np; i++) {
            int e = 0;
            while (x % primes[i] == 0) { x /= primes[i]; e++; }
            v += (u64)e << (6 * i);
        }
        vec[m] = v;
    }

    tab = malloc(sizeof(u64) * HS);
    used = calloc(HS, 1);
    list = malloc(sizeof(u64) * (HS / 2));
    if (!tab || !used || !list) { fprintf(stderr, "out of memory\n"); return 1; }

    /* 既存の b401472_01.txt があれば、1 から連続して書かれている行を読み込み、
       その続きから計算して追記する（途中で止めても再開できる） */
    const char *fname = "b401472_01.txt";
    int start = 1;                              /* 次に計算する n */
    gval[0] = 0;
    FILE *in = fopen(fname, "r");
    if (in) {
        char line[128];
        int a, b;
        /* 改行で終わる完全な行だけを採用する（書き込み途中で止まった最終行は捨てる） */
        while (fgets(line, sizeof line, in)) {
            size_t len = strlen(line);
            if (len == 0 || line[len - 1] != '\n') break;
            if (sscanf(line, "%d %d", &a, &b) != 2 || a != start || a > N) break;
            gval[a] = b;
            start++;
        }
        fclose(in);
    }
    /* 読み込めた行だけを残してファイルを書き直し、以降は追記する */
    FILE *f = fopen(fname, "w");
    if (!f) { perror(fname); return 1; }
    for (int n = 1; n < start; n++) fprintf(f, "%d %d\n", n, gval[n]);
    fflush(f);
    if (start > 1) printf("resume from n = %d\n", start);

    if (start == 1) {                           /* g(1) = 0 */
        gval[1] = 0;
        fprintf(f, "1 0\n");
        fflush(f);
        printf("1 0\n");
        fflush(stdout);
        start = 2;
    }
    int g = gval[start - 1];
    for (int n = start; n <= N; n++) {
        /* n が素数なら、g(n-1) を与える集合に n を加えても条件は保たれる
           （素数 n の指数ベクトルは n 自身にしか現れない成分をもつ）ので g(n) = g(n-1) + 1 */
        if (np > 0) {
            int isprime = 1;
            for (int q = 2; q * q <= n; q++) if (n % q == 0) { isprime = 0; break; }
            if (isprime) {
                g++; gval[n] = g;
                fprintf(f, "%d %d\n", n, g);
                fflush(f);                      /* 1 項ごとにファイルへ書き出す */
                printf("%d %d\n", n, g);
                fflush(stdout);
                continue;
            }
        }
        memset(used, 0, HS);
        top = 0; list[top++] = 0; ins(0);      /* P = {空集合の積} */
        target = g + 1; found = 0;
        if (add(vec[n])) dfs(n - 1, 1);         /* n を必ず含める */
        if (found) g++;
        gval[n] = g;
        fprintf(f, "%d %d\n", n, g);
        fflush(f);                              /* 1 項ごとにファイルへ書き出す */
        printf("%d %d\n", n, g);
        fflush(stdout);
    }
    fclose(f);
    return 0;
}
