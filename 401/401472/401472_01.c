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
 * 注意: 旧版で作った b401472_01.txt に n >= 38 の行があれば、再開前にその行を
 *       消すこと（再開時は既存の行をそのまま信じて続きを計算するため）。
 * 1 項ごとに b401472_01.txt へ書き出し（標準出力にも表示）。
 * 既存の b401472_01.txt があれば、その続きから計算を再開して追記する。
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
static int isprime_[MAXN + 1];   /* isprime_[x] = 1: x は素数 */
static int pf[MAXN + 1][8], npf[MAXN + 1];  /* x の相異なる素因数 */
static int cntp[MAXN + 1];       /* cntp[p] = 選んだ要素のうち p の倍数の個数 */
static int gval[MAXN + 1];   /* 計算済みの g(m) */

/* 部分和ベクトルの集合 P（線形探索法のハッシュ表）
   空きは EMPTY（全ビット 1）で表す。指数ベクトルは高々 63 bit なので EMPTY と衝突しない。
   表の大きさは n ごとに、その n で P がとりうる最大の大きさ 2^target の 4 倍
   （埋まり具合 25% 以下）に合わせて決める。小さい表はキャッシュに乗るので速い。
   MAXHB で上限を決める（MAXHB = 26 で tab 512 MB + list 128 MB）。 */
#ifndef MAXHB
#define MAXHB 26
#endif
#define EMPTY (~(u64)0)
static u64 *tab;
static unsigned mask;      /* 表の大きさ - 1 */
static u64 *list;          /* P の要素の一覧（追加順） */
static long cap;           /* list に入る最大要素数 */
static long top;

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

int main(int argc, char **argv) {
    int N = argc > 1 ? atoi(argv[1]) : 30;
    if (N < 1 || N > MAXN) { fprintf(stderr, "N must be 1..%d\n", MAXN); return 1; }

    for (int p = 2; p <= N; p++) {
        int ip = 1;
        for (int q = 2; q * q <= p; q++) if (p % q == 0) { ip = 0; break; }
        if (ip) primes[np++] = p;
    }
    /* 素数 p の成分の幅は、部分和の指数の最大値 v_p(N!) が入るビット数にする。
       （部分和は 1..N の相異なる数の積なので、p の指数は v_p(N!) を超えない）
       幅の合計が 64 を超えたら安全に詰められないので中止する。 */
    int shift[20], total = 0;
    for (int i = 0; i < np; i++) {
        int p = primes[i], vmax = 0;
        for (long q = p; q <= N; q *= p) vmax += N / q;   /* v_p(N!) */
        int w = 0;
        while ((1 << w) <= vmax) w++;                       /* vmax を表せるビット数 */
        shift[i] = total;
        total += w;
    }
    if (total > 63) { fprintf(stderr, "exponent vectors do not fit in 64 bits (%d bits)\n", total); return 1; }
    for (int m = 1; m <= N; m++) {
        u64 v = 0; int x = m;
        for (int i = 0; i < np; i++) {
            int e = 0;
            while (x % primes[i] == 0) { x /= primes[i]; e++; }
            v += (u64)e << shift[i];
        }
        vec[m] = v;
    }
    for (int m = 2; m <= N; m++) {
        int x = m;
        npf[m] = 0;
        for (int i = 0; i < np; i++) {
            if (x % primes[i] == 0) {
                pf[m][npf[m]++] = primes[i];
                while (x % primes[i] == 0) x /= primes[i];
            }
        }
        isprime_[m] = (npf[m] == 1 && pf[m][0] == m);
    }

    tab = malloc(sizeof(u64) << MAXHB);
    list = malloc(sizeof(u64) << (MAXHB - 2));
    if (!tab || !list) { fprintf(stderr, "out of memory\n"); return 1; }

    /* 既存の b401472_01.txt があれば、1 から連続して書かれている行を読み込み、
       その続きから計算して追記する（途中で止めても再開できる） */
    const char *fname = "b401472_01.txt";
    int start = 1;                              /* 次に計算する n */
    gval[0] = 0;
    int junk = 0;                               /* 採用しなかった行が残っているか */
    FILE *in = fopen(fname, "r");
    if (in) {
        char line[128];
        int a, b;
        /* 改行で終わる完全な行だけを採用する（書き込み途中で止まった最終行は捨てる） */
        while (fgets(line, sizeof line, in)) {
            size_t len = strlen(line);
            if (len == 0 || line[len - 1] != '\n' ||
                sscanf(line, "%d %d", &a, &b) != 2 || a != start || a > MAXN) { junk = 1; break; }
            gval[a] = b;
            start++;
        }
        fclose(in);
    }
    if (start > N) {
        /* すでに N まで計算済み。ファイルには触らずに終わる（N を小さく指定しても行は消さない） */
        printf("already computed up to n = %d\n", start - 1);
        return 0;
    }
    FILE *f;
    if (junk) {
        /* 採用しなかった行（書きかけの行など）があるときだけ、正しい行を一時ファイルに
           書いてから置き換える（置き換えの途中で止まっても元のファイルは残る） */
        char tmpname[64];
        snprintf(tmpname, sizeof tmpname, "%s.tmp", fname);
        FILE *t = fopen(tmpname, "w");
        if (!t) { perror(tmpname); return 1; }
        for (int n = 1; n < start; n++) fprintf(t, "%d %d\n", n, gval[n]);
        if (fclose(t) != 0 || rename(tmpname, fname) != 0) { perror("rewrite"); return 1; }
    }
    /* 以降は追記（既存の行は書き換えない） */
    f = fopen(fname, "a");
    if (!f) { perror(fname); return 1; }
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
        target = g + 1; found = 0;
        /* |P| <= 2^target。表の大きさを 2^(target+2)（埋まり具合 25% 以下）にする */
        int hb = target + 2;
        if (hb < 10) hb = 10;
        if (hb > MAXHB) {
            fprintf(stderr, "n = %d needs 2^%d table entries; recompile with -DMAXHB=%d\n", n, hb, hb);
            return 1;
        }
        mask = (1u << hb) - 1;
        cap = 1L << (hb - 2);
        for (unsigned i = 0; i <= mask; i++) tab[i] = EMPTY;
        for (int x = 0; x <= N; x++) cntp[x] = 0;
        top = 0; list[top++] = 0; ins(0);      /* P = {空集合の積} */
        if (add(vec[n])) {                      /* n を必ず含める */
            for (int i = 0; i < npf[n]; i++) cntp[pf[n][i]]++;
            dfs(n - 1, 1);
        }
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
