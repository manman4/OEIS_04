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
 * コンパイル: gcc -O2 -o 400464_01 400464_01.c
 * 実行:       ./400464_01 [N]   （N の既定値は 60、上限 MAXN）
 * 1 項ごとに b400464_01.txt へ書き出し（標準出力にも表示）。
 * 既存の b400464_01.txt があれば、その続きから計算を再開して追記する
 * （既存の行は書き換えない。N まで計算済みなら何もせずに終わる）。
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 1000

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

int main(int argc, char **argv) {
    int N = argc > 1 ? atoi(argv[1]) : 60;
    if (N < 1 || N > MAXN) { fprintf(stderr, "N must be 1..%d\n", MAXN); return 1; }

    used = calloc((size_t)(N + 1) * (N + 1), 1);
    if (!used) { fprintf(stderr, "out of memory\n"); return 1; }
    for (int i = 2; i <= N; i++) if (spf[i] == 0) for (int j = i; j <= N; j += i) if (spf[j] == 0) spf[j] = i;

    /* 既存ファイルから、1 から連続し改行で終わる完全な行だけを読み込む */
    const char *fname = "b400464_01.txt";
    int start = 1;
    fval[0] = 0;
    FILE *in = fopen(fname, "r");
    int junk = 0;                                /* 採用しなかった行が残っているか */
    if (in) {
        char line[128];
        int a, b;
        while (fgets(line, sizeof line, in)) {
            size_t len = strlen(line);
            if (len == 0 || line[len - 1] != '\n' ||
                sscanf(line, "%d %d", &a, &b) != 2 || a != start || a > MAXN) { junk = 1; break; }
            fval[a] = b;
            start++;
        }
        fclose(in);
    }
    if (start > N) {
        /* すでに N まで計算済み。ファイルには触らずに終わる（N を小さく指定しても行は消さない） */
        printf("already computed up to n = %d\n", start - 1);
        return 0;
    }
    if (junk) {
        /* 採用しなかった行（書きかけの行など）があるときだけ、正しい行を一時ファイルに
           書いてから置き換える（置き換えの途中で止まっても元のファイルは残る） */
        char tmpname[64];
        snprintf(tmpname, sizeof tmpname, "%s.tmp", fname);
        FILE *t = fopen(tmpname, "w");
        if (!t) { perror(tmpname); return 1; }
        for (int n = 1; n < start; n++) fprintf(t, "%d %d\n", n, fval[n]);
        if (fclose(t) != 0 || rename(tmpname, fname) != 0) { perror("rewrite"); return 1; }
    }
    FILE *f = fopen(fname, "a");                 /* 以降は追記（既存の行は書き換えない） */
    if (!f) { perror(fname); return 1; }
    if (start > 1) { printf("resume from n = %d\n", start); fflush(stdout); }

    int g = fval[start - 1];
    for (int n = start; n <= N; n++) {
        if (n == 1 || is_prime(n)) {
            g++;                                 /* F(1) = 1, 素数 n では F(n) = F(n-1) + 1 */
        } else {
            memset(used, 0, (size_t)(N + 1) * (N + 1));
            memset(cntp, 0, sizeof cntp);
            k = 0; A[k++] = n;                   /* n を必ず含める */
            count_factors(n, +1);
            target = g + 1; found = 0;
            dfs(n - 1, 0);
            if (found) g++;
        }
        fval[n] = g;
        fprintf(f, "%d %d\n", n, g);
        fflush(f);                               /* 1 項ごとにファイルへ書き出す */
        printf("%d %d\n", n, g);
        fflush(stdout);
    }
    fclose(f);
    return 0;
}
