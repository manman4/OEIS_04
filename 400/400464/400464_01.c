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
 *
 * コンパイル: gcc -O2 -o 400464_01 400464_01.c
 * 実行:       ./400464_01 [N]   （N の既定値は 60、上限 MAXN）
 * 1 項ごとに b400464_01.txt へ書き出し（標準出力にも表示）。
 * 既存の b400464_01.txt があれば、その続きから計算を再開して追記する。
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 1000

static unsigned char *used;          /* used[m] = 1 なら積 m が既出 */
static int A[MAXN + 1], k;           /* 選んだ集合 */
static int target, found;
static int fval[MAXN + 1];           /* 計算済みの F(m) */

/* x, x-1, ..., 1 から選び、|A| が target に達するか */
static void dfs(int x) {
    if (found) return;
    if (k == target) { found = 1; return; }
    if (x < 1) return;
    if (k + fval[x] < target) return;   /* {1..x} からは高々 F(x) 個しか選べない */
    int ok = 1;
    for (int i = 0; i < k; i++) if (used[A[i] * x]) { ok = 0; break; }
    if (ok) {
        for (int i = 0; i < k; i++) used[A[i] * x] = 1;
        A[k++] = x;
        dfs(x - 1);
        k--;
        for (int i = 0; i < k; i++) used[A[i] * x] = 0;
        if (found) return;
    }
    dfs(x - 1);
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

    /* 既存ファイルから、1 から連続し改行で終わる完全な行だけを読み込む */
    const char *fname = "b400464_01.txt";
    int start = 1;
    fval[0] = 0;
    FILE *in = fopen(fname, "r");
    if (in) {
        char line[128];
        int a, b;
        while (fgets(line, sizeof line, in)) {
            size_t len = strlen(line);
            if (len == 0 || line[len - 1] != '\n') break;
            if (sscanf(line, "%d %d", &a, &b) != 2 || a != start || a > N) break;
            fval[a] = b;
            start++;
        }
        fclose(in);
    }
    FILE *f = fopen(fname, "w");
    if (!f) { perror(fname); return 1; }
    for (int n = 1; n < start; n++) fprintf(f, "%d %d\n", n, fval[n]);
    fflush(f);
    if (start > 1) { printf("resume from n = %d\n", start); fflush(stdout); }

    int g = fval[start - 1];
    for (int n = start; n <= N; n++) {
        if (n == 1 || is_prime(n)) {
            g++;                                 /* F(1) = 1, 素数 n では F(n) = F(n-1) + 1 */
        } else {
            memset(used, 0, (size_t)(N + 1) * (N + 1));
            k = 0; A[k++] = n;                   /* n を必ず含める */
            target = g + 1; found = 0;
            dfs(n - 1);
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
