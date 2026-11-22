// 402607_01.cpp  --  b-file for OEIS A402607
//
// a(n) = number of ways to tile an n X n square with squares of integer side
//        lengths so that the side lengths weakly decrease from left to right
//        along every row and from bottom to top along every column
//        (equivalently: no square has a smaller square immediately to its
//        left or immediately below it).
//        1, 2, 3, 8, 12, 47, 82, 323, 707, 2652, 6156, 27005, ...
//
// Usage:  ./402607_01 N        computes a(1..N); after each n the b-file
//                              b402607_01.txt ("n a(n)") is rewritten atomically
//         ./402607_01 --help
//
// ---------------------------------------------------------------------------
// Cells (i,j), 0 <= i,j < n, row i from the top, are taken in row-major
// order.  Every partial tiling is built by covering the first uncovered cell
// (i,j) with a square whose top-left corner is (i,j); then the covered cells
// of every column form a prefix from the top, and a state is
//    h_c = number of covered cells of column c,
//    s_c = side of the lowest square of column c (0 if h_c = 0).
// The first uncovered cell is in row i = min h_c (over columns with h_c < n),
// at the leftmost such column j.  Since no square with top row > i has been
// placed yet, every covered cell (r,c) with r >= i lies in the lowest square
// of its column.  Hence, for a new square of side k at (i,j):
//    the squares immediately above it are the lowest squares of columns
//      j..j+k-1  (need s_c <= k: sizes weakly increase downwards),
//    the square immediately to its left in rows i.. is the lowest square of
//      column j-1  (need s_{j-1} >= k),
//    a square immediately to its right that is already placed is the lowest
//      square of column j+k, and it is placed iff h_{j+k} > i  (need
//      s_{j+k} <= k);
// every adjacent pair (left/right or above/below) is checked when the later
// of the two squares is placed.  The square fits iff j+k <= n, i+k <= n and
// h_c = i for c = j..j+k-1.  Each tiling corresponds to exactly one sequence
// of placements, so the number of paths from the empty state to the full
// ones is a(n) (the complete states differ only in the s_c and are summed).
// States are processed in increasing order of the first uncovered cell (a
// placement strictly increases it); equal states are merged (one hash map per
// cell, freed when done).
// Checked: n = 1..10 agree with a brute force that builds every tiling and
// tests the condition; n = 1..20 agree with an independent Python version of
// the same DP; a(2) = 2 and a(3) = 3 by hand.
//
// Values: unsigned 128-bit integers; every addition is checked for a carry
// out of 128 bits (then the program stops and writes nothing).
// Keys: 6 bits for h_c and 6 bits for s_c, 5 columns per 64-bit word.
// ---------------------------------------------------------------------------
//
// Build:  g++ -O3 -march=native -std=c++17 -Wall -Wextra -Wpedantic -o 402607_01 402607_01.cpp
//         (option: -DMAXN=n  largest allowed N, default 40, at most 40)

#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <string>
#include <vector>
#include <algorithm>

#include <fcntl.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>

#ifndef MAXN
#define MAXN 40
#endif
static_assert(MAXN >= 1 && MAXN <= 40, "MAXN must be in 1..40 (values < 64, 8 key words)");

__extension__ typedef unsigned __int128 u128;

static const char *OUTFILE = "b402607_01.txt";
static const char *LOCKFILE = "b402607_01.txt.lock";
static const size_t MAX_SAVED_BYTES = 16u << 20;
static const size_t MAX_DIGITS = 2000;
static const int KW = 8;           // key words: 5 columns per word

[[noreturn]] static void die(const char *msg) {
    std::fprintf(stderr, "402607_01: %s\n", msg);
    std::exit(1);
}
[[noreturn]] static void die_errno(const char *msg) {
    std::fprintf(stderr, "402607_01: %s: %s\n", msg, std::strerror(errno));
    std::exit(1);
}

static std::string u128_to_dec(u128 x) {
    if (x == 0) return "0";
    std::string s;
    while (x) { s.push_back((char)('0' + (int)(x % 10))); x /= 10; }
    std::reverse(s.begin(), s.end());
    return s;
}

// ---------------- hash map: key -> u128 ----------------
struct Key { uint64_t w[KW]; };
static bool g_overflow = false;
struct Map {
    size_t cap = 0, cnt = 0;
    Key *keys = nullptr;
    u128 *vals = nullptr;
    unsigned char *used = nullptr;
};
static void map_alloc(Map &m, size_t cap) {
    if (cap < 16) cap = 16;
    if (cap > SIZE_MAX / (sizeof(Key) + sizeof(u128) + 1)) die("hash table too large");
    m.cap = cap; m.cnt = 0;
    m.keys = static_cast<Key *>(std::malloc(cap * sizeof(Key)));
    m.vals = static_cast<u128 *>(std::malloc(cap * sizeof(u128)));
    m.used = static_cast<unsigned char *>(std::calloc(cap, 1));
    if (!m.keys || !m.vals || !m.used) die("out of memory (try a smaller N)");
}
static void map_free(Map &m) {
    std::free(m.keys); std::free(m.vals); std::free(m.used);
    m.keys = nullptr; m.vals = nullptr; m.used = nullptr; m.cap = m.cnt = 0;
}
static int g_kw;                   // words actually used for the current n
static inline size_t slot0(const Key &k, size_t cap) {
    uint64_t h = 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < g_kw; i++) { h ^= k.w[i] + 0x9E3779B97F4A7C15ULL + (h << 6) + (h >> 2); h *= 0xff51afd7ed558ccdULL; h ^= h >> 33; }
    h *= 0xc4ceb9fe1a85ec53ULL; h ^= h >> 33;
    return (size_t)(((u128)h * cap) >> 64);
}
static void map_add(Map &m, const Key &key, u128 v);
static void map_resize(Map &m, size_t newcap) {
    Map n;
    map_alloc(n, newcap);
    for (size_t i = 0; i < m.cap; i++) if (m.used[i]) map_add(n, m.keys[i], m.vals[i]);
    map_free(m);
    m = n;
}
static void map_add(Map &m, const Key &key, u128 v) {
    if (m.cap == 0) map_alloc(m, 64);
    if ((m.cnt + 1) * 20 > m.cap * 17) map_resize(m, m.cap + m.cap / 2 + 16);   // load <= 0.85
    size_t h = slot0(key, m.cap);
    for (;;) {
        if (!m.used[h]) { m.used[h] = 1; m.keys[h] = key; m.vals[h] = v; m.cnt++; return; }
        if (std::memcmp(m.keys[h].w, key.w, sizeof(uint64_t) * (size_t)g_kw) == 0) {
            u128 s = m.vals[h] + v;
            if (s < v) g_overflow = true;      // carry out of 128 bits
            m.vals[h] = s;
            return;
        }
        if (++h == m.cap) h = 0;
    }
}

// column c: word c / 5, bits 12*(c % 5): low 6 bits h_c, high 6 bits s_c
static inline void unpack(const Key &k, int n, int *h, int *s) {
    for (int c = 0; c < n; c++) {
        uint64_t f = (k.w[c / 5] >> (12 * (c % 5))) & 4095;
        h[c] = (int)(f & 63); s[c] = (int)(f >> 6);
    }
}
static inline void pack(Key &k, int n, const int *h, const int *s) {
    std::memset(k.w, 0, sizeof k.w);
    for (int c = 0; c < n; c++) k.w[c / 5] |= (uint64_t)(h[c] | (s[c] << 6)) << (12 * (c % 5));
}
static inline int first_cell(const int *h, int n) {
    int row = n, col = -1;
    for (int c = 0; c < n; c++) if (h[c] < n && h[c] < row) { row = h[c]; col = c; }
    return col < 0 ? -1 : row * n + col;
}

static std::string compute_term(int n) {
    g_kw = (n + 4) / 5;
    if (g_kw > KW) die("internal: key width");
    const int NC = n * n;
    std::vector<Map> bucket(NC + 1);
    g_overflow = false;
    int h[MAXN], s[MAXN];
    for (int c = 0; c < n; c++) { h[c] = 0; s[c] = 0; }
    { Key k0; pack(k0, n, h, s); map_add(bucket[0], k0, (u128)1); }
    size_t total = 0, live = 1, peak = 1;
    time_t t0 = std::time(nullptr);
    for (int f = 0; f < NC; f++) {
        Map &B = bucket[f];
        if (B.cap == 0) continue;
        total += B.cnt;
        for (size_t q = 0; q < B.cap; q++) {
            if (!B.used[q]) continue;
            const u128 v = B.vals[q];
            unpack(B.keys[q], n, h, s);
            if (first_cell(h, n) != f) die("internal: state in the wrong bucket");
            const int i = f / n, j = f % n;
            for (int k = 1; j + k <= n && i + k <= n; k++) {
                const int c = j + k - 1;                     // new column of the square
                if (h[c] != i) break;                        // (i,c) covered: larger squares fail too
                bool ok = true;
                for (int t = j; t <= c && ok; t++) if (s[t] > k) ok = false;      // squares above
                if (ok && j > 0 && s[j - 1] < k) ok = false;                      // square to the left
                if (ok && c + 1 < n && h[c + 1] > i && s[c + 1] > k) ok = false;  // square to the right
                if (!ok) continue;
                int h2[MAXN], s2[MAXN];
                for (int t = 0; t < n; t++) { h2[t] = h[t]; s2[t] = s[t]; }
                for (int t = j; t <= c; t++) { h2[t] = i + k; s2[t] = k; }
                int f2 = first_cell(h2, n);
                if (f2 < 0) f2 = NC;
                else if (f2 <= f) die("internal: first cell did not advance");
                Key K2; pack(K2, n, h2, s2);
                size_t before = bucket[f2].cnt;
                map_add(bucket[f2], K2, v);
                live += bucket[f2].cnt - before;
            }
        }
        live -= B.cnt;
        map_free(B);
        if (live > peak) peak = live;
        if (g_overflow) die("overflow of 128-bit values; nothing written");
        if ((f + 1) % n == 0 && (f + 1) / n % 4 == 0)
            std::fprintf(stderr, "402607_01:   n=%d row %d/%d, %zu states so far, %zu live, %lds\n",
                         n, (f + 1) / n, n, total, live, (long)(std::time(nullptr) - t0));
    }
    // complete tilings: all h_c = n; they still differ in s_c, so sum them
    Map &F = bucket[NC];
    u128 res = 0;
    for (size_t q = 0; q < F.cap; q++) {
        if (!F.used[q]) continue;
        unpack(F.keys[q], n, h, s);
        for (int c = 0; c < n; c++) if (h[c] != n) die("internal: incomplete final state");
        u128 t = res + F.vals[q];
        if (t < res) die("overflow of 128-bit values; nothing written");
        res = t;
    }
    map_free(F);
    std::fprintf(stderr, "402607_01: n=%d: %zu states, peak %zu live, %lds\n", n, total, peak,
                 (long)(std::time(nullptr) - t0));
    return u128_to_dec(res);
}

// ---------------- arguments and files ----------------
static void usage(FILE *f) {
    std::fprintf(f,
        "usage: 402607_01 N\n"
        "  computes a(1..N) (tilings of an n X n square, see source) and\n"
        "  rewrites %s after each n\n"
        "  1 <= N <= %d; saved lines are re-verified, lines beyond N are kept\n",
        OUTFILE, MAXN);
}
static int parse_n(const char *s) {
    if (!*s) die("N must be a positive integer");
    for (const char *p = s; *p; p++)
        if (*p < '0' || *p > '9') die("N must be a positive integer (digits only)");
    errno = 0;
    char *end = nullptr;
    long v = std::strtol(s, &end, 10);
    if (errno || *end || v < 1 || v > MAXN) {
        std::fprintf(stderr, "402607_01: N must satisfy 1 <= N <= %d\n", MAXN);
        std::exit(1);
    }
    return (int)v;
}
static void open_lock() {
    int fd = open(LOCKFILE, O_RDWR | O_CREAT | O_NOFOLLOW | O_CLOEXEC, 0644);
    if (fd < 0) die_errno("cannot open lock file");
    struct stat st;
    if (fstat(fd, &st) != 0) die_errno("fstat lock file");
    if (!S_ISREG(st.st_mode) || st.st_nlink != 1) die("lock file is not a plain regular file");
    if (flock(fd, LOCK_EX | LOCK_NB) != 0) {
        if (errno == EWOULDBLOCK) die("another instance is running (lock held)");
        die_errno("flock");
    }
}
static std::vector<std::string> read_saved() {
    std::vector<std::string> vals;
    int fd = open(OUTFILE, O_RDONLY | O_NOFOLLOW | O_CLOEXEC);
    if (fd < 0) {
        if (errno == ENOENT) return vals;
        die_errno("cannot open saved file (symlink?)");
    }
    struct stat st;
    if (fstat(fd, &st) != 0) die_errno("fstat saved file");
    if (!S_ISREG(st.st_mode) || st.st_nlink != 1) die("saved file is not a plain regular file");
    if ((size_t)st.st_size > MAX_SAVED_BYTES) die("saved file too large");
    std::string data;
    char buf[65536];
    for (;;) {
        ssize_t r = read(fd, buf, sizeof buf);
        if (r < 0) { if (errno == EINTR) continue; die_errno("read saved file"); }
        if (r == 0) break;
        data.append(buf, (size_t)r);
        if (data.size() > MAX_SAVED_BYTES) die("saved file too large");
    }
    if (close(fd) != 0) die_errno("close saved file");
    size_t pos = 0;
    long expect = 1;
    while (pos < data.size()) {
        size_t nl = data.find('\n', pos);
        if (nl == std::string::npos) {
            std::fprintf(stderr, "402607_01: note: ignoring incomplete last line of %s\n", OUTFILE);
            break;
        }
        std::string line = data.substr(pos, nl - pos);
        pos = nl + 1;
        size_t sp = line.find(' ');
        if (sp == std::string::npos || sp == 0 || sp + 1 >= line.size())
            die("saved file: malformed line (file left unchanged)");
        std::string ns = line.substr(0, sp), vs = line.substr(sp + 1);
        for (char ch : ns) if (ch < '0' || ch > '9') die("saved file: bad index (file left unchanged)");
        for (char ch : vs) if (ch < '0' || ch > '9') die("saved file: bad value (file left unchanged)");
        if (ns.size() > 6 || ns[0] == '0' || std::strtol(ns.c_str(), nullptr, 10) != expect)
            die("saved file: indices must be 1,2,3,... (file left unchanged)");
        if (vs.size() > MAX_DIGITS || vs[0] == '0')
            die("saved file: value out of range (must be positive, no leading zeros)");
        vals.push_back(vs);
        expect++;
    }
    return vals;
}
static void write_all(const std::vector<std::string> &vals) {
    struct stat st;
    if (lstat(OUTFILE, &st) == 0) {
        if (!S_ISREG(st.st_mode) || st.st_nlink != 1)
            die("refusing to replace result file: not a plain regular file");
    } else if (errno != ENOENT) {
        die_errno("lstat result file");
    }
    std::string tmpl = std::string(OUTFILE) + ".tmpXXXXXX";
    std::vector<char> name(tmpl.begin(), tmpl.end());
    name.push_back('\0');
    int fd = mkstemp(name.data());
    if (fd < 0) die_errno("mkstemp");
    if (fchmod(fd, 0644) != 0) { unlink(name.data()); die_errno("fchmod"); }
    FILE *f = fdopen(fd, "w");
    if (!f) { close(fd); unlink(name.data()); die_errno("fdopen"); }
    for (size_t i = 0; i < vals.size(); i++)
        if (std::fprintf(f, "%zu %s\n", i + 1, vals[i].c_str()) < 0) { std::fclose(f); unlink(name.data()); die("write to temp file failed"); }
    if (std::fflush(f) != 0) { std::fclose(f); unlink(name.data()); die_errno("fflush temp"); }
    if (fsync(fileno(f)) != 0) { std::fclose(f); unlink(name.data()); die_errno("fsync temp"); }
    if (std::fclose(f) != 0) { unlink(name.data()); die_errno("fclose temp"); }
    if (rename(name.data(), OUTFILE) != 0) { unlink(name.data()); die_errno("rename"); }
    int dfd = open(".", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (dfd < 0) die_errno("open directory");
    if (fsync(dfd) != 0) die_errno("fsync directory");
    if (close(dfd) != 0) die_errno("close directory");
}

int main(int argc, char **argv) {
    if (argc == 2 && (!std::strcmp(argv[1], "--help") || !std::strcmp(argv[1], "-h"))) { usage(stdout); return 0; }
    if (argc != 2) { usage(stderr); return 1; }
    const int N = parse_n(argv[1]);

    open_lock();
    std::vector<std::string> vals = read_saved();
    if (vals.size() > (size_t)N)
        std::fprintf(stderr, "402607_01: note: keeping saved lines beyond N=%d (not re-verified)\n", N);

    for (int n = 1; n <= N; n++) {
        std::string v = compute_term(n);
        if ((size_t)n <= vals.size()) {
            if (vals[(size_t)n - 1] != v) {
                std::fprintf(stderr, "402607_01: saved a(%d) = %s but computed %s; file left unchanged\n",
                             n, vals[(size_t)n - 1].c_str(), v.c_str());
                return 1;
            }
            if (std::printf("%d %s (verified)\n", n, v.c_str()) < 0) die("printf failed");
        } else {
            vals.push_back(v);
            write_all(vals);
            if (std::printf("%d %s\n", n, v.c_str()) < 0) die("printf failed");
        }
        if (std::fflush(stdout) != 0) die("fflush stdout failed");
    }
    return 0;
}
