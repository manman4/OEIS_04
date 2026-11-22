// 402607_02.cpp  --  b-file for OEIS A402607 (column-transfer version)
//
// a(n) = number of ways to tile an n X n square with squares of integer side
//        lengths so that the side lengths weakly decrease from left to right
//        along every row and from bottom to top along every column
//        (equivalently: no square has a smaller square immediately to its
//        left or immediately below it).
//        1, 2, 3, 8, 12, 47, 82, 323, 707, 2652, 6156, 27005, ...
//
// Usage:  ./402607_02 N        computes a(1..N); after each n the b-file
//                              b402607_02.txt ("n a(n)") is rewritten atomically
//         ./402607_02 --help
//
// ---------------------------------------------------------------------------
// We count the mirror images in the horizontal midline: tilings in which the
// side lengths weakly decrease from left to right along every row and from
// top to bottom along every column (same number).
//
// Column transfer.  Sweep the columns c = 0..n-1 from left to right.  The
// squares meeting column c, read from top to bottom, have weakly decreasing
// sizes (column condition) and their sizes add up to n; for each of them we
// record its size s and its phase p (= c minus its leftmost column,
// 0 <= p <= s-1).  This sequence of (s,p) is the state of column c.
// Column c -> c+1: every square with p < s-1 continues as (s,p+1) in the same
// rows; the other rows (where squares ended) are filled, from top to bottom,
// by new squares (t,0) such that
//    - each lies inside one block of free rows (it may not overlap a
//      continuing square) and fits: c+1+t <= n;
//    - the whole new column still has weakly decreasing sizes from top to
//      bottom (continuing squares included);
//    - every square of column c in its rows has size >= t (row condition:
//      these are exactly the horizontal adjacencies between different
//      squares; a continuing square is its own left neighbour).
// Column 0 consists of new squares only (no left neighbours).  A tiling is
// complete iff after column n-1 every square has p = s-1.
// Every tiling gives exactly one admissible sequence of column states and
// conversely, so a(n) is the number of admissible sequences.  The number of
// states of a column is at most the number of partitions of n with a phase
// 0 <= p < s attached to each part s (cf. A006906), far fewer than in the
// skyline method of 402607_01.cpp.
// Checked: n = 1..27 agree with 402607_01.cpp (skyline method) and its
// mirrored version; n = 1..10 agree with a brute force that builds every
// tiling and tests the condition.
//
// Values: unsigned 128-bit integers; every addition is checked for a carry out
// of 128 bits (then the program stops and writes nothing).
// Keys: one 10-bit code s(s-1)/2 + p per square, top to bottom (the sizes add
// up to n, so the sequence is self-delimiting); at most 7 words for n <= 40.
// ---------------------------------------------------------------------------
//
// Build:  g++ -O3 -march=native -std=c++17 -Wall -Wextra -Wpedantic -o 402607_02 402607_02.cpp
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
static_assert(MAXN >= 1 && MAXN <= 40, "MAXN must be in 1..40 (codes < 1024, 7 key words)");

__extension__ typedef unsigned __int128 u128;

static const char *OUTFILE = "b402607_02.txt";
static const char *LOCKFILE = "b402607_02.txt.lock";
static const size_t MAX_SAVED_BYTES = 16u << 20;
static const size_t MAX_DIGITS = 2000;
static const int KW = 7;           // key words (40 squares * 10 bits <= 448 bits)

[[noreturn]] static void die(const char *msg) {
    std::fprintf(stderr, "402607_02: %s\n", msg);
    std::exit(1);
}
[[noreturn]] static void die_errno(const char *msg) {
    std::fprintf(stderr, "402607_02: %s: %s\n", msg, std::strerror(errno));
    std::exit(1);
}

static std::string u128_to_dec(u128 x) {
    if (x == 0) return "0";
    std::string s;
    while (x) { s.push_back((char)('0' + (int)(x % 10))); x /= 10; }
    std::reverse(s.begin(), s.end());
    return s;
}

// ---------------- hash map: KW-word key -> u128 ----------------
struct Key { uint64_t w[KW]; };
static bool g_overflow = false;
static const uint64_t EMPTY0 = ~0ULL;   // word 0 of a real key never is all ones (codes use 10 bits, unused bits 0)
struct Map {
    size_t cap = 0, cnt = 0;
    Key *keys = nullptr;
    u128 *vals = nullptr;
};
static void map_alloc(Map &m, size_t cap) {
    if (cap < 64) cap = 64;
    if (cap > SIZE_MAX / (sizeof(Key) + sizeof(u128))) die("hash table too large");
    m.cap = cap; m.cnt = 0;
    m.keys = static_cast<Key *>(std::malloc(cap * sizeof(Key)));
    m.vals = static_cast<u128 *>(std::malloc(cap * sizeof(u128)));
    if (!m.keys || !m.vals) die("out of memory (try a smaller N)");
    for (size_t i = 0; i < cap; i++) m.keys[i].w[0] = EMPTY0;
}
static void map_free(Map &m) { std::free(m.keys); std::free(m.vals); m.keys = nullptr; m.vals = nullptr; m.cap = m.cnt = 0; }
static void map_clear(Map &m) { for (size_t i = 0; i < m.cap; i++) m.keys[i].w[0] = EMPTY0; m.cnt = 0; }
static inline size_t slot0(const Key &k, size_t cap) {
    uint64_t h = 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < KW; i++) { h ^= k.w[i] + 0x9E3779B97F4A7C15ULL + (h << 6) + (h >> 2); h *= 0xff51afd7ed558ccdULL; h ^= h >> 33; }
    h *= 0xc4ceb9fe1a85ec53ULL; h ^= h >> 33;
    return (size_t)(((u128)h * cap) >> 64);
}
static void map_add(Map &m, const Key &key, u128 v);
static void map_resize(Map &m, size_t newcap) {
    Map n;
    map_alloc(n, newcap);
    for (size_t i = 0; i < m.cap; i++) if (m.keys[i].w[0] != EMPTY0) map_add(n, m.keys[i], m.vals[i]);
    map_free(m);
    m = n;
}
static void map_add(Map &m, const Key &key, u128 v) {
    if ((m.cnt + 1) * 10 > m.cap * 7) map_resize(m, m.cap * 2);       // load <= 0.7
    size_t h = slot0(key, m.cap);
    for (;;) {
        Key &k = m.keys[h];
        if (k.w[0] == EMPTY0) { k = key; m.vals[h] = v; m.cnt++; return; }
        if (std::memcmp(k.w, key.w, sizeof k.w) == 0) {
            u128 s = m.vals[h] + v;
            if (s < v) g_overflow = true;      // carry out of 128 bits
            m.vals[h] = s;
            return;
        }
        if (++h == m.cap) h = 0;
    }
}

// ---------------- column states ----------------
struct Sq { int s, p; };
static inline void encode(const Sq *q, int m, Key &k) {
    std::memset(k.w, 0, sizeof k.w);
    for (int i = 0; i < m; i++) {
        const uint64_t code = (uint64_t)(q[i].s * (q[i].s - 1) / 2 + q[i].p);   // < 820 for s <= 40
        const int b = 10 * i, w = b / 64, sh = b % 64;
        k.w[w] |= code << sh;
        if (sh > 54) k.w[w + 1] |= code >> (64 - sh);
    }
}
static inline int decode(const Key &k, int n, Sq *q) {
    int m = 0, rows = 0;
    while (rows < n) {
        const int b = 10 * m, w = b / 64, sh = b % 64;
        uint64_t code = k.w[w] >> sh;
        if (sh > 54) code |= k.w[w + 1] << (64 - sh);
        code &= 1023;
        int s = 1;
        while ((uint64_t)(s * (s + 1) / 2) <= code) s++;     // s(s-1)/2 <= code < s(s+1)/2
        q[m].s = s; q[m].p = (int)code - s * (s - 1) / 2;
        rows += s; m++;
    }
    if (rows != n) die("internal: bad column state");
    return m;
}

// generation of the next column
static int g_n, g_col;                     // g_col: index of the column being built
static int g_cont[MAXN + 1];               // g_cont[r] = size of a continuing square starting at row r (0 if none)
static int g_cphase[MAXN + 1];
static bool g_controw[MAXN + 1];           // row covered by a continuing square
static int g_left[MAXN + 1];               // size of the square of the previous column in row r (0 for column 0)
static Map *g_out;
static u128 g_val;
static Sq g_seq[MAXN + 1];

static void gen(int r, int last, int m) {
    if (r == g_n) {
        Key k; encode(g_seq, m, k);
        map_add(*g_out, k, g_val);
        return;
    }
    if (g_cont[r]) {
        const int s = g_cont[r];
        if (s > last) return;                                   // column must weakly decrease downwards
        g_seq[m] = { s, g_cphase[r] };
        gen(r + s, s, m + 1);
        return;
    }
    for (int t = 1; t <= last; t++) {
        if (r + t > g_n || g_col + t > g_n) break;              // fits vertically / horizontally
        const int rr = r + t - 1;                               // newly added row
        if (g_controw[rr]) break;                               // would overlap a continuing square
        if (g_left[rr] && g_left[rr] < t) break;                // left neighbours must be >= t
        bool ok = true;                                         // (rows r..rr-1 were checked for t-1 >= ...)
        for (int x = r; x <= rr; x++) if (g_left[x] && g_left[x] < t) { ok = false; break; }
        if (!ok) break;
        g_seq[m] = { t, 0 };
        gen(r + t, t, m + 1);
    }
}

static std::string compute_term(int n) {
    g_n = n;
    g_overflow = false;
    Map cur, nxt;
    map_alloc(cur, 1024);
    map_alloc(nxt, 1024);
    time_t t0 = std::time(nullptr);
    // column 0
    for (int r = 0; r <= n; r++) { g_cont[r] = 0; g_controw[r] = false; g_left[r] = 0; }
    g_col = 0; g_out = &cur; g_val = 1;
    gen(0, n, 0);
    size_t peak = cur.cnt, total = cur.cnt;
    Sq q[MAXN + 1];
    for (int col = 1; col < n; col++) {
        map_clear(nxt);
        g_col = col; g_out = &nxt;
        for (size_t h = 0; h < cur.cap; h++) {
            if (cur.keys[h].w[0] == EMPTY0) continue;
            const int m = decode(cur.keys[h], n, q);
            for (int r = 0; r <= n; r++) { g_cont[r] = 0; g_controw[r] = false; }
            int r = 0;
            for (int i = 0; i < m; i++) {
                for (int x = r; x < r + q[i].s; x++) g_left[x] = q[i].s;
                if (q[i].p < q[i].s - 1) {
                    g_cont[r] = q[i].s; g_cphase[r] = q[i].p + 1;
                    for (int x = r; x < r + q[i].s; x++) g_controw[x] = true;
                }
                r += q[i].s;
            }
            g_val = cur.vals[h];
            gen(0, n, 0);
        }
        std::swap(cur, nxt);
        if (g_overflow) die("overflow of 128-bit values; nothing written");
        if (cur.cnt > peak) peak = cur.cnt;
        total += cur.cnt;
    }
    // complete: every square ends at the right edge
    u128 res = 0;
    for (size_t h = 0; h < cur.cap; h++) {
        if (cur.keys[h].w[0] == EMPTY0) continue;
        const int m = decode(cur.keys[h], n, q);
        bool done = true;
        for (int i = 0; i < m; i++) if (q[i].p != q[i].s - 1) { done = false; break; }
        if (!done) continue;
        u128 t = res + cur.vals[h];
        if (t < res) die("overflow of 128-bit values; nothing written");
        res = t;
    }
    map_free(cur); map_free(nxt);
    std::fprintf(stderr, "402607_02: n=%d: %zu column states in all, at most %zu per column, %lds\n",
                 n, total, peak, (long)(std::time(nullptr) - t0));
    return u128_to_dec(res);
}

// ---------------- arguments and files ----------------
static void usage(FILE *f) {
    std::fprintf(f,
        "usage: 402607_02 N\n"
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
        std::fprintf(stderr, "402607_02: N must satisfy 1 <= N <= %d\n", MAXN);
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
            std::fprintf(stderr, "402607_02: note: ignoring incomplete last line of %s\n", OUTFILE);
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
        std::fprintf(stderr, "402607_02: note: keeping saved lines beyond N=%d (not re-verified)\n", N);

    for (int n = 1; n <= N; n++) {
        std::string v = compute_term(n);
        if ((size_t)n <= vals.size()) {
            if (vals[(size_t)n - 1] != v) {
                std::fprintf(stderr, "402607_02: saved a(%d) = %s but computed %s; file left unchanged\n",
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
