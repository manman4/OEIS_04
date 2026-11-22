// 401435_01.cpp  --  b-file for OEIS A401435
//
// a(n) = number of ways to tile an n X n square with rectangles of integer side
//        lengths so that the widths weakly decrease from left to right along
//        every row and the heights weakly decrease from bottom to top along
//        every column (equivalently: every rectangle is at least as wide as each
//        rectangle immediately to its right and at least as high as each
//        rectangle immediately above it).
//        1, 8, 101, 4495, 301564, ...
//
// Usage:  ./401435_01 N        computes a(1..N); after each n the b-file
//                              b401435_01.txt ("n a(n)") is rewritten atomically
//         ./401435_01 --help
// Do not redirect stdout or stderr to the b-file. The shell can truncate a
// file before this program starts. Incomplete saved lines are rejected.
//
// ---------------------------------------------------------------------------
// We count the mirror images in the horizontal midline: tilings in which the
// widths weakly decrease from left to right along every row and the heights
// weakly decrease from top to bottom along every column (same number).
//
// Column transfer.  Sweep the columns c = 0..n-1 from left to right.  The
// rectangles meeting column c, read from top to bottom, have weakly decreasing
// heights (they are vertically adjacent in this column; their widths are not
// restricted), and their heights add up to n; for each we record its width w,
// its height h and its phase p (= c minus its leftmost column, 0 <= p <= w-1).
// This sequence is the state of column c.
// Column c -> c+1: every rectangle with p < w-1 continues as (w,h,p+1) in the
// same rows; the other rows are filled, from top to bottom, by new rectangles
// (w',h',0) such that
//    - each lies inside one block of free rows and fits: c+1+w' <= n;
//    - the heights in the new column still weakly decrease from top to
//      bottom (continuing rectangles included);
//    - every rectangle of column c in its rows has width >= w' (these are
//      exactly the horizontal adjacencies between different rectangles; a
//      continuing rectangle is its own left neighbour).
// Column 0 consists of new rectangles only.  A tiling is complete iff after
// column n-1 every rectangle has p = w-1.  Every tiling gives exactly one
// admissible sequence of column states and conversely, so a(n) is the number
// of these sequences.
// Checked: n = 1..5 agree with a brute force that builds every tiling and
// tests the condition; n = 1..6 agree (values and numbers of states) with an
// independent Python version of the column transfer.
//
// Values: unsigned 128-bit integers; every addition is checked for a carry out
// of 128 bits. On overflow the current term is not saved. The input limit
// is a key encoding limit, not a time, memory, or count bound.
// Keys: every rectangle is stored as w, h, p with 4 bits each, top to bottom
// (the heights add up to n, so the sequence is self-delimiting; at most
// 15 rectangles for n <= 15: 180 bits, 3 words).
// ---------------------------------------------------------------------------
//
// Build:  g++ -O3 -march=native -std=c++17 -Wall -Wextra -Wpedantic -o 401435_01 401435_01.cpp
//         (option: -DMAXN=n  largest allowed N, default 15, at most 15)

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
#ifdef __APPLE__
#include <copyfile.h>
#endif

#ifndef MAXN
#define MAXN 15
#endif
static constexpr int FORMAT_MAX_N = 15;
static_assert(MAXN >= 1 && MAXN <= FORMAT_MAX_N, "MAXN must be in 1..15 (4-bit fields, 3 key words)");

__extension__ typedef unsigned __int128 u128;

static const char *OUTFILE = "b401435_01.txt";
static const char *LOCKFILE = "b401435_01.txt.lock";
// Keep longer valid files even when compiled with a smaller MAXN.
static constexpr char MAX_SAVED_VALUE[] = "340282366920938463463374607431768211455";
static constexpr size_t MAX_SAVED_BYTES =
    FORMAT_MAX_N * (2 + 1 + (sizeof MAX_SAVED_VALUE - 1) + 1);
static const int KW = 3;           // key words (15 * 12 = 180 <= 192 bits)

[[noreturn]] static void die(const char *msg) {
    std::fprintf(stderr, "401435_01: %s\n", msg);
    std::exit(1);
}
[[noreturn]] static void die_errno(const char *msg) {
    std::fprintf(stderr, "401435_01: %s: %s\n", msg, std::strerror(errno));
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
static constexpr u128 MAX_COUNT = ~u128{0};

static u128 add_counts(u128 a, u128 b) {
    if (b > MAX_COUNT - a) die("128-bit count overflow; current term not saved");
    return a + b;
}
static const uint64_t EMPTY0 = ~0ULL;   // word 0 of a real key is never all ones: its low 12 bits hold
                                        // w, h, p of the first rectangle, and p <= w-1 <= 14 < 15
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
            m.vals[h] = add_counts(m.vals[h], v);
            return;
        }
        if (++h == m.cap) h = 0;
    }
}

// ---------------- column states ----------------
struct Rc { int w, h, p; };
static inline void put_bits(Key &k, int b, uint64_t v) {      // 12-bit field at bit b
    const int w = b / 64, sh = b % 64;
    k.w[w] |= v << sh;
    if (sh > 52) k.w[w + 1] |= v >> (64 - sh);
}
static inline uint64_t get_bits(const Key &k, int b) {
    const int w = b / 64, sh = b % 64;
    uint64_t v = k.w[w] >> sh;
    if (sh > 52) v |= k.w[w + 1] << (64 - sh);
    return v & 4095;
}
static inline void encode(const Rc *q, int m, Key &k) {
    std::memset(k.w, 0, sizeof k.w);
    for (int i = 0; i < m; i++)
        put_bits(k, 12 * i, (uint64_t)q[i].w | ((uint64_t)q[i].h << 4) | ((uint64_t)q[i].p << 8));
}
static inline int decode(const Key &k, int n, Rc *q) {
    int m = 0, rows = 0;
    while (rows < n) {
        const uint64_t f = get_bits(k, 12 * m);
        q[m].w = (int)(f & 15); q[m].h = (int)((f >> 4) & 15); q[m].p = (int)(f >> 8);
        if (q[m].w < 1 || q[m].h < 1 || q[m].p >= q[m].w) die("internal: bad column state");
        rows += q[m].h; m++;
    }
    if (rows != n) die("internal: bad column state");
    return m;
}

// generation of the next column
static int g_n, g_col;
static int g_contw[MAXN + 1], g_conth[MAXN + 1], g_contp[MAXN + 1];   // continuing rectangle starting at row r (w = 0: none)
static bool g_controw[MAXN + 1];
static int g_leftw[MAXN + 1];                                         // width of the rectangle of the previous column in row r
static u128 g_val;
static Rc g_seq[MAXN + 1];

static void gen(Map &out, int r, int lh, int m) {
    if (r == g_n) {
        Key k; encode(g_seq, m, k);
        map_add(out, k, g_val);
        return;
    }
    if (g_contw[r]) {
        const int h = g_conth[r];
        if (h > lh) return;                                 // heights weakly decrease downwards
        g_seq[m] = { g_contw[r], h, g_contp[r] };
        gen(out, r + h, h, m + 1);
        return;
    }
    int minw = MAXN + 1;                                    // minimum width of the left neighbours over rows r..r+h-1
    for (int h = 1; h <= lh; h++) {
        const int rr = r + h - 1;
        if (rr >= g_n || g_controw[rr]) break;              // fits vertically, no overlap with continuing ones
        if (g_col > 0 && g_leftw[rr] < minw) minw = g_leftw[rr];
        int wmax = g_n - g_col;                             // fits horizontally
        if (g_col > 0 && minw < wmax) wmax = minw;          // left neighbours at least as wide
        for (int w = 1; w <= wmax; w++) {
            g_seq[m] = { w, h, 0 };
            gen(out, r + h, h, m + 1);
        }
    }
}

static std::string compute_term(int n) {
    g_n = n;
    Map cur, nxt;
    map_alloc(cur, 1024);
    map_alloc(nxt, 1024);
    time_t t0 = std::time(nullptr);
    for (int r = 0; r <= n; r++) { g_contw[r] = 0; g_controw[r] = false; g_leftw[r] = 0; }
    g_col = 0; g_val = 1;
    gen(cur, 0, n, 0);
    size_t peak = cur.cnt, total = cur.cnt;
    Rc q[MAXN + 1];
    for (int col = 1; col < n; col++) {
        map_clear(nxt);
        g_col = col;
        for (size_t hh = 0; hh < cur.cap; hh++) {
            if (cur.keys[hh].w[0] == EMPTY0) continue;
            const int m = decode(cur.keys[hh], n, q);
            for (int r = 0; r <= n; r++) { g_contw[r] = 0; g_controw[r] = false; }
            int r = 0;
            for (int i = 0; i < m; i++) {
                for (int x = r; x < r + q[i].h; x++) g_leftw[x] = q[i].w;
                if (q[i].p < q[i].w - 1) {
                    g_contw[r] = q[i].w; g_conth[r] = q[i].h; g_contp[r] = q[i].p + 1;
                    for (int x = r; x < r + q[i].h; x++) g_controw[x] = true;
                }
                r += q[i].h;
            }
            g_val = cur.vals[hh];
            gen(nxt, 0, n, 0);
        }
        std::swap(cur, nxt);
        if (cur.cnt > peak) peak = cur.cnt;
        total += cur.cnt;
    }
    u128 res = 0;
    for (size_t hh = 0; hh < cur.cap; hh++) {
        if (cur.keys[hh].w[0] == EMPTY0) continue;
        const int m = decode(cur.keys[hh], n, q);
        bool done = true;
        for (int i = 0; i < m; i++) if (q[i].p != q[i].w - 1) { done = false; break; }
        if (!done) continue;
        res = add_counts(res, cur.vals[hh]);
    }
    map_free(cur); map_free(nxt);
    std::fprintf(stderr, "401435_01: n=%d: %zu column states in all, at most %zu per column, %lds\n",
                 n, total, peak, (long)(std::time(nullptr) - t0));
    return u128_to_dec(res);
}

// ---------------- arguments and files ----------------
static void usage(FILE *f) {
    std::fprintf(f,
        "usage: 401435_01 N\n"
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
        std::fprintf(stderr, "401435_01: N must satisfy 1 <= N <= %d\n", MAXN);
        std::exit(1);
    }
    return (int)v;
}
// Compare device and inode so aliases via links are detected too.
static bool stream_is_file(int fd, const struct stat &file) {
    struct stat stream;
    return fstat(fd, &stream) == 0 &&
        stream.st_dev == file.st_dev && stream.st_ino == file.st_ino;
}

static void reject_output_alias(const struct stat &file) {
    const bool out = stream_is_file(STDOUT_FILENO, file);
    const bool err = stream_is_file(STDERR_FILENO, file);
    if (!out && !err) return;
    if (!err) std::fputs("401435_01: stdout refers to the b-file\n", stderr);
    else if (!out) std::fputs("401435_01: stderr refers to the b-file\n", stdout);
    std::exit(1);
}

static void open_lock() {
    int fd = open(LOCKFILE, O_RDWR | O_CREAT | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK, 0644);
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
    int fd = open(OUTFILE, O_RDONLY | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK);
    if (fd < 0) {
        if (errno == ENOENT) return vals;
        die_errno("cannot open saved file (symlink?)");
    }
    struct stat st;
    if (fstat(fd, &st) != 0) die_errno("fstat saved file");
    reject_output_alias(st);
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
        if (nl == std::string::npos)
            die("saved file: incomplete last line (file left unchanged)");
        std::string line = data.substr(pos, nl - pos);
        pos = nl + 1;
        size_t sp = line.find(' ');
        if (sp == std::string::npos || sp == 0 || sp + 1 >= line.size())
            die("saved file: malformed line (file left unchanged)");
        std::string ns = line.substr(0, sp), vs = line.substr(sp + 1);
        for (char ch : ns) if (ch < '0' || ch > '9') die("saved file: bad index (file left unchanged)");
        for (char ch : vs) if (ch < '0' || ch > '9') die("saved file: bad value (file left unchanged)");
        if (expect > FORMAT_MAX_N || ns != std::to_string(expect))
            die("saved file: indices must be 1,2,3,... (file left unchanged)");
        constexpr size_t max_digits = sizeof MAX_SAVED_VALUE - 1;
        if (vs[0] == '0' || vs.size() > max_digits ||
            (vs.size() == max_digits && vs > MAX_SAVED_VALUE))
            die("saved file: expected a positive 128-bit value without leading zeros");
        vals.push_back(vs);
        expect++;
    }
    return vals;
}
static void write_all(const std::vector<std::string> &vals) {
    struct stat st = {};
    const int old_fd = open(OUTFILE, O_RDONLY | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK);
    if (old_fd >= 0) {
        if (fstat(old_fd, &st) != 0) die_errno("fstat result file");
        reject_output_alias(st);
        if (!S_ISREG(st.st_mode) || st.st_nlink != 1)
            die("refusing to replace result file: not a plain regular file");
    } else if (errno != ENOENT) {
        die_errno("open result file");
    }
    std::string tmpl = std::string(OUTFILE) + ".tmpXXXXXX";
    std::vector<char> name(tmpl.begin(), tmpl.end());
    name.push_back('\0');
    int fd = mkstemp(name.data());
    if (fd < 0) die_errno("mkstemp");
    FILE *f = fdopen(fd, "w");
    if (!f) { close(fd); unlink(name.data()); die_errno("fdopen"); }
    for (size_t i = 0; i < vals.size(); i++)
        if (std::fprintf(f, "%zu %s\n", i + 1, vals[i].c_str()) < 0) { std::fclose(f); unlink(name.data()); die("write to temp file failed"); }
    if (std::fflush(f) != 0) { std::fclose(f); unlink(name.data()); die_errno("fflush temp"); }
    const auto fail_temp = [&](const char *message) {
        const int saved_errno = errno;
        std::fclose(f);
        unlink(name.data());
        errno = saved_errno;
        die_errno(message);
    };
    const mode_t mode = old_fd >= 0 ? st.st_mode & 0777 : 0644;
    if (fchmod(fd, mode) != 0) fail_temp("preserve result permissions");
#ifdef __APPLE__
    if (old_fd >= 0 && fcopyfile(old_fd, fd, nullptr, COPYFILE_ACL) != 0)
        fail_temp("preserve result ACL");
#endif
    if (old_fd >= 0 && close(old_fd) != 0) fail_temp("close old result file");
    if (fsync(fileno(f)) != 0) { std::fclose(f); unlink(name.data()); die_errno("fsync temp"); }
    if (std::fclose(f) != 0) { unlink(name.data()); die_errno("fclose temp"); }
    if (rename(name.data(), OUTFILE) != 0) { unlink(name.data()); die_errno("rename"); }
    int dfd = open(".", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (dfd < 0) die_errno("open directory");
    if (fsync(dfd) != 0) die_errno("fsync directory");
    if (close(dfd) != 0) die_errno("close directory");
}

int main(int argc, char **argv) {
    struct stat saved;
    if (stat(OUTFILE, &saved) == 0) reject_output_alias(saved);
    if (argc == 2 && (!std::strcmp(argv[1], "--help") || !std::strcmp(argv[1], "-h"))) { usage(stdout); return 0; }
    if (argc != 2) { usage(stderr); return 1; }
    const int N = parse_n(argv[1]);

    open_lock();
    std::vector<std::string> vals = read_saved();
    if (vals.size() > (size_t)N)
        std::fprintf(stderr, "401435_01: note: keeping saved lines beyond N=%d (not re-verified)\n", N);

    for (int n = 1; n <= N; n++) {
        std::string v = compute_term(n);
        if ((size_t)n <= vals.size()) {
            if (vals[(size_t)n - 1] != v) {
                std::fprintf(stderr, "401435_01: saved a(%d) = %s but computed %s; file left unchanged\n",
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
