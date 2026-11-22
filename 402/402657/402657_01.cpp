// 402657_01.cpp  --  b-file for OEIS A402657
//
// a(n) = number of ways to tile an n X n square with rectangles of integer side
//        lengths so that both the widths and the heights weakly decrease from
//        left to right along every row and from bottom to top along every
//        column (equivalently: every rectangle is at least as wide and at least
//        as high as each rectangle immediately to its right and each rectangle
//        immediately above it).
//        1, 6, 30, 294, 2263, 31579, 333719, 5560499, 79559303, ...
//
// Usage:  ./402657_01 N        computes a(1..N); after each n the b-file
//                              b402657_01.txt ("n a(n)") is rewritten atomically
//         ./402657_01 --help
// Incomplete saved lines are rejected. Existing permissions and macOS ACLs
// are preserved. Do not redirect stdout or stderr to the b-file.
//
// ---------------------------------------------------------------------------
// We count the mirror images in the horizontal midline: tilings in which the
// widths and the heights weakly decrease from left to right along every row
// and from top to bottom along every column (same number).
//
// Column transfer.  Sweep the columns c = 0..n-1 from left to right.  The
// rectangles meeting column c, read from top to bottom, have weakly decreasing
// widths and weakly decreasing heights (they are vertically adjacent in this
// column), and their heights add up to n; for each we record its width w, its
// height h and its phase p (= c minus its leftmost column, 0 <= p <= w-1).
// This sequence is the state of column c.
// Column c -> c+1: every rectangle with p < w-1 continues as (w,h,p+1) in the
// same rows; the other rows are filled, from top to bottom, by new rectangles
// (w',h',0) such that
//    - each lies inside one block of free rows and fits: c+1+w' <= n;
//    - the whole new column still has weakly decreasing widths and heights
//      from top to bottom (continuing rectangles included);
//    - every rectangle of column c in its rows has width >= w' and height
//      >= h' (these are exactly the horizontal adjacencies between different
//      rectangles; a continuing rectangle is its own left neighbour).
// Column 0 consists of new rectangles only.  A tiling is complete iff after
// column n-1 every rectangle has p = w-1.  Every tiling gives exactly one
// admissible sequence of column states and conversely, so a(n) is the number
// of these sequences.
// Checked: n = 1..4 agree with unrestricted enumeration followed by testing
// the inequalities; n = 1..7 agree with independent skyline and row transfers.
// For squares only, the same model gives A402607.
//
// Values: unsigned 64-bit integers; every addition is checked for a carry out
// of 64 bits. On overflow the unfinished term is not saved; earlier saved
// terms remain. The input limit is an encoding limit, not a proof that all
// intermediate counts fit in 64 bits or a runtime/memory guarantee.
// Keys: the unit squares are at the bottom of a column (they are the smallest
// in both dimensions), so only their number is stored (4 bits); every other
// rectangle is stored as w, h, p with 4 bits each, top to bottom (at most
// 15 of them for n <= 15: 4 + 15*12 = 184 bits, 3 words).
// ---------------------------------------------------------------------------
//
// Build:  g++ -O3 -march=native -std=c++17 -Wall -Wextra -Wpedantic -o 402657_01 402657_01.cpp
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
static_assert(MAXN >= 1 && MAXN <= 15, "MAXN must be in 1..15 (4-bit fields, 3 key words)");

__extension__ typedef unsigned __int128 u128;

static const char *OUTFILE = "b402657_01.txt";
static const char *LOCKFILE = "b402657_01.txt.lock";
static const size_t MAX_SAVED_BYTES = 16u << 20;
static const size_t MAX_DIGITS = 2000;
static const int KW = 3;           // key words (4 + 15 * 12 = 184 <= 192 bits)

[[noreturn]] static void die(const char *msg) {
    std::fprintf(stderr, "402657_01: %s\n", msg);
    std::exit(1);
}
[[noreturn]] static void die_errno(const char *msg) {
    std::fprintf(stderr, "402657_01: %s: %s\n", msg, std::strerror(errno));
    std::exit(1);
}

static std::string u128_to_dec(u128 x) {
    if (x == 0) return "0";
    std::string s;
    while (x) { s.push_back((char)('0' + (int)(x % 10))); x /= 10; }
    std::reverse(s.begin(), s.end());
    return s;
}

// ---------------- hash map: KW-word key -> uint64 ----------------
struct Key { uint64_t w[KW]; };
static bool g_overflow = false;
static const uint64_t EMPTY0 = ~0ULL;   // word 0 of a real key is never all ones: its low 4 bits hold the
                                        // number of unit squares, which is <= 15, and 15 unit squares
                                        // leave all other bits 0
struct Map {
    size_t cap = 0, cnt = 0;
    Key *keys = nullptr;
    uint64_t *vals = nullptr;
};
static void map_alloc(Map &m, size_t cap) {
    if (cap < 64) cap = 64;
    if (cap > SIZE_MAX / (sizeof(Key) + sizeof(uint64_t))) die("hash table too large");
    m.cap = cap; m.cnt = 0;
    m.keys = static_cast<Key *>(std::malloc(cap * sizeof(Key)));
    m.vals = static_cast<uint64_t *>(std::malloc(cap * sizeof(uint64_t)));
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
static void map_add(Map &m, const Key &key, uint64_t v);
static void map_resize(Map &m, size_t newcap) {
    Map n;
    map_alloc(n, newcap);
    for (size_t i = 0; i < m.cap; i++) if (m.keys[i].w[0] != EMPTY0) map_add(n, m.keys[i], m.vals[i]);
    map_free(m);
    m = n;
}
static void map_add(Map &m, const Key &key, uint64_t v) {
    if ((m.cnt + 1) * 10 > m.cap * 7) map_resize(m, m.cap * 2);       // load <= 0.7
    size_t h = slot0(key, m.cap);
    for (;;) {
        Key &k = m.keys[h];
        if (k.w[0] == EMPTY0) { k = key; m.vals[h] = v; m.cnt++; return; }
        if (std::memcmp(k.w, key.w, sizeof k.w) == 0) {
            uint64_t s = m.vals[h] + v;
            if (s < v) g_overflow = true;      // carry out of 64 bits
            m.vals[h] = s;
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
    int units = 0, i = 0;
    for (; i < m && !(q[i].w == 1 && q[i].h == 1); i++)
        put_bits(k, 4 + 12 * i, (uint64_t)q[i].w | ((uint64_t)q[i].h << 4) | ((uint64_t)q[i].p << 8));
    for (; i < m; i++) { if (q[i].w != 1 || q[i].h != 1) die("internal: unit squares not at the bottom"); units++; }
    k.w[0] |= (uint64_t)units;
}
static inline int decode(const Key &k, int n, Rc *q) {
    const int units = (int)(k.w[0] & 15);
    int m = 0, rows = 0;
    while (rows < n - units) {
        const uint64_t f = get_bits(k, 4 + 12 * m);
        q[m].w = (int)(f & 15); q[m].h = (int)((f >> 4) & 15); q[m].p = (int)(f >> 8);
        if (q[m].w < 1 || q[m].h < 1 || q[m].p >= q[m].w) die("internal: bad column state");
        rows += q[m].h; m++;
    }
    for (int i = 0; i < units; i++) { q[m] = { 1, 1, 0 }; m++; rows++; }
    if (rows != n) die("internal: bad column state");
    return m;
}

// generation of the next column
static int g_n, g_col;
static int g_contw[MAXN + 1], g_conth[MAXN + 1], g_contp[MAXN + 1];   // continuing rectangle starting at row r (w = 0: none)
static bool g_controw[MAXN + 1];
static int g_leftw[MAXN + 1], g_lefth[MAXN + 1];                      // rectangle of the previous column in row r (0: none)
static Map *g_out;
static uint64_t g_val;
static Rc g_seq[MAXN + 1];

static void gen(int r, int lw, int lh, int m) {
    if (r == g_n) {
        Key k; encode(g_seq, m, k);
        map_add(*g_out, k, g_val);
        return;
    }
    if (g_contw[r]) {
        const int w = g_contw[r], h = g_conth[r];
        if (w > lw || h > lh) return;                       // column must weakly decrease downwards
        g_seq[m] = { w, h, g_contp[r] };
        gen(r + h, w, h, m + 1);
        return;
    }
    int minw = MAXN + 1, minh = MAXN + 1;                   // minima of the left neighbours over rows r..r+h-1
    for (int h = 1; h <= lh; h++) {
        const int rr = r + h - 1;
        if (rr >= g_n || g_controw[rr]) break;              // fits vertically, no overlap with continuing ones
        if (g_col > 0) {
            if (g_leftw[rr] < minw) minw = g_leftw[rr];
            if (g_lefth[rr] < minh) minh = g_lefth[rr];
            if (minh < h) break;                            // left neighbours too low (also for larger h)
        }
        int wmax = lw;
        if (g_n - g_col < wmax) wmax = g_n - g_col;         // fits horizontally
        if (g_col > 0 && minw < wmax) wmax = minw;          // left neighbours at least as wide
        for (int w = 1; w <= wmax; w++) {
            g_seq[m] = { w, h, 0 };
            gen(r + h, w, h, m + 1);
        }
    }
}

static std::string compute_term(int n) {
    g_n = n;
    g_overflow = false;
    Map cur, nxt;
    map_alloc(cur, 1024);
    map_alloc(nxt, 1024);
    time_t t0 = std::time(nullptr);
    for (int r = 0; r <= n; r++) { g_contw[r] = 0; g_controw[r] = false; g_leftw[r] = 0; g_lefth[r] = 0; }
    g_col = 0; g_out = &cur; g_val = 1;
    gen(0, n, n, 0);
    size_t peak = cur.cnt, total = cur.cnt;
    Rc q[MAXN + 1];
    for (int col = 1; col < n; col++) {
        map_clear(nxt);
        g_col = col; g_out = &nxt;
        for (size_t hh = 0; hh < cur.cap; hh++) {
            if (cur.keys[hh].w[0] == EMPTY0) continue;
            const int m = decode(cur.keys[hh], n, q);
            for (int r = 0; r <= n; r++) { g_contw[r] = 0; g_controw[r] = false; }
            int r = 0;
            for (int i = 0; i < m; i++) {
                for (int x = r; x < r + q[i].h; x++) { g_leftw[x] = q[i].w; g_lefth[x] = q[i].h; }
                if (q[i].p < q[i].w - 1) {
                    g_contw[r] = q[i].w; g_conth[r] = q[i].h; g_contp[r] = q[i].p + 1;
                    for (int x = r; x < r + q[i].h; x++) g_controw[x] = true;
                }
                r += q[i].h;
            }
            g_val = cur.vals[hh];
            gen(0, n, n, 0);
        }
        std::swap(cur, nxt);
        if (g_overflow) die("overflow of 64-bit values; nothing written");
        if (cur.cnt > peak) peak = cur.cnt;
        total += cur.cnt;
    }
    uint64_t res = 0;
    for (size_t hh = 0; hh < cur.cap; hh++) {
        if (cur.keys[hh].w[0] == EMPTY0) continue;
        const int m = decode(cur.keys[hh], n, q);
        bool done = true;
        for (int i = 0; i < m; i++) if (q[i].p != q[i].w - 1) { done = false; break; }
        if (!done) continue;
        uint64_t t = res + cur.vals[hh];
        if (t < res) die("overflow of 64-bit values; nothing written");
        res = t;
    }
    g_out = nullptr;
    map_free(cur); map_free(nxt);
    std::fprintf(stderr, "402657_01: n=%d: %zu column states in all, at most %zu per column, %lds\n",
                 n, total, peak, (long)(std::time(nullptr) - t0));
    return u128_to_dec((u128)res);
}

// ---------------- arguments and files ----------------
static void usage(FILE *f) {
    std::fprintf(f,
        "usage: 402657_01 N\n"
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
        std::fprintf(stderr, "402657_01: N must satisfy 1 <= N <= %d\n", MAXN);
        std::exit(1);
    }
    return (int)v;
}
// Reject aliases before emitting any message to either standard stream.
static bool output_conflict(const struct stat &saved) {
    struct stat out, err;
    const bool out_alias = fstat(STDOUT_FILENO, &out) == 0 &&
        out.st_dev == saved.st_dev && out.st_ino == saved.st_ino;
    const bool err_alias = fstat(STDERR_FILENO, &err) == 0 &&
        err.st_dev == saved.st_dev && err.st_ino == saved.st_ino;
    if (!out_alias && !err_alias) return false;
    if (!err_alias)
        std::fputs("402657_01: stdout refers to the b-file; refusing to run\n", stderr);
    else if (!out_alias)
        std::fputs("402657_01: stderr refers to the b-file; refusing to run\n", stdout);
    return true;
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
    if (output_conflict(st)) std::exit(1);
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
    // Retain an open descriptor for metadata; never follow a symlink or block
    // on a FIFO. All cooperating writers hold the stable lock for the run.
    struct stat st = {};
    int old_fd = open(OUTFILE, O_RDONLY | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK);
    if (old_fd >= 0) {
        if (fstat(old_fd, &st) != 0) die_errno("fstat result file");
        if (output_conflict(st)) std::exit(1);
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
    const mode_t mode = old_fd >= 0 ? st.st_mode & 0777 : 0644;
    if (fchmod(fd, mode) != 0) { unlink(name.data()); die_errno("fchmod"); }
    FILE *f = fdopen(fd, "w");
    if (!f) { close(fd); unlink(name.data()); die_errno("fdopen"); }
    for (size_t i = 0; i < vals.size(); i++)
        if (std::fprintf(f, "%zu %s\n", i + 1, vals[i].c_str()) < 0) { std::fclose(f); unlink(name.data()); die("write to temp file failed"); }
    if (std::fflush(f) != 0) { std::fclose(f); unlink(name.data()); die_errno("fflush temp"); }
#ifdef __APPLE__
    // Copy ACLs after writing, as the old ACL may deny writes to the new file.
    if (old_fd >= 0 && fcopyfile(old_fd, fd, nullptr, COPYFILE_ACL) != 0) {
        std::fclose(f); unlink(name.data()); die_errno("preserve result ACL");
    }
#endif
    if (old_fd >= 0 && close(old_fd) != 0) {
        std::fclose(f); unlink(name.data()); die_errno("close old result file");
    }
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
    if (stat(OUTFILE, &saved) == 0 && output_conflict(saved)) return 1;
    if (argc == 2 && (!std::strcmp(argv[1], "--help") || !std::strcmp(argv[1], "-h"))) { usage(stdout); return 0; }
    if (argc != 2) { usage(stderr); return 1; }
    const int N = parse_n(argv[1]);

    open_lock();
    std::vector<std::string> vals = read_saved();
    if (vals.size() > (size_t)N)
        std::fprintf(stderr, "402657_01: note: keeping saved lines beyond N=%d (not re-verified)\n", N);

    for (int n = 1; n <= N; n++) {
        std::string v = compute_term(n);
        if ((size_t)n <= vals.size()) {
            if (vals[(size_t)n - 1] != v) {
                std::fprintf(stderr, "402657_01: saved a(%d) = %s but computed %s; file left unchanged\n",
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
