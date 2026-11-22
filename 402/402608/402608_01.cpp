// 402608_01.cpp  --  b-file for OEIS A402608 (column-transfer version)
//
// a(n) = number of ways to tile a size n staircase polyomino with squares of
//        integer side lengths so that the side lengths weakly decrease from
//        left to right along every row and from bottom to top along every
//        column (equivalently: no square has a smaller square immediately to
//        its left or immediately below it).
//        (A size-n staircase polyomino consists of n left-aligned rows of
//        lengths 1, 2, ..., n, the shortest row on top.)
//        1, 1, 2, 2, 6, 9, 22, 38, 119, 215, 720, 1446, 4489, ...
//
// Usage:  ./402608_01 N        computes a(1..N); after each n the b-file
//                              b402608_01.txt ("n a(n)") is rewritten atomically
//         ./402608_01 --help
//
// ---------------------------------------------------------------------------
// We count the mirror images in the horizontal midline: the staircase with
// rows of lengths n, n-1, ..., 1 from the top (left aligned), tiled so that the
// side lengths weakly decrease from left to right along every row and from top
// to bottom along every column (same number).  Column c (c = 0..n-1) then
// consists of the rows 0..n-1-c: all columns start at the top row.
//
// Column transfer.  Sweep the columns from left to right.  The squares meeting
// column c, read from top to bottom, have weakly decreasing sizes (column
// condition) adding up to n-c; for each we record its size s and its phase p
// (= c minus its leftmost column, 0 <= p <= s-1).  This is the state of
// column c.  A square with top-left cell (r,c) and side t lies in the
// staircase iff its bottom-right cell (r+t-1, c+t-1) does, i.e.
//      r + 2t <= n - c + 1;
// then it automatically fits in every column it meets.
// Column c -> c+1 (which has n-c-1 rows): every square with p < s-1 continues
// as (s,p+1) in the same rows; the other rows 0..n-c-2 are filled, from top
// to bottom, by new squares (t,0) such that
//    - each lies inside one block of free rows and satisfies the fit test
//      above (with c+1 in place of c);
//    - the whole new column still has weakly decreasing sizes from top to
//      bottom (continuing squares included);
//    - every square of column c in its rows has size >= t (row condition:
//      these are exactly the horizontal adjacencies between different squares;
//      a continuing square is its own left neighbour).
// Column 0 consists of new squares only.  After column n-1 (one row) every
// square has ended.  Every tiling gives exactly one admissible sequence of
// column states and conversely, so a(n) is the number of these sequences.
// Checked: n = 1..32 agree with the skyline version of this program (cells
// in row-major order, a different set of states); n = 1..16 agree with a brute
// force that builds every tiling and tests the condition.
//
// Values: unsigned 128-bit integers; every addition is checked for a carry out
// of 128 bits (the unfinished term is not saved).
// Keys: the squares of size 1 are at the bottom of a column (sizes decrease
// downwards), so only their number is stored (6 bits); every square of size
// s >= 2 is stored as the 11-bit code s(s-1)/2 + p, top to bottom.  A column
// of m rows has at most m/2 squares of size >= 2, so 6 words suffice for
// n <= 58.
// ---------------------------------------------------------------------------
//
// Build:  g++ -O3 -march=native -std=c++17 -Wall -Wextra -Wpedantic -o 402608_01 402608_01.cpp
//         (option: -DMAXN=n  largest allowed N, default 58, at most 58)

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
#define MAXN 58
#endif
static_assert(MAXN >= 1 && MAXN <= 58, "MAXN must be in 1..58 (codes < 2048, 6 key words)");

__extension__ typedef unsigned __int128 u128;

static const char *OUTFILE = "b402608_01.txt";
static const char *LOCKFILE = "b402608_01.txt.lock";
static const size_t MAX_SAVED_BYTES = 16u << 20;
static const size_t MAX_DIGITS = 2000;
static const int KW = 6;           // key words (6 + 29 * 11 = 325 <= 384 bits)

[[noreturn]] static void die(const char *msg) {
    std::fprintf(stderr, "402608_01: %s\n", msg);
    std::exit(1);
}
[[noreturn]] static void die_errno(const char *msg) {
    std::fprintf(stderr, "402608_01: %s: %s\n", msg, std::strerror(errno));
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
static const uint64_t EMPTY0 = ~0ULL;   // word 0 of a real key is never all ones: its low 6 bits hold the
                                        // number of size-1 squares, which is <= 58 < 63
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
// key: bits 0..5 = number of trailing squares of size 1; then 11 bits per square of size >= 2
static inline void encode(const Sq *q, int m, Key &k) {
    std::memset(k.w, 0, sizeof k.w);
    int ones = 0, i = 0;
    for (; i < m && q[i].s >= 2; i++) {
        const uint64_t code = (uint64_t)(q[i].s * (q[i].s - 1) / 2 + q[i].p);   // < 1711 for s <= 58
        const int b = 6 + 11 * i, w = b / 64, sh = b % 64;
        k.w[w] |= code << sh;
        if (sh > 53) k.w[w + 1] |= code >> (64 - sh);
    }
    for (; i < m; i++) { if (q[i].s != 1) die("internal: size-1 squares not at the bottom"); ones++; }
    k.w[0] |= (uint64_t)ones;
}
static inline int decode(const Key &k, int len, Sq *q) {
    const int ones = (int)(k.w[0] & 63);
    int m = 0, rows = 0;
    while (rows < len - ones) {
        const int b = 6 + 11 * m, w = b / 64, sh = b % 64;
        uint64_t code = k.w[w] >> sh;
        if (sh > 53) code |= k.w[w + 1] << (64 - sh);
        code &= 2047;
        int s = 2;
        while ((uint64_t)(s * (s + 1) / 2) <= code) s++;     // s(s-1)/2 <= code < s(s+1)/2
        q[m].s = s; q[m].p = (int)code - s * (s - 1) / 2;
        rows += s; m++;
    }
    for (int i = 0; i < ones; i++) { q[m].s = 1; q[m].p = 0; m++; rows++; }
    if (rows != len) die("internal: bad column state");
    return m;
}

// generation of the next column
static int g_n, g_col, g_len;              // g_col: column being built, g_len = n - g_col rows
static int g_cont[MAXN + 1];               // g_cont[r] = size of a continuing square starting at row r (0 if none)
static int g_cphase[MAXN + 1];
static bool g_controw[MAXN + 1];           // row covered by a continuing square
static int g_left[MAXN + 1];               // size of the square of the previous column in row r (0 for column 0)
static Map *g_out;
static u128 g_val;
static Sq g_seq[MAXN + 1];

static void gen(int r, int last, int m) {
    if (r == g_len) {
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
        if (r + t > g_len) break;                               // inside the column
        if (r + 2 * t > g_n - g_col + 1) break;                 // bottom-right cell inside the staircase
        const int rr = r + t - 1;                               // newly added row
        if (g_controw[rr]) break;                               // would overlap a continuing square
        bool ok = true;                                         // left neighbours must be >= t
        for (int x = r; x <= rr; x++) if (g_left[x] && g_left[x] < t) { ok = false; break; }
        if (!ok) break;                                         // (fails for every larger t as well)
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
    // column 0: n rows, new squares only
    for (int r = 0; r <= n; r++) { g_cont[r] = 0; g_controw[r] = false; g_left[r] = 0; }
    g_col = 0; g_len = n; g_out = &cur; g_val = 1;
    gen(0, n, 0);
    size_t peak = cur.cnt, total = cur.cnt;
    Sq q[MAXN + 1];
    for (int col = 1; col < n; col++) {
        map_clear(nxt);
        g_col = col; g_len = n - col; g_out = &nxt;
        for (size_t h = 0; h < cur.cap; h++) {
            if (cur.keys[h].w[0] == EMPTY0) continue;
            const int m = decode(cur.keys[h], n - col + 1, q);   // previous column has n-col+1 rows
            for (int r = 0; r <= n; r++) { g_cont[r] = 0; g_controw[r] = false; g_left[r] = 0; }
            int r = 0;
            bool bad = false;
            for (int i = 0; i < m; i++) {
                for (int x = r; x < r + q[i].s; x++) g_left[x] = q[i].s;
                if (q[i].p < q[i].s - 1) {
                    if (r + q[i].s > g_len) { bad = true; break; }      // cannot happen (fit test)
                    g_cont[r] = q[i].s; g_cphase[r] = q[i].p + 1;
                    for (int x = r; x < r + q[i].s; x++) g_controw[x] = true;
                }
                r += q[i].s;
            }
            if (bad) die("internal: continuing square leaves the staircase");
            g_val = cur.vals[h];
            gen(0, n, 0);
        }
        std::swap(cur, nxt);
        if (g_overflow) die("overflow of 128-bit values; nothing written");
        if (cur.cnt > peak) peak = cur.cnt;
        total += cur.cnt;
    }
    // last column (1 row): every square must have ended
    u128 res = 0;
    for (size_t h = 0; h < cur.cap; h++) {
        if (cur.keys[h].w[0] == EMPTY0) continue;
        const int m = decode(cur.keys[h], 1, q);
        bool done = true;
        for (int i = 0; i < m; i++) if (q[i].p != q[i].s - 1) { done = false; break; }
        if (!done) continue;
        u128 t = res + cur.vals[h];
        if (t < res) die("overflow of 128-bit values; nothing written");
        res = t;
    }
    g_out = nullptr;
    map_free(cur); map_free(nxt);
    std::fprintf(stderr, "402608_01: n=%d: %zu column states in all, at most %zu per column, %lds\n",
                 n, total, peak, (long)(std::time(nullptr) - t0));
    return u128_to_dec(res);
}

// ---------------- arguments and files ----------------
static void usage(FILE *f) {
    std::fprintf(f,
        "usage: 402608_01 N\n"
        "  computes a(1..N): monotone square tilings of a size n staircase\n"
        "  (left-aligned rows of lengths 1,2,...,n from top to bottom)\n"
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
        std::fprintf(stderr, "402608_01: N must satisfy 1 <= N <= %d\n", MAXN);
        std::exit(1);
    }
    return (int)v;
}
struct OutputFiles {
    struct stat output{};
    struct stat error{};
    bool have_output = false;
    bool have_error = false;
};

static bool same_file(const struct stat &a, const struct stat &b) {
    return a.st_dev == b.st_dev && a.st_ino == b.st_ino;
}

static void reject_redirected_output(const struct stat &target, const OutputFiles &streams) {
    bool out_alias = streams.have_output && same_file(target, streams.output);
    bool err_alias = streams.have_error && same_file(target, streams.error);
    if (!out_alias && !err_alias) return;
    // A diagnostic must not be written into the b-file either.
    if (!err_alias)
        std::fprintf(stderr, "402608_01: stdout is redirected to %s\n", OUTFILE);
    else if (!out_alias)
        std::fprintf(stdout, "402608_01: stderr is redirected to %s\n", OUTFILE);
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
static std::vector<std::string> read_saved(const OutputFiles &streams) {
    std::vector<std::string> vals;
    int fd = open(OUTFILE, O_RDONLY | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK);
    if (fd < 0) {
        if (errno == ENOENT) return vals;
        die_errno("cannot open saved file (symlink?)");
    }
    struct stat st;
    if (fstat(fd, &st) != 0) die_errno("fstat saved file");
    reject_redirected_output(st, streams);
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
        size_t end = nl == std::string::npos ? data.size() : nl;
        std::string line = data.substr(pos, end - pos);
        pos = nl == std::string::npos ? end : nl + 1;
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
static void write_all(const std::vector<std::string> &vals, const OutputFiles &streams) {
    // Keep the metadata source open until mode and ACL have been copied.
    int old_fd = open(OUTFILE, O_RDONLY | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK);
    struct stat old_stat{};
    if (old_fd >= 0) {
        if (fstat(old_fd, &old_stat) != 0) die_errno("fstat result file");
        reject_redirected_output(old_stat, streams);
        if (!S_ISREG(old_stat.st_mode) || old_stat.st_nlink != 1)
            die("refusing to replace result file: not a plain regular file");
    } else if (errno != ENOENT) {
        die_errno("opening result file metadata");
    }

    std::string tmpl = std::string(OUTFILE) + ".tmpXXXXXX";
    std::vector<char> name(tmpl.begin(), tmpl.end());
    name.push_back('\0');
    int fd = mkstemp(name.data());
    if (fd < 0) die_errno("mkstemp");
    FILE *f = fdopen(fd, "w");
    if (!f) { close(fd); unlink(name.data()); die_errno("fdopen"); }
    for (size_t i = 0; i < vals.size(); i++)
        if (std::fprintf(f, "%zu %s\n", i + 1, vals[i].c_str()) < 0) {
            std::fclose(f);
            unlink(name.data());
            die("write to temp file failed");
        }

    const char *failure = nullptr;
    if (std::fflush(f) != 0)
        failure = "fflush temp";
    if (!failure && old_fd >= 0 && fchmod(fd, old_stat.st_mode & 0777) != 0)
        failure = "preserving result file permissions";
#ifdef __APPLE__
    if (!failure && old_fd >= 0 && fcopyfile(old_fd, fd, nullptr, COPYFILE_ACL) != 0)
        failure = "preserving result file ACL";
#endif
    if (!failure && fsync(fd) != 0)
        failure = "fsync temp";
    int error = errno;
    if (old_fd >= 0 && close(old_fd) != 0 && !failure) {
        failure = "close metadata source";
        error = errno;
    }
    if (std::fclose(f) != 0 && !failure) {
        failure = "fclose temp";
        error = errno;
    }
    if (failure) {
        unlink(name.data());
        errno = error;
        die_errno(failure);
    }
    if (rename(name.data(), OUTFILE) != 0) {
        error = errno;
        unlink(name.data());
        errno = error;
        die_errno("rename");
    }
    int dfd = open(".", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (dfd < 0) die_errno("open directory");
    if (fsync(dfd) != 0) die_errno("fsync directory");
    if (close(dfd) != 0) die_errno("close directory");
}

int main(int argc, char **argv) {
    OutputFiles streams;
    streams.have_output = fstat(STDOUT_FILENO, &streams.output) == 0;
    streams.have_error = fstat(STDERR_FILENO, &streams.error) == 0;
    struct stat target;
    if (stat(OUTFILE, &target) == 0) reject_redirected_output(target, streams);

    if (argc == 2 && (!std::strcmp(argv[1], "--help") || !std::strcmp(argv[1], "-h"))) { usage(stdout); return 0; }
    if (argc != 2) { usage(stderr); return 1; }
    const int N = parse_n(argv[1]);

    open_lock();
    std::vector<std::string> vals = read_saved(streams);
    if (vals.size() > (size_t)N)
        std::fprintf(stderr, "402608_01: note: keeping saved lines beyond N=%d (not re-verified)\n", N);

    for (int n = 1; n <= N; n++) {
        std::string v = compute_term(n);
        if ((size_t)n <= vals.size()) {
            if (vals[(size_t)n - 1] != v) {
                std::fprintf(stderr, "402608_01: saved a(%d) = %s but computed %s; file left unchanged\n",
                             n, vals[(size_t)n - 1].c_str(), v.c_str());
                return 1;
            }
            if (std::printf("%d %s (verified)\n", n, v.c_str()) < 0) die("printf failed");
        } else {
            vals.push_back(v);
            write_all(vals, streams);
            if (std::printf("%d %s\n", n, v.c_str()) < 0) die("printf failed");
        }
        if (std::fflush(stdout) != 0) die("fflush stdout failed");
    }
    return 0;
}
