// 401338_01.cpp  --  b-file for OEIS A401338
//
// a(n) = number of ways to tile a size n staircase polyomino with squares.
//        (A size-n staircase polyomino consists of n left-aligned rows of
//        lengths 1, 2, ..., n.)
//        1, 1, 2, 4, 14, 58, 352, 2860, 32008, 490972, ...
//
// Usage:  ./401338_01 [--memory-mib MIB] N
//         computes a(1..N); after each n the b-file
//                              b401338_01.txt ("n a(n)") is rewritten atomically
//         ./401338_01 --help
//
// ---------------------------------------------------------------------------
// Cells (i,j), 0 <= j <= i <= n-1 (row i from the top has length i+1), are
// taken in row-major order, short rows first.  In a partial tiling built by
// always covering the first uncovered cell (i,j) with a square whose top-left
// corner is (i,j), the covered cells of every column form a prefix from its
// top (squares always cover whole runs of rows starting at the current row),
// so a state is the "skyline"  h_c = number of covered cells of column c
// (column c consists of the rows c..n-1).  The first uncovered cell is in row
// i = min_c (c + h_c) (over unfinished columns) at the smallest such column j.
// A square of side k with top-left corner (i,j) fits iff j+k-1 <= i (it stays
// in row i), i+k-1 <= n-1, and c + h_c = i for c = j..j+k-1 (all these cells
// of row i are uncovered; the rows below are then uncovered as well); it adds
// k to h_j..h_{j+k-1}.  Each tiling corresponds to exactly one sequence of
// placements, so the number of paths from the empty skyline to the full one
// is a(n).  States are processed in increasing order of the first uncovered
// cell (a placement strictly increases it); equal skylines are merged (one
// hash map per cell, freed when done).
// Checked against a Python brute force (exact cover of the cells, two cell
// orders) for n = 1..14 and the Python skyline count for n = 1..23.
//
// Values: residues modulo primes p < 2^62, LANES primes per pass, rebuilt by
// CRT (Garner).  Bound:  a(n) <= 2^(n(n-1)): a tiling is determined by the set
// of interior unit edges lying on square boundaries, and the staircase has
// n(n-1)/2 interior horizontal and n(n-1)/2 interior vertical unit edges.  The
// product of the K primes exceeds this bound; one extra prime is a check (the
// rebuilt value must agree with it and be <= the bound, otherwise nothing is
// written).
// Keys: 6 bits per column height, 10 columns per word (n <= 42 -> 5 words).
// ---------------------------------------------------------------------------
//
// Build:  g++ -O3 -march=native -std=c++17 -Wall -Wextra -Wpedantic -o 401338_01 401338_01.cpp
//         (options: -DLANES=g  primes per pass, default 8 (memory 8 bytes/state each)
//                   -DMAXN=n   largest allowed N, default 42, at most 42)

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
#define MAXN 42
#endif
#ifndef LANES
#define LANES 8
#endif
static_assert(MAXN >= 1 && MAXN <= 42, "MAXN must be in 1..42 (heights < 64, 5 key words)");
static_assert(LANES >= 1 && LANES <= 32, "LANES must be in 1..32");

__extension__ typedef unsigned __int128 u128;

static const char *OUTFILE = "b401338_01.txt";
static const char *LOCKFILE = "b401338_01.txt.lock";
static const size_t MAX_SAVED_BYTES = 16u << 20;
static const size_t MAX_DIGITS = 2000;
static constexpr size_t MIB = 1024 * 1024;
static constexpr size_t DEFAULT_MEMORY_MIB = std::min<size_t>(4096, SIZE_MAX / MIB);
static const int KW = 5;          // key words (10 columns of 6 bits per word)

[[noreturn]] static void die(const char *msg) {
    std::fprintf(stderr, "401338_01: %s\n", msg);
    std::exit(1);
}
[[noreturn]] static void die_errno(const char *msg) {
    std::fprintf(stderr, "401338_01: %s: %s\n", msg, std::strerror(errno));
    std::exit(1);
}

// ---------------- 64-bit modular arithmetic, primes ----------------
static inline uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m) { return (uint64_t)((u128)a * b % m); }
static uint64_t powmod(uint64_t a, uint64_t e, uint64_t m) {
    uint64_t r = 1 % m; a %= m;
    while (e) { if (e & 1) r = mulmod(r, a, m); a = mulmod(a, a, m); e >>= 1; }
    return r;
}
static bool is_prime64(uint64_t n) {          // deterministic Miller-Rabin for n < 2^64
    if (n < 2) return false;
    static const uint64_t B[] = { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37 };
    for (uint64_t p : B) { if (n % p == 0) return n == p; }
    uint64_t d = n - 1; int s = 0;
    while ((d & 1) == 0) { d >>= 1; s++; }
    for (uint64_t a : B) {
        uint64_t x = powmod(a, d, n);
        if (x == 1 || x == n - 1) continue;
        bool comp = true;
        for (int r = 1; r < s; r++) { x = mulmod(x, x, n); if (x == n - 1) { comp = false; break; } }
        if (comp) return false;
    }
    return true;
}

// ---------------- small unsigned big integer (base 2^32) ----------------
struct BigU {
    std::vector<uint32_t> d;
    void trim() { while (!d.empty() && d.back() == 0) d.pop_back(); }
};
static void mul_u64(BigU &x, uint64_t m) {
    u128 c = 0;
    for (auto &w : x.d) { c += (u128)w * m; w = (uint32_t)c; c >>= 32; }
    while (c) { x.d.push_back((uint32_t)c); c >>= 32; }
    x.trim();
}
static void add_u64(BigU &x, uint64_t a) {
    u128 c = a;
    for (size_t k = 0; c && k < x.d.size(); k++) { c += x.d[k]; x.d[k] = (uint32_t)c; c >>= 32; }
    while (c) { x.d.push_back((uint32_t)c); c >>= 32; }
}
static uint64_t mod_u64(const BigU &x, uint64_t m) {
    u128 r = 0;
    for (size_t k = x.d.size(); k-- > 0;) r = ((r << 32) | x.d[k]) % m;
    return (uint64_t)r;
}
static int cmp(const BigU &a, const BigU &b) {
    if (a.d.size() != b.d.size()) return a.d.size() < b.d.size() ? -1 : 1;
    for (size_t k = a.d.size(); k-- > 0;) if (a.d[k] != b.d[k]) return a.d[k] < b.d[k] ? -1 : 1;
    return 0;
}
static std::string to_dec(BigU x) {
    if (x.d.empty()) return "0";
    std::vector<uint32_t> ch;
    while (!x.d.empty()) {
        uint64_t r = 0;
        for (size_t k = x.d.size(); k-- > 0;) {
            uint64_t cur = (r << 32) | x.d[k];
            x.d[k] = (uint32_t)(cur / 1000000000u);
            r = cur % 1000000000u;
        }
        x.trim();
        ch.push_back((uint32_t)r);
    }
    std::string s = std::to_string(ch.back());
    char buf[16];
    for (size_t i = ch.size() - 1; i-- > 0;) { std::snprintf(buf, sizeof buf, "%09u", ch[i]); s += buf; }
    return s;
}

static uint64_t g_p[LANES];

// ---------------- hash map: 5-word key -> LANES residues ----------------
struct Key { uint64_t w[KW]; };
static inline bool key_eq(const Key &a, const Key &b) { return std::memcmp(a.w, b.w, sizeof a.w) == 0; }
struct Map {
    size_t cap = 0, cnt = 0;
    Key *keys = nullptr;
    uint64_t *vals = nullptr;
    unsigned char *used = nullptr;
};
static constexpr size_t MAP_SLOT_BYTES = sizeof(Key) + LANES * sizeof(uint64_t) + 1;
static size_t map_memory_limit = DEFAULT_MEMORY_MIB * MIB;
static size_t map_memory_used = 0;
static void map_alloc(Map &m, size_t cap) {
    if (cap < 16) cap = 16;
    // Include every live bucket and old/new arrays during rehashing.
    if (cap > (map_memory_limit - map_memory_used) / MAP_SLOT_BYTES)
        die("state-table memory limit exceeded (increase --memory-mib or use a smaller N or LANES)");
    m.cap = cap; m.cnt = 0;
    m.keys = static_cast<Key *>(std::malloc(cap * sizeof(Key)));
    m.vals = static_cast<uint64_t *>(std::malloc(cap * LANES * sizeof(uint64_t)));
    m.used = static_cast<unsigned char *>(std::calloc(cap, 1));
    if (!m.keys || !m.vals || !m.used) die("out of memory (try a smaller N or LANES)");
    map_memory_used += cap * MAP_SLOT_BYTES;
}
static void map_free(Map &m) {
    std::free(m.keys); std::free(m.vals); std::free(m.used);
    map_memory_used -= m.cap * MAP_SLOT_BYTES;
    m = Map{};
}
static inline size_t slot0(const Key &k, size_t cap) {
    uint64_t h = 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < KW; i++) { h ^= k.w[i] + 0x9E3779B97F4A7C15ULL + (h << 6) + (h >> 2); h *= 0xff51afd7ed558ccdULL; h ^= h >> 33; }
    h *= 0xc4ceb9fe1a85ec53ULL; h ^= h >> 33;
    return (size_t)(((u128)h * cap) >> 64);
}
static void map_add(Map &m, const Key &key, const uint64_t *v);
static void map_resize(Map &m, size_t newcap) {
    Map n;
    map_alloc(n, newcap);
    for (size_t i = 0; i < m.cap; i++) if (m.used[i]) map_add(n, m.keys[i], m.vals + i * LANES);
    map_free(m);
    m = n;
}
static size_t find_slot(const Map &m, const Key &key) {
    size_t h = slot0(key, m.cap);
    while (m.used[h] && !key_eq(m.keys[h], key)) {
        if (++h == m.cap) h = 0;
    }
    return h;
}
static void map_add(Map &m, const Key &key, const uint64_t *v) {
    if (m.cap == 0) map_alloc(m, 64);
    size_t h = find_slot(m, key);
    if (m.used[h]) {
        uint64_t *d = m.vals + h * LANES;
        for (int lane = 0; lane < LANES; lane++) {
            uint64_t sum = d[lane] + v[lane];
            d[lane] = sum >= g_p[lane] ? sum - g_p[lane] : sum;
        }
        return;
    }
    if ((m.cnt + 1) * 20 > m.cap * 17) {
        map_resize(m, m.cap + m.cap / 2 + 16);   // load <= 0.85
        h = find_slot(m, key);
    }
    m.used[h] = 1;
    m.keys[h] = key;
    std::memcpy(m.vals + h * LANES, v, LANES * sizeof(uint64_t));
    m.cnt++;
}

// ---------------- skyline ----------------
// column c is stored in word c / 10, bits 6*(c % 10) .. 6*(c % 10)+5 (no straddling)
static inline int get_h(const Key &k, int c) { return (int)((k.w[c / 10] >> (6 * (c % 10))) & 63); }
static inline void set_h(Key &k, int c, int v) {
    const int w = c / 10, sh = 6 * (c % 10);
    k.w[w] = (k.w[w] & ~(63ULL << sh)) | ((uint64_t)v << sh);
}

// first uncovered cell (row-major, short rows first): returns its index, or -1 if full
static inline int first_cell(const int *h, int n, int &row, int &col) {
    row = n; col = -1;
    for (int c = 0; c < n; c++) {
        if (h[c] >= n - c) continue;                // column finished
        int r = c + h[c];
        if (r < row) { row = r; col = c; }          // smallest row, then smallest column
    }
    if (col < 0) return -1;
    return row * (row + 1) / 2 + col;
}

static void run_pass(int n, uint64_t *res, bool verbose) {
    const int NC = n * (n + 1) / 2;
    std::vector<Map> bucket(NC + 1);                // bucket NC: complete tilings
    {
        Key k0; std::memset(k0.w, 0, sizeof k0.w);
        uint64_t one[LANES];
        for (int l = 0; l < LANES; l++) one[l] = 1 % g_p[l];
        map_add(bucket[0], k0, one);
    }
    BigU total;
    size_t live = 1, peak = 1;
    time_t t0 = std::time(nullptr);
    int h[MAXN + 1];
    for (int f = 0; f < NC; f++) {
        Map &B = bucket[f];
        if (B.cap == 0) continue;
        add_u64(total, B.cnt);
        for (size_t s = 0; s < B.cap; s++) {
            if (!B.used[s]) continue;
            const Key &K = B.keys[s];
            const uint64_t *v = B.vals + s * LANES;
            for (int c = 0; c < n; c++) h[c] = get_h(K, c);
            int i, j;
            const int fc = first_cell(h, n, i, j);
            if (fc != f) die("internal: state in the wrong bucket");
            for (int k = 1; j + k - 1 <= i && i + k - 1 <= n - 1; k++) {
                const int c = j + k - 1;            // new column of the square
                if (c + h[c] != i) break;           // cell (i,c) already covered: larger squares fail too
                Key K2 = K;
                for (int t = j; t <= c; t++) set_h(K2, t, h[t] + k);
                int h2[MAXN + 1];
                for (int t = 0; t < n; t++) h2[t] = h[t];
                for (int t = j; t <= c; t++) h2[t] += k;
                int i2, j2;
                int f2 = first_cell(h2, n, i2, j2);
                if (f2 < 0) f2 = NC;
                else if (f2 <= f) die("internal: first cell did not advance");
                size_t before = bucket[f2].cnt;
                map_add(bucket[f2], K2, v);
                live += bucket[f2].cnt - before;
                if (live > peak) peak = live;
            }
        }
        live -= B.cnt;
        map_free(B);
        if (verbose && (f + 1) % ((n + 1) * 4) == 0)
            std::fprintf(stderr, "401338_01:   n=%d cells %d/%d, %s states so far, %zu live, %lds\n",
                         n, f + 1, NC, to_dec(total).c_str(), live, (long)(std::time(nullptr) - t0));
    }
    Map &F = bucket[NC];
    if (F.cnt != 1) die("internal: final bucket");
    for (size_t s = 0; s < F.cap; s++)
        if (F.used[s]) for (int l = 0; l < LANES; l++) res[l] = F.vals[s * LANES + l];
    map_free(F);
    if (verbose) std::fprintf(stderr, "401338_01:   n=%d: %s states, peak %zu live\n", n, to_dec(total).c_str(), peak);
}

static std::string compute_term(int n) {
    const unsigned bits = (unsigned)n * (unsigned)(n - 1);    // a(n) <= 2^bits
    BigU bound; bound.d.assign(bits / 32 + 1, 0); bound.d[bits / 32] = 1u << (bits % 32);
    std::vector<uint64_t> primes;
    {
        BigU P; P.d = { 1 };
        uint64_t c = (1ULL << 62) - 1;
        while (cmp(P, bound) <= 0) {
            while (!is_prime64(c)) c--;
            primes.push_back(c); mul_u64(P, c); c--;
        }
        while (!is_prime64(c)) c--;
        primes.push_back(c);                                   // check prime
    }
    const size_t np = primes.size(), K = np - 1;
    std::fprintf(stderr, "401338_01: n=%d: %zu prime(s) + 1 check prime, %zu pass(es) (LANES=%d)\n",
                 n, K, (np + LANES - 1) / LANES, LANES);
    std::vector<uint64_t> R(np);
    time_t t0 = std::time(nullptr);
    for (size_t k0 = 0; k0 < np; k0 += LANES) {
        for (int l = 0; l < LANES; l++) g_p[l] = primes[k0 + (size_t)l < np ? k0 + (size_t)l : np - 1];
        uint64_t res[LANES] = { 0 };
        run_pass(n, res, k0 == 0);
        for (int l = 0; l < LANES && k0 + (size_t)l < np; l++) R[k0 + (size_t)l] = res[l];
        size_t done = k0 + LANES < np ? k0 + LANES : np;
        std::fprintf(stderr, "401338_01: n=%d: primes %zu/%zu done, %lds\n", n, done, np, (long)(std::time(nullptr) - t0));
    }
    std::vector<uint64_t> c(K);
    for (size_t j = 0; j < K; j++) {
        const uint64_t pj = primes[j];
        uint64_t v = 0, prod = 1;
        for (size_t t = 0; t < j; t++) {
            v = (v + mulmod(c[t] % pj, prod, pj)) % pj;
            prod = mulmod(prod, primes[t] % pj, pj);
        }
        uint64_t diff = (R[j] % pj + pj - v) % pj;
        c[j] = mulmod(diff, powmod(prod, pj - 2, pj), pj);
    }
    BigU x;
    for (size_t j = K; j-- > 0;) { mul_u64(x, primes[j]); add_u64(x, c[j]); }
    if (mod_u64(x, primes[K]) != R[K]) {
        std::fprintf(stderr, "401338_01: check prime mismatch at n=%d; nothing written for this n\n", n);
        std::exit(1);
    }
    if (cmp(x, bound) > 0) die("value exceeds proven bound; nothing written");
    return to_dec(x);
}

// ---------------- arguments and files ----------------
static void usage(FILE *f) {
    std::fprintf(f,
        "usage: 401338_01 [--memory-mib MIB] N\n"
        "  counts square tilings of the staircase with row lengths 1,2,...,n\n"
        "  saves each new term to %s\n"
        "  1 <= N <= %d; saved lines through N are re-verified\n"
        "  --memory-mib MIB limits all state tables including rehashes (default %zu)\n",
        OUTFILE, MAXN, DEFAULT_MEMORY_MIB);
}
static int parse_n(const char *s) {
    if (!*s) die("N must be a positive integer");
    for (const char *p = s; *p; p++)
        if (*p < '0' || *p > '9') die("N must be a positive integer (digits only)");
    errno = 0;
    char *end = nullptr;
    long v = std::strtol(s, &end, 10);
    if (errno || *end || v < 1 || v > MAXN) {
        std::fprintf(stderr, "401338_01: N must satisfy 1 <= N <= %d\n", MAXN);
        std::exit(1);
    }
    return (int)v;
}
static size_t parse_memory_mib(const char *s) {
    if (!*s) die("--memory-mib requires a positive integer");
    for (const char *p = s; *p; p++)
        if (*p < '0' || *p > '9') die("--memory-mib requires a positive integer");
    errno = 0;
    char *end = nullptr;
    unsigned long long value = std::strtoull(s, &end, 10);
    if (errno || *end || value == 0 || value > SIZE_MAX / MIB)
        die("--memory-mib is out of range");
    return static_cast<size_t>(value);
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
        std::fprintf(stderr, "401338_01: stdout is redirected to %s\n", OUTFILE);
    else if (!out_alias)
        std::fprintf(stdout, "401338_01: stderr is redirected to %s\n", OUTFILE);
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

    if (argc == 2 && (!std::strcmp(argv[1], "--help") || !std::strcmp(argv[1], "-h"))) {
        usage(stdout);
        return 0;
    }
    int N = 0;
    bool have_memory_limit = false;
    for (int i = 1; i < argc; i++) {
        if (std::strcmp(argv[i], "--memory-mib") == 0) {
            if (have_memory_limit || ++i == argc) die("expected one --memory-mib value");
            map_memory_limit = parse_memory_mib(argv[i]) * MIB;
            have_memory_limit = true;
        } else {
            if (N != 0) { usage(stderr); return 1; }
            N = parse_n(argv[i]);
        }
    }
    if (N == 0) { usage(stderr); return 1; }

    open_lock();
    std::vector<std::string> vals = read_saved(streams);
    if (vals.size() > (size_t)N)
        std::fprintf(stderr, "401338_01: note: keeping saved lines beyond N=%d (not re-verified)\n", N);

    for (int n = 1; n <= N; n++) {
        std::string v = compute_term(n);
        if ((size_t)n <= vals.size()) {
            if (vals[(size_t)n - 1] != v) {
                std::fprintf(stderr, "401338_01: saved a(%d) = %s but computed %s; file left unchanged\n",
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
