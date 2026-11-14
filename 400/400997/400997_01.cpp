// 400997_01.cpp  --  b-file for OEIS A400997 (as defined below)
//
// a(n) = number of tilings of an n X n square by isosceles right triangles
//        with vertices at lattice points and legs parallel to the sides of
//        the square.
//        2, 26, 2134, 1322672, 5653917654, ...
//
// Usage:  ./400997_01 N        computes a(1..N); after each n the b-file
//                              b400997_01.txt ("n a(n)") is rewritten atomically
//         ./400997_01 --help
//
// ---------------------------------------------------------------------------
// Cells: the 4n^2 elementary triangles ("quarters" N,E,S,W of each unit
// square), ordered row by row (top to bottom), square by square (left to
// right), and N,E,S,W inside a square.
// Tiles: isosceles right triangles with lattice vertices and legs parallel
// to the axes, i.e. right-angle vertex (a,b), legs of integer length k in
// the four axis directions; the hypotenuse lies on a line x +- y = int, so
// every tile is a union of cells.
// (These are the (L) tiles of A402162 (402162_01.cpp); every tiling counted
// here is also counted there.)
// A cell belongs to a tile iff its centroid lies inside the triangle (cells
// never straddle tile sides, since the sides lie on the grid lines).
//
// Counting: exact cover in cell order.  In every partial tiling built in this
// order, all cells before the first uncovered cell f are covered, and the
// tile covering f must be a tile whose first cell is f.  So
//    count(S) = sum over tiles T with first cell f(S), T disjoint from S,
//               of count(S u T),
// and states S are processed in increasing order of f(S) (a tile placement
// strictly increases f).  States with the same covered set are merged
// (hash map per f); a bucket is freed once processed.
// Each tiling corresponds to exactly one path (the order of placement is
// forced), so the final count is a(n).  Checked against a Python brute force
// (two different cell orders) for n = 1..6, and a(2) = 26 by hand.
//
// Numbers: fixed width VW limbs of 64 bits with VW = ceil((5n^2-2n)/64) + 1.
//   a(n) <= 2^(5n^2-2n): a tiling is determined by the partition of every unit
//   square into pieces (here at most 3 possibilities: whole or one of the two
//   halves; we use the cruder 8) and, for each of the 2n(n-1) interior unit
//   edges, whether it lies on a tile boundary.  Intermediate values are
//   counts of partial tilings; any carry out of the top limb aborts the
//   program (nothing is written), so a wrong value can never be saved.
// ---------------------------------------------------------------------------
//
// Build:  g++ -O3 -march=native -std=c++17 -Wall -Wextra -Wpedantic -o 400997_01 400997_01.cpp
//         (option: -DMAXN=n  largest allowed N, default 12, at most 12)

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
#define MAXN 12
#endif
static_assert(MAXN >= 1 && MAXN <= 12, "MAXN must be in 1..12 (4n^2 <= 576 cells in 9 words)");

__extension__ typedef unsigned __int128 u128;

static const char *OUTFILE = "b400997_01.txt";
static const char *LOCKFILE = "b400997_01.txt.lock";
static const size_t MAX_SAVED_BYTES = 16u << 20;
static const size_t MAX_DIGITS = 2000;
static const int MAXKW = 9;      // key words (cells / 64)
static const int MAXVW = 12;     // value limbs

[[noreturn]] static void die(const char *msg) {
    std::fprintf(stderr, "400997_01: %s\n", msg);
    std::exit(1);
}
[[noreturn]] static void die_errno(const char *msg) {
    std::fprintf(stderr, "400997_01: %s: %s\n", msg, std::strerror(errno));
    std::exit(1);
}

static int KW, VW;               // run-time widths for the current n
static bool g_overflow = false;

// ---------------- values ----------------
static inline void val_add(uint64_t *r, const uint64_t *a) {
    u128 c = 0;
    for (int k = 0; k < VW; k++) { c += (u128)r[k] + a[k]; r[k] = (uint64_t)c; c >>= 64; }
    if (c) g_overflow = true;
}
static std::string val_to_dec(const uint64_t *x) {
    uint64_t t[MAXVW];
    std::memcpy(t, x, sizeof(uint64_t) * (size_t)VW);
    std::vector<uint64_t> ch;
    const uint64_t BASE = 10000000000000000000ULL;
    for (;;) {
        bool zero = true;
        for (int k = 0; k < VW; k++) if (t[k]) { zero = false; break; }
        if (zero) break;
        u128 rem = 0;
        for (int k = VW - 1; k >= 0; k--) {
            u128 cur = (rem << 64) | t[k];
            t[k] = (uint64_t)(cur / BASE);
            rem = cur % BASE;
        }
        ch.push_back((uint64_t)rem);
    }
    if (ch.empty()) return "0";
    std::string s = std::to_string(ch.back());
    char buf[32];
    for (size_t i = ch.size() - 1; i-- > 0;) { std::snprintf(buf, sizeof buf, "%019llu", (unsigned long long)ch[i]); s += buf; }
    return s;
}

// ---------------- hash map: KW-word key -> VW-limb value ----------------
struct Map {
    size_t cap = 0, cnt = 0;
    uint64_t *keys = nullptr;    // cap * KW ; empty slot: first word == EMPTY0
    uint64_t *vals = nullptr;    // cap * VW
};
// keys always have bit 0 of word 0 set except for the empty start state, which
// is stored in its own bucket handling below; we mark empty slots with a flag array
static void map_alloc(Map &m, size_t cap, unsigned char *&used) {
    (void)used;
    if (cap < 16) cap = 16;
    if (cap > SIZE_MAX / (sizeof(uint64_t) * (size_t)(KW + VW) + 1)) die("hash table too large");
    m.cap = cap; m.cnt = 0;
    m.keys = static_cast<uint64_t *>(std::calloc(cap * (size_t)KW + cap, sizeof(uint64_t)));  // + flags
    m.vals = static_cast<uint64_t *>(std::calloc(cap * (size_t)VW, sizeof(uint64_t)));
    if (!m.keys || !m.vals) die("out of memory (try a smaller N)");
}
// flag of slot i is stored after the keys: keys[cap*KW + i] (0 = empty)
static inline uint64_t &slot_flag(Map &m, size_t i) { return m.keys[m.cap * (size_t)KW + i]; }
static void map_free(Map &m) { std::free(m.keys); std::free(m.vals); m.keys = m.vals = nullptr; m.cap = m.cnt = 0; }
static inline size_t hash_key(const uint64_t *k, size_t cap) {
    uint64_t h = 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < KW; i++) { h ^= k[i] + 0x9E3779B97F4A7C15ULL + (h << 6) + (h >> 2); h *= 0xff51afd7ed558ccdULL; h ^= h >> 33; }
    h *= 0xc4ceb9fe1a85ec53ULL; h ^= h >> 33;
    return (size_t)(((u128)h * cap) >> 64);
}
static void map_add(Map &m, const uint64_t *key, const uint64_t *val);
static void map_resize(Map &m, size_t newcap) {
    Map n; unsigned char *dummy = nullptr;
    map_alloc(n, newcap, dummy);
    for (size_t i = 0; i < m.cap; i++)
        if (slot_flag(m, i)) map_add(n, m.keys + i * (size_t)KW, m.vals + i * (size_t)VW);
    map_free(m);
    m = n;
}
static void map_add(Map &m, const uint64_t *key, const uint64_t *val) {
    if (m.cap == 0) { unsigned char *dummy = nullptr; map_alloc(m, 64, dummy); }
    if ((m.cnt + 1) * 4 > m.cap * 3) map_resize(m, m.cap * 2);
    size_t h = hash_key(key, m.cap);
    for (;;) {
        if (!slot_flag(m, h)) {
            slot_flag(m, h) = 1;
            std::memcpy(m.keys + h * (size_t)KW, key, sizeof(uint64_t) * (size_t)KW);
            std::memcpy(m.vals + h * (size_t)VW, val, sizeof(uint64_t) * (size_t)VW);
            m.cnt++;
            return;
        }
        if (std::memcmp(m.keys + h * (size_t)KW, key, sizeof(uint64_t) * (size_t)KW) == 0) {
            val_add(m.vals + h * (size_t)VW, val);
            return;
        }
        if (++h == m.cap) h = 0;
    }
}

// ---------------- tiles ----------------
struct Tile { uint64_t m[MAXKW]; };
static std::vector<std::vector<Tile>> g_by_first;   // tiles indexed by first cell

static void build_tiles(int n) {
    const int NQ = 4 * n * n;
    // centroids in units of 1/6, (X right, Y down); cell index 4*(y*n+x)+k, k = N,E,S,W
    std::vector<int> cx(NQ), cy(NQ);
    for (int y = 0; y < n; y++)
        for (int x = 0; x < n; x++) {
            int c = 4 * (y * n + x);
            cx[c + 0] = 6 * x + 3; cy[c + 0] = 6 * y + 1;   // N
            cx[c + 1] = 6 * x + 5; cy[c + 1] = 6 * y + 3;   // E
            cx[c + 2] = 6 * x + 3; cy[c + 2] = 6 * y + 5;   // S
            cx[c + 3] = 6 * x + 1; cy[c + 3] = 6 * y + 3;   // W
        }
    std::vector<std::vector<int>> tris;   // vertices in half units: x1,y1,x2,y2,x3,y3
    const int M = 2 * n;
    auto add_tri = [&](int x1, int y1, int x2, int y2, int x3, int y3) {
        int v[6] = { x1, y1, x2, y2, x3, y3 };
        for (int i = 0; i < 6; i++) if (v[i] < 0 || v[i] > M) return;
        tris.push_back(std::vector<int>(v, v + 6));
    };
    for (int a = 0; a <= n; a++)
        for (int b = 0; b <= n; b++)
            for (int k = 1; k <= n; k++) {
                for (int sx = -1; sx <= 1; sx += 2)
                    for (int sy = -1; sy <= 1; sy += 2)           // (L): right angle at (a,b)
                        add_tri(2 * a, 2 * b, 2 * (a + sx * k), 2 * b, 2 * a, 2 * (b + sy * k));
            }
    std::vector<Tile> all;
    for (auto &t : tris) {
        long long X[3], Y[3];
        for (int i = 0; i < 3; i++) { X[i] = 3LL * t[2 * i]; Y[i] = 3LL * t[2 * i + 1]; }
        Tile T; std::memset(T.m, 0, sizeof T.m);
        int cnt = 0;
        for (int c = 0; c < NQ; c++) {
            long long px = cx[c], py = cy[c];
            long long d1 = (X[1] - X[0]) * (py - Y[0]) - (Y[1] - Y[0]) * (px - X[0]);
            long long d2 = (X[2] - X[1]) * (py - Y[1]) - (Y[2] - Y[1]) * (px - X[1]);
            long long d3 = (X[0] - X[2]) * (py - Y[2]) - (Y[0] - Y[2]) * (px - X[2]);
            if ((d1 > 0 && d2 > 0 && d3 > 0) || (d1 < 0 && d2 < 0 && d3 < 0)) { T.m[c / 64] |= 1ULL << (c % 64); cnt++; }
            else if (d1 == 0 || d2 == 0 || d3 == 0) {
                // a centroid on a tile side would mean a cell straddling it: impossible
                bool on = (d1 == 0 && d2 * d3 > 0) || (d2 == 0 && d1 * d3 > 0) || (d3 == 0 && d1 * d2 > 0);
                if (on) die("internal: centroid on a tile side");
            }
        }
        if (cnt == 0) die("internal: empty tile");
        all.push_back(T);
    }
    // remove duplicates
    std::sort(all.begin(), all.end(), [](const Tile &p, const Tile &q) { return std::memcmp(p.m, q.m, sizeof p.m) < 0; });
    all.erase(std::unique(all.begin(), all.end(), [](const Tile &p, const Tile &q) { return std::memcmp(p.m, q.m, sizeof p.m) == 0; }), all.end());
    g_by_first.assign(NQ, {});
    for (auto &T : all) {
        int f = -1;
        for (int w = 0; w < MAXKW && f < 0; w++) if (T.m[w]) f = 64 * w + __builtin_ctzll(T.m[w]);
        g_by_first[f].push_back(T);
    }
}

// first zero bit at position >= from (returns NQ if none)
static inline int first_zero(const uint64_t *k, int from, int NQ) {
    int w = from / 64;
    uint64_t x = ~k[w] & (~0ULL << (from % 64));
    for (;;) {
        if (x) { int p = 64 * w + __builtin_ctzll(x); return p < NQ ? p : NQ; }
        if (++w >= KW) return NQ;
        x = ~k[w];
    }
}

static std::string compute_term(int n) {
    const int NQ = 4 * n * n;
    KW = (NQ + 63) / 64;
    const int bits = 5 * n * n - 2 * n;
    VW = (bits + 63) / 64 + 1;
    if (KW > MAXKW || VW > MAXVW) die("internal: widths");
    build_tiles(n);
    g_overflow = false;

    std::vector<Map> bucket(NQ + 1);
    uint64_t key[MAXKW] = { 0 }, val[MAXVW] = { 0 };
    val[0] = 1;
    map_add(bucket[0], key, val);
    size_t total = 0, peak_live = 0, live = 1;
    time_t t0 = std::time(nullptr);
    for (int f = 0; f < NQ; f++) {
        Map &B = bucket[f];
        if (B.cap == 0) continue;
        total += B.cnt;
        for (size_t i = 0; i < B.cap; i++) {
            if (!slot_flag(B, i)) continue;
            const uint64_t *k = B.keys + i * (size_t)KW;
            const uint64_t *v = B.vals + i * (size_t)VW;
            for (const Tile &T : g_by_first[f]) {
                bool ok = true;
                for (int w = 0; w < KW; w++) if (k[w] & T.m[w]) { ok = false; break; }
                if (!ok) continue;
                uint64_t nk[MAXKW];
                for (int w = 0; w < KW; w++) nk[w] = k[w] | T.m[w];
                int f2 = first_zero(nk, f, NQ);
                size_t before = bucket[f2].cnt;
                map_add(bucket[f2], nk, v);
                live += bucket[f2].cnt - before;
            }
        }
        live -= B.cnt;
        map_free(B);
        if (live > peak_live) peak_live = live;
        if (g_overflow) die("overflow of the value width; nothing written (report this)");
        if ((f + 1) % (4 * n) == 0)
            std::fprintf(stderr, "400997_01:   n=%d row %d/%d done, %zu states so far, %zu live, %lds\n",
                         n, (f + 1) / (4 * n), n, total, live, (long)(std::time(nullptr) - t0));
    }
    Map &F = bucket[NQ];
    if (F.cnt != 1) die("internal: final bucket");
    std::string s;
    for (size_t i = 0; i < F.cap; i++)
        if (slot_flag(F, i)) {
            for (int w = 0; w < KW; w++) {
                uint64_t want = (w < NQ / 64) ? ~0ULL : (NQ % 64 ? ((1ULL << (NQ % 64)) - 1) : 0);
                if (w * 64 >= NQ) want = 0;
                if (F.keys[i * (size_t)KW + w] != want) die("internal: final key");
            }
            const uint64_t *v = F.vals + i * (size_t)VW;
            // check against the proven bound a(n) <= 2^bits
            for (int b = bits; b < 64 * VW; b++)
                if ((v[b / 64] >> (b % 64)) & 1) die("value exceeds proven bound; nothing written");
            s = val_to_dec(v);
        }
    map_free(F);
    std::fprintf(stderr, "400997_01: n=%d: %zu states, peak %zu live, %lds\n", n, total, peak_live,
                 (long)(std::time(nullptr) - t0));
    return s;
}

// ---------------- arguments and files ----------------
static void usage(FILE *f) {
    std::fprintf(f,
        "usage: 400997_01 N\n"
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
        std::fprintf(stderr, "400997_01: N must satisfy 1 <= N <= %d\n", MAXN);
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
            std::fprintf(stderr, "400997_01: note: ignoring incomplete last line of %s\n", OUTFILE);
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
        std::fprintf(stderr, "400997_01: note: keeping saved lines beyond N=%d (not re-verified)\n", N);

    for (int n = 1; n <= N; n++) {
        std::string v = compute_term(n);
        if ((size_t)n <= vals.size()) {
            if (vals[(size_t)n - 1] != v) {
                std::fprintf(stderr, "400997_01: saved a(%d) = %s but computed %s; file left unchanged\n",
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
