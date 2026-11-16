// 402226_01.cpp  --  b-file for OEIS A402226
//
// a(n) = number of tilings of a regular hexagon of side n by equilateral
//        triangles of integer side lengths (any sizes, both orientations).
//        1, 117, 298538, 32053026686, 121885999659021819, ...
//
// Usage:  ./402226_01 N        computes a(1..N); after each n the b-file
//                              b402226_01.txt ("n a(n)") is rewritten atomically
//         ./402226_01 --help
//
// ---------------------------------------------------------------------------
// Sheared coordinates.  The linear map sending the triangular lattice basis
// (1,0), (1/2, sqrt(3)/2) to (1,0), (0,1) maps the triangular lattice onto
// Z^2; a unit up-triangle becomes the lower-left half and a unit down-triangle
// the upper-right half of a unit square cut along a line x + y = const.  The
// hexagon of side n becomes the region
//      0 <= x <= 2n,  0 <= y <= 2n,  n <= x + y <= 3n,
// and the equilateral triangles of side k become
//      up:   (a,b), (a+k,b), (a,b+k)        down: (a+k,b), (a,b+k), (a+k,b+k).
// (An affine bijection preserves tilings, so the count is unchanged.)
// Cells: the 6n^2 unit triangles of the hexagon, numbered row by row
// (y = 2n-1 down to 0), square by square (x increasing), lower-left half
// before upper-right half.  A cell belongs to a tile iff its centroid lies
// inside the tile; a tile is used iff all its k^2 cells lie in the hexagon.
// Checked: the same code with the triangle region gives 1, 2, 5, 26, ... (the
// counts for the equilateral triangle, cf. 358715_01.c).
//
// Counting: exact cover in cell order.  In every partial tiling built in this
// order all cells before the first uncovered cell f are covered, and the tile
// covering f must be a tile whose first cell is f.  So
//    count(S) = sum over tiles T with first cell f(S), T disjoint from S,
//               of count(S u T),
// processed in increasing order of f(S) (a placement strictly increases f);
// equal covered sets are merged (one hash map per f, freed when done).  Each
// tiling corresponds to exactly one path, so the final count is a(n).
// Only the cells f+1 .. 6n^2-1 are stored in the key of a state of bucket f.
//
// Values: residues modulo primes p < 2^62 (uint64_t, a+b < 2^63), LANES primes
// per pass; a(n) is rebuilt by CRT (Garner).  Bound:
//   a(n) <= 2^(9n^2 - 3n).  A tiling is determined by the set of interior
//   edges between adjacent unit triangles that lie on tile boundaries (the
//   tiles are the connected pieces); there are (3*6n^2 - 6n)/2 = 9n^2 - 3n
//   interior edges.
// The product of the K primes exceeds this bound; one extra prime is used
// only as a check (the rebuilt value must agree with it and be <= the bound,
// otherwise nothing is written).
// ---------------------------------------------------------------------------
//
// Build:  g++ -O3 -march=native -std=c++17 -Wall -Wextra -Wpedantic -o 402226_01 402226_01.cpp
//         (options: -DLANES=g   primes per pass, default 4 (memory 8 bytes/state each)
//                   -DMAXN=n    largest allowed N, default 11, at most 11)

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
#define MAXN 11
#endif
#ifndef LANES
#define LANES 4
#endif
static_assert(MAXN >= 1 && MAXN <= 11, "MAXN must be in 1..11 (6n^2 <= 768 cells in 12 words)");
static_assert(LANES >= 1 && LANES <= 16, "LANES must be in 1..16");

__extension__ typedef unsigned __int128 u128;

static const char *OUTFILE = "b402226_01.txt";
static const char *LOCKFILE = "b402226_01.txt.lock";
static const size_t MAX_SAVED_BYTES = 16u << 20;
static const size_t MAX_DIGITS = 2000;
static const int MAXKW = 12;     // key words (cells / 64)

[[noreturn]] static void die(const char *msg) {
    std::fprintf(stderr, "402226_01: %s\n", msg);
    std::exit(1);
}
[[noreturn]] static void die_errno(const char *msg) {
    std::fprintf(stderr, "402226_01: %s: %s\n", msg, std::strerror(errno));
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
static BigU pow2(unsigned e) { BigU x; x.d.assign(e / 32 + 1, 0); x.d[e / 32] = 1u << (e % 32); return x; }
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

// ---------------- hash map with per-map key width ----------------
struct Map {
    int kw = 0;                  // key words
    size_t cap = 0, cnt = 0;
    uint64_t *keys = nullptr;    // cap * kw
    uint64_t *vals = nullptr;    // cap * LANES
    unsigned char *used = nullptr;
};
static void map_alloc(Map &m, int kw, size_t cap) {
    if (cap < 16) cap = 16;
    if (cap > SIZE_MAX / (sizeof(uint64_t) * (size_t)(kw + LANES) + 1)) die("hash table too large");
    m.kw = kw; m.cap = cap; m.cnt = 0;
    m.keys = kw ? static_cast<uint64_t *>(std::malloc(cap * (size_t)kw * sizeof(uint64_t))) : nullptr;
    m.vals = static_cast<uint64_t *>(std::malloc(cap * LANES * sizeof(uint64_t)));
    m.used = static_cast<unsigned char *>(std::calloc(cap, 1));
    if ((kw && !m.keys) || !m.vals || !m.used) die("out of memory (try a smaller N)");
}
static void map_free(Map &m) {
    std::free(m.keys); std::free(m.vals); std::free(m.used);
    m.keys = m.vals = nullptr; m.used = nullptr; m.cap = m.cnt = 0;
}
static inline size_t hash_key(const uint64_t *k, int kw, size_t cap) {
    uint64_t h = 0x9E3779B97F4A7C15ULL ^ (uint64_t)kw;
    for (int i = 0; i < kw; i++) { h ^= k[i] + 0x9E3779B97F4A7C15ULL + (h << 6) + (h >> 2); h *= 0xff51afd7ed558ccdULL; h ^= h >> 33; }
    h *= 0xc4ceb9fe1a85ec53ULL; h ^= h >> 33;
    return (size_t)(((u128)h * cap) >> 64);
}
static void map_add(Map &m, const uint64_t *key, const uint64_t *val);
static void map_resize(Map &m, size_t newcap) {
    Map n;
    map_alloc(n, m.kw, newcap);
    for (size_t i = 0; i < m.cap; i++)
        if (m.used[i]) map_add(n, m.keys + i * (size_t)m.kw, m.vals + i * LANES);
    map_free(m);
    m = n;
}
static void map_add(Map &m, const uint64_t *key, const uint64_t *val) {
    if ((m.cnt + 1) * 20 > m.cap * 17) map_resize(m, m.cap + m.cap / 2 + 16);   // load <= 0.85
    const int kw = m.kw;
    size_t h = hash_key(key, kw, m.cap);
    for (;;) {
        if (!m.used[h]) {
            m.used[h] = 1;
            if (kw) std::memcpy(m.keys + h * (size_t)kw, key, sizeof(uint64_t) * (size_t)kw);
            std::memcpy(m.vals + h * LANES, val, sizeof(uint64_t) * LANES);
            m.cnt++;
            return;
        }
        if (kw == 0 || std::memcmp(m.keys + h * (size_t)kw, key, sizeof(uint64_t) * (size_t)kw) == 0) {
            uint64_t *d = m.vals + h * LANES;
            for (int l = 0; l < LANES; l++) { uint64_t s = d[l] + val[l]; if (s >= g_p[l]) s -= g_p[l]; d[l] = s; }
            return;
        }
        if (++h == m.cap) h = 0;
    }
}

struct Tile { uint64_t m[MAXKW]; };
static std::vector<std::vector<Tile>> g_by_first;   // tiles indexed by first cell

static int g_NR;                                   // number of cells in the hexagon

static void build_tiles(int n) {
    const int S = 2 * n;                               // bounding square [0,S]^2
    // cells in units of 1/3: lower-left half (3x+1,3y+1), upper-right half (3x+2,3y+2)
    struct C { int cx, cy; };
    std::vector<C> cells;
    for (int y = S - 1; y >= 0; y--)
        for (int x = 0; x < S; x++) {
            C lo{ 3 * x + 1, 3 * y + 1 }, hi{ 3 * x + 2, 3 * y + 2 };
            for (const C &c : { lo, hi }) {
                int t = c.cx + c.cy;                   // 3(x+y) of the centroid; never 3n or 9n
                if (t == 3 * n || t == 9 * n) die("internal: centroid on the hexagon boundary");
                if (t > 3 * n && t < 9 * n) cells.push_back(c);
            }
        }
    g_NR = (int)cells.size();
    if (g_NR != 6 * n * n) die("internal: number of cells in the hexagon");
    if ((g_NR + 63) / 64 > MAXKW) die("internal: too many cells");
    // map from (cx,cy) to index
    std::vector<int> idx((size_t)(3 * S + 1) * (size_t)(3 * S + 1), -1);
    for (int i = 0; i < g_NR; i++) idx[(size_t)cells[i].cy * (size_t)(3 * S + 1) + (size_t)cells[i].cx] = i;

    std::vector<Tile> all;
    for (int a = 0; a <= S; a++)
        for (int b = 0; b <= S; b++)
            for (int k = 1; a + k <= S && b + k <= S; k++)
                for (int up = 0; up <= 1; up++) {
                    // vertices in units of 1/3
                    long long X[3], Y[3];
                    if (up) { X[0] = 3LL * a; Y[0] = 3LL * b; X[1] = 3LL * (a + k); Y[1] = 3LL * b; X[2] = 3LL * a; Y[2] = 3LL * (b + k); }
                    else    { X[0] = 3LL * (a + k); Y[0] = 3LL * b; X[1] = 3LL * a; Y[1] = 3LL * (b + k); X[2] = 3LL * (a + k); Y[2] = 3LL * (b + k); }
                    Tile T; std::memset(T.m, 0, sizeof T.m);
                    int cnt = 0;
                    bool outside = false;
                    // candidate cells: all unit triangles of the squares in [a,a+k) x [b,b+k)
                    for (int y = b; y < b + k && !outside; y++)
                        for (int x = a; x < a + k && !outside; x++)
                            for (int h = 0; h < 2; h++) {
                                long long px = 3 * x + 1 + h, py = 3 * y + 1 + h;
                                long long d1 = (X[1] - X[0]) * (py - Y[0]) - (Y[1] - Y[0]) * (px - X[0]);
                                long long d2 = (X[2] - X[1]) * (py - Y[1]) - (Y[2] - Y[1]) * (px - X[1]);
                                long long d3 = (X[0] - X[2]) * (py - Y[2]) - (Y[0] - Y[2]) * (px - X[2]);
                                bool in = (d1 > 0 && d2 > 0 && d3 > 0) || (d1 < 0 && d2 < 0 && d3 < 0);
                                bool on = (d1 == 0 && d2 * d3 > 0) || (d2 == 0 && d1 * d3 > 0) || (d3 == 0 && d1 * d2 > 0);
                                if (on) die("internal: centroid on a tile side");
                                if (!in) continue;
                                int i = idx[(size_t)py * (size_t)(3 * S + 1) + (size_t)px];
                                if (i < 0) { outside = true; break; }
                                T.m[i / 64] |= 1ULL << (i % 64); cnt++;
                            }
                    if (outside) continue;
                    if (cnt != k * k) die("internal: tile does not have k^2 cells");
                    all.push_back(T);
                }
    std::sort(all.begin(), all.end(), [](const Tile &p, const Tile &q) { return std::memcmp(p.m, q.m, sizeof p.m) < 0; });
    all.erase(std::unique(all.begin(), all.end(), [](const Tile &p, const Tile &q) { return std::memcmp(p.m, q.m, sizeof p.m) == 0; }), all.end());
    g_by_first.assign(g_NR, {});
    for (auto &T : all) {
        int f = -1;
        for (int w = 0; w < MAXKW && f < 0; w++) if (T.m[w]) f = 64 * w + __builtin_ctzll(T.m[w]);
        g_by_first[f].push_back(T);
    }
}

// relative key of bucket f: bit i <-> cell f+1+i, i < NQ-1-f
static inline int kw_of(int f, int NQ) { int b = NQ - 1 - f; return b > 0 ? (b + 63) / 64 : 0; }

// tiles of first cell f, shifted so that bit i <-> cell f+1+i (cell f itself dropped)
static std::vector<std::vector<Tile>> g_rel;

static void shift_right(const uint64_t *src, int sw, int sh, uint64_t *dst, int dw) {
    // dst = src >> sh (dst has dw words)
    int ws = sh / 64, bs = sh % 64;
    for (int i = 0; i < dw; i++) {
        uint64_t lo = (i + ws < sw) ? src[i + ws] : 0;
        uint64_t hi = (i + ws + 1 < sw) ? src[i + ws + 1] : 0;
        dst[i] = bs ? ((lo >> bs) | (hi << (64 - bs))) : lo;
    }
}

static void prepare_rel(int NQ) {
    g_rel.assign(NQ, {});
    for (int f = 0; f < NQ; f++)
        for (const Tile &T : g_by_first[f]) {
            Tile R; std::memset(R.m, 0, sizeof R.m);
            shift_right(T.m, MAXKW, f + 1, R.m, MAXKW);
            g_rel[f].push_back(R);
        }
}

// one pass: res[l] = a(n) mod g_p[l]
static void run_pass(int NQ, uint64_t *res, bool verbose, int n) {
    std::vector<Map> bucket(NQ + 1);
    for (int f = 0; f <= NQ; f++) bucket[f].kw = kw_of(f, NQ);
    {   // start: nothing covered, first uncovered cell 0
        uint64_t key[MAXKW] = { 0 }, one[LANES];
        for (int l = 0; l < LANES; l++) one[l] = 1 % g_p[l];
        map_alloc(bucket[0], bucket[0].kw, 16);
        map_add(bucket[0], key, one);
    }
    size_t total = 0, live = 1, peak = 1;
    time_t t0 = std::time(nullptr);
    for (int f = 0; f < NQ; f++) {
        Map &B = bucket[f];
        if (B.cap == 0) continue;
        total += B.cnt;
        const int kw = B.kw;
        for (size_t i = 0; i < B.cap; i++) {
            if (!B.used[i]) continue;
            const uint64_t *k = B.keys + i * (size_t)kw;
            const uint64_t *v = B.vals + i * LANES;
            for (const Tile &T : g_rel[f]) {
                bool ok = true;
                for (int w = 0; w < kw; w++) if (k[w] & T.m[w]) { ok = false; break; }
                if (!ok) continue;
                uint64_t u[MAXKW];
                for (int w = 0; w < kw; w++) u[w] = k[w] | T.m[w];
                // first zero of u among the NQ-1-f valid bits
                const int nb = NQ - 1 - f;
                int z = nb;
                for (int w = 0; w < kw; w++) {
                    uint64_t x = ~u[w];
                    if (x) { int p = 64 * w + __builtin_ctzll(x); z = p < nb ? p : nb; break; }
                }
                const int f2 = f + 1 + z;                 // NQ if all covered
                Map &D = bucket[f2];
                uint64_t nk[MAXKW];
                shift_right(u, kw, z + 1, nk, D.kw);      // bit j <-> cell f2+1+j
                if (D.cap == 0) map_alloc(D, D.kw, 64);
                size_t before = D.cnt;
                map_add(D, nk, v);
                live += D.cnt - before;
            }
        }
        live -= B.cnt;
        map_free(B);
        if (live > peak) peak = live;
        if (verbose && (f + 1) % (2 * n) == 0)
            std::fprintf(stderr, "402226_01:   n=%d cells %d/%d, %zu states so far, %zu live, %lds\n",
                         n, f + 1, NQ, total, live, (long)(std::time(nullptr) - t0));
    }
    Map &F = bucket[NQ];
    if (F.cnt != 1) die("internal: final bucket");
    for (size_t i = 0; i < F.cap; i++)
        if (F.used[i]) for (int l = 0; l < LANES; l++) res[l] = F.vals[i * LANES + l];
    map_free(F);
    if (verbose) std::fprintf(stderr, "402226_01:   n=%d: %zu states, peak %zu live\n", n, total, peak);
}

static std::string compute_term(int n) {
    const int NQ = 6 * n * n;
    build_tiles(n);
    if (g_NR != NQ) die("internal: cell count");
    prepare_rel(NQ);
    const unsigned bits = 9u * (unsigned)n * (unsigned)n - 3u * (unsigned)n;          // a(n) <= 2^bits
    BigU bound = pow2(bits);
    std::vector<uint64_t> primes;
    {
        BigU P; P.d = { 1 };
        uint64_t c = (1ULL << 62) - 1;
        while (cmp(P, bound) <= 0) {
            while (!is_prime64(c)) c--;
            primes.push_back(c); mul_u64(P, c); c--;
        }
        while (!is_prime64(c)) c--;
        primes.push_back(c);                                     // check prime
    }
    const size_t np = primes.size(), K = np - 1;
    std::fprintf(stderr, "402226_01: n=%d: %zu prime(s) + 1 check prime, %zu pass(es) (LANES=%d)\n",
                 n, K, (np + LANES - 1) / LANES, LANES);
    std::vector<uint64_t> R(np);
    time_t t0 = std::time(nullptr);
    for (size_t k0 = 0; k0 < np; k0 += LANES) {
        for (int l = 0; l < LANES; l++) g_p[l] = primes[k0 + (size_t)l < np ? k0 + (size_t)l : np - 1];
        uint64_t res[LANES] = { 0 };
        run_pass(NQ, res, k0 == 0, n);
        for (int l = 0; l < LANES && k0 + (size_t)l < np; l++) R[k0 + (size_t)l] = res[l];
        size_t done = k0 + LANES < np ? k0 + LANES : np;
        std::fprintf(stderr, "402226_01: n=%d: primes %zu/%zu done, %lds\n", n, done, np, (long)(std::time(nullptr) - t0));
    }
    // Garner: x = c_0 + c_1 p_0 + c_2 p_0 p_1 + ...
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
        std::fprintf(stderr, "402226_01: check prime mismatch at n=%d; nothing written for this n\n", n);
        std::exit(1);
    }
    if (cmp(x, bound) > 0) die("value exceeds proven bound; nothing written");
    return to_dec(x);
}

// ---------------- arguments and files ----------------
static void usage(FILE *f) {
    std::fprintf(f,
        "usage: 402226_01 N\n"
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
        std::fprintf(stderr, "402226_01: N must satisfy 1 <= N <= %d\n", MAXN);
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
            std::fprintf(stderr, "402226_01: note: ignoring incomplete last line of %s\n", OUTFILE);
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
        std::fprintf(stderr, "402226_01: note: keeping saved lines beyond N=%d (not re-verified)\n", N);

    for (int n = 1; n <= N; n++) {
        std::string v = compute_term(n);
        if ((size_t)n <= vals.size()) {
            if (vals[(size_t)n - 1] != v) {
                std::fprintf(stderr, "402226_01: saved a(%d) = %s but computed %s; file left unchanged\n",
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
