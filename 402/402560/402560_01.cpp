// 402560_01.cpp  --  b-file for OEIS A402560
//
// a(n) = number of tilings of a rhombus with side length n and angles 60 and
//        120 degrees by equilateral triangles of integer side lengths (any
//        sizes, both orientations).
//        1, 4, 33, 1130, 123022, 45392882, 55332456551, ...
//
// Usage:  ./402560_01 N        computes a(1..N); after each n the b-file
//                              b402560_01.txt ("n a(n)") is rewritten atomically
//         ./402560_01 --help
//
// ---------------------------------------------------------------------------
// Coordinates.  The linear map sending the triangular lattice basis (1,0),
// (1/2, sqrt(3)/2) to (1,0), (0,1) maps the rhombus onto the square
// [0,n] x [0,n]; a unit up-triangle becomes the lower-left half and a unit
// down-triangle the upper-right half of a unit square (cut along a line
// x + y = const), and the equilateral triangles of side k become
//      up: (a,b), (a+k,b), (a,b+k)        down: (a+k,b), (a,b+k), (a+k,b+k).
// Rows r = 0..n-1 of unit triangles from the top (row r = strip y = n-1-r);
// in a row, the lower-left half of square (x,y) has position p = 2x and the
// upper-right half p = 2x+1, so every row occupies the positions 0..2n-1.
// An up-triangle of side k with apex at position s of row r occupies
// positions [s, s+2t] of row r+t; a down-triangle whose top row is [s, e]
// (s, e odd) occupies [s+2t, e] of row r+t.
//
// Row slices.  A tiling meets row r in a partition of [0, 2n-1] into
// segments; a segment starting at an even (odd) position is the slice of an
// up- (down-) triangle and has odd length, so the segments alternate.  A row
// is encoded by its cut bits (bit p = 1 iff p and p+1 lie in different
// segments).  A row has at most F(2n) states (compositions of 2n into odd
// parts; F = Fibonacci numbers).
// Row r -> r+1: every up slice [s,e] ends or continues as [s,e+2]; every down
// slice [s,e] with e > s continues as [s+2,e], one with e = s ends; every
// other cell of row r+1 is the apex of a new up-triangle (even position) or
// belongs to the top row of a new down-triangle (odd..odd segment of free
// cells).  Cells outside [0, 2n-1] may not be used.  A tiling is determined
// by its sequence of rows (a continued up slice has length >= 3, so it is not
// a new triangle; down triangles cannot stop early), and every admissible
// sequence whose last row has only down slices of length 1 is a tiling.
// Hence  a(n) <= B(n) := F(2n)^n.
// (Same model as 358715_01.c for the triangle and 402560_01.cpp for the
// hexagon; only the ranges of the rows differ.)
//
// In-place sweep: row r -> r+1 is done position by position q = 0..2n-1 with
// key = new cut bits (< q-1) | old cut bits (>= q-1) | context:
//    typ, cont : old segment containing q-1 (up/down) and whether that up
//                slice continues
//    doff      : offset of q-1 in an old down slice (0, 1, >= 2)
//    ext       : cells still covered by the 2-cell extension of the last
//                continued up slice (0..2)
//    prev      : owner of new cell q-1: A (continued up), B (shrunk down),
//                C (new up apex), NMID (new down, even interior cell: must
//                continue), NODD (new down, odd cell: may end), X (outside)
// New cell q is A if it lies in a continued old up slice or ext > 0, B if it
// is at offset >= 2 of an old down slice, otherwise free (C / new down).  An
// up slice may continue only if ext = 0 at its first cell.  A and B cells
// outside the row make the configuration impossible.  Different A (B)
// triangles are never adjacent, so the new cut bit between q-1 and q is 0 iff
// (A,A), (B,B) or a new down triangle continues.
//
// Values: residues modulo primes p < 2^62, LANES primes per pass, rebuilt by
// CRT (Garner).  The product of the K primes exceeds B(n); one extra prime
// is a check (the rebuilt value must agree with it and be <= B(n), otherwise
// nothing is written).
// Checked: n = 1..6 agree with a Python brute force (exact cover of the unit
// triangles, two cell orders); a(2) = 4 by hand.
// ---------------------------------------------------------------------------
//
// Build:  g++ -O3 -march=native -std=c++17 -Wall -Wextra -Wpedantic -o 402560_01 402560_01.cpp
//         (options: -DLANES=g  primes per pass, default 2 (memory 8 bytes/state each)
//                   -DMAXN=n   largest allowed N, default 24, at most 27)

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
#define MAXN 24
#endif
#ifndef LANES
#define LANES 2
#endif
static_assert(MAXN >= 1 && MAXN <= 27, "MAXN must be in 1..27 (2n-1 cut bits + 9 context bits < 64)");
static_assert(LANES >= 1 && LANES <= 16, "LANES must be in 1..16");

__extension__ typedef unsigned __int128 u128;

static const char *OUTFILE = "b402560_01.txt";
static const char *LOCKFILE = "b402560_01.txt.lock";
static const size_t MAX_SAVED_BYTES = 16u << 20;
static const size_t MAX_DIGITS = 2000;

[[noreturn]] static void die(const char *msg) {
    std::fprintf(stderr, "402560_01: %s\n", msg);
    std::exit(1);
}
[[noreturn]] static void die_errno(const char *msg) {
    std::fprintf(stderr, "402560_01: %s: %s\n", msg, std::strerror(errno));
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

// ---------------- hash map: uint64 key -> LANES residues ----------------
static const uint64_t EMPTY = ~0ULL;     // keys are < 2^63
struct Map {
    size_t cap = 0, cnt = 0;
    uint64_t *keys = nullptr;
    uint64_t *vals = nullptr;
};
static void map_alloc(Map &m, size_t cap) {
    if (cap < 64) cap = 64;
    if (cap > SIZE_MAX / (sizeof(uint64_t) * (1 + LANES))) die("hash table too large");
    m.cap = cap; m.cnt = 0;
    m.keys = static_cast<uint64_t *>(std::malloc(cap * sizeof(uint64_t)));
    m.vals = static_cast<uint64_t *>(std::malloc(cap * LANES * sizeof(uint64_t)));
    if (!m.keys || !m.vals) die("out of memory (try a smaller N or LANES)");
    for (size_t i = 0; i < cap; i++) m.keys[i] = EMPTY;
}
static void map_free(Map &m) { std::free(m.keys); std::free(m.vals); m.keys = m.vals = nullptr; m.cap = m.cnt = 0; }
static inline size_t slot0(uint64_t k, size_t cap) {
    k ^= k >> 33; k *= 0xff51afd7ed558ccdULL; k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ULL; k ^= k >> 33;
    return (size_t)(((u128)k * cap) >> 64);
}
static void map_add(Map &m, uint64_t key, const uint64_t *v);
static void map_resize(Map &m, size_t newcap) {
    Map n;
    map_alloc(n, newcap);
    for (size_t i = 0; i < m.cap; i++) if (m.keys[i] != EMPTY) map_add(n, m.keys[i], m.vals + i * LANES);
    map_free(m);
    m = n;
}
static void map_add(Map &m, uint64_t key, const uint64_t *v) {
    if ((m.cnt + 1) * 5 > m.cap * 4) map_resize(m, m.cap + m.cap / 2 + 64);     // load <= 0.8
    size_t h = slot0(key, m.cap);
    while (m.keys[h] != EMPTY && m.keys[h] != key) { if (++h == m.cap) h = 0; }
    uint64_t *d = m.vals + h * LANES;
    if (m.keys[h] == EMPTY) { m.keys[h] = key; std::memcpy(d, v, LANES * sizeof(uint64_t)); m.cnt++; }
    else for (int l = 0; l < LANES; l++) { uint64_t s = d[l] + v[l]; if (s >= g_p[l]) s -= g_p[l]; d[l] = s; }
}
static void map_clear(Map &m) { for (size_t i = 0; i < m.cap; i++) m.keys[i] = EMPTY; m.cnt = 0; }

// ---------------- rows ----------------
static int g_n, g_P, g_rows;
static void row_range(int r, int &L, int &R) {
    const int n = g_n;
    if (r < 0 || r >= g_rows) { L = 1; R = 0; return; }        // empty
    L = 0; R = 2 * n - 1;                                        // every row of the rhombus
}

enum { U = 0, D = 1 };
enum { P_NONE = 0, P_A, P_B, P_C, P_NMID, P_NODD, P_X };
static const int CTX = 54;
static inline uint64_t pack(uint64_t mask, int typ, int cont, int doff, int ext, int prev) {
    return mask | ((uint64_t)(typ | (cont << 1) | (doff << 2) | (ext << 4) | (prev << 6)) << CTX);
}

// old row r-1 (keys in cur, context 0) -> new row r (result in cur)
static void row_step(Map &cur, Map &nxt, int r) {
    int Lo, Ro, Ln, Rn;
    row_range(r - 1, Lo, Ro);
    row_range(r, Ln, Rn);
    const bool oldrow = Lo <= Ro;
    const int P = g_P;
    for (int q = 0; q < P; q++) {
        map_clear(nxt);
        for (size_t h = 0; h < cur.cap; h++) {
            const uint64_t key = cur.keys[h];
            if (key == EMPTY) continue;
            const uint64_t *v = cur.vals + h * LANES;
            uint64_t mask = key & ((1ULL << CTX) - 1);
            const uint64_t ctx = key >> CTX;
            int typ = (int)(ctx & 1), cont = (int)((ctx >> 1) & 1), doff = (int)((ctx >> 2) & 3);
            int ext = (int)((ctx >> 4) & 3), prev = (int)((ctx >> 6) & 7);

            const bool inOld = oldrow && q >= Lo && q <= Ro;
            bool newseg;
            if (inOld) newseg = (q == Lo) || ((mask >> (q - 1)) & 1);
            else newseg = oldrow && q == Ro + 1;
            if (newseg) {
                if (q > Lo && typ == U && cont) ext = 2;    // a continued up slice ended at q-1
                if (inOld) { typ = (q & 1) ? D : U; doff = 0; cont = 0; }
                else cont = 0;
            } else if (inOld && typ == D && doff < 2) {
                doff++;
            }
            int nc = 1, cl[2] = { cont, 0 };
            if (inOld && newseg && typ == U) { cl[0] = 0; if (ext == 0) { cl[1] = 1; nc = 2; } }
            const bool inNew = q >= Ln && q <= Rn;
            for (int ci = 0; ci < nc; ci++) {
                const int c = cl[ci];
                int e = ext, own;                           // own: P_A, P_B, 0 = free
                if (inOld && typ == U && c) own = P_A;
                else if (e > 0) { own = P_A; e--; }
                else if (inOld && typ == D && doff >= 2) own = P_B;
                else own = 0;
                int no = 0, cuts[2], cls[2];
                if (!inNew) {
                    if (own) continue;                      // a triangle would leave the region
                    if (prev == P_NMID) continue;           // open new down triangle blocked
                    cuts[0] = 1; cls[0] = P_X; no = 1;
                } else if (own) {
                    if (prev == P_NMID) continue;
                    cuts[0] = (prev != own); cls[0] = own; no = 1;
                } else if ((q & 1) == 0) {
                    if (prev == P_NMID) die("internal: NMID before an even cell");
                    cuts[0] = 1; cls[0] = P_C; no = 1;
                    if (prev == P_NODD) { cuts[1] = 0; cls[1] = P_NMID; no = 2; }
                } else {
                    cuts[0] = (prev == P_NMID) ? 0 : 1; cls[0] = P_NODD; no = 1;
                }
                for (int oi = 0; oi < no; oi++) {
                    uint64_t m2 = mask;
                    if (q >= 1) {
                        const uint64_t bit = 1ULL << (q - 1);
                        const bool inside = (q - 1 >= Ln) && (q <= Rn);   // both cells in the new row
                        m2 &= ~bit;
                        if (inside && cuts[oi]) m2 |= bit;
                    }
                    map_add(nxt, pack(m2, typ, c, doff, e, cls[oi]), v);
                }
            }
        }
        std::swap(cur, nxt);
    }
    // end of the row: nothing may be pending
    map_clear(nxt);
    for (size_t h = 0; h < cur.cap; h++) {
        const uint64_t key = cur.keys[h];
        if (key == EMPTY) continue;
        const uint64_t ctx = key >> CTX;
        const int typ = (int)(ctx & 1), cont = (int)((ctx >> 1) & 1);
        const int ext = (int)((ctx >> 4) & 3), prev = (int)((ctx >> 6) & 7);
        if (prev == P_NMID) continue;
        if (ext > 0) continue;
        if (oldrow && Ro == P - 1 && typ == U && cont) continue;
        map_add(nxt, key & ((1ULL << CTX) - 1), cur.vals + h * LANES);
    }
    std::swap(cur, nxt);
}

// row r: every down slice (segment starting at an odd position) has length 1
static bool final_ok(uint64_t mask, int L, int R) {
    int s = L;
    for (int p = L; p <= R; p++) {
        if (p == R || ((mask >> p) & 1)) {
            if ((s & 1) && p != s) return false;
            s = p + 1;
        }
    }
    return true;
}

static void run_pass(Map &cur, Map &nxt, uint64_t *res, bool verbose) {
    map_clear(cur);
    uint64_t one[LANES];
    for (int l = 0; l < LANES; l++) one[l] = 1 % g_p[l];
    map_add(cur, 0, one);                          // virtual empty row above the region
    time_t t0 = std::time(nullptr);
    for (int r = 0; r < g_rows; r++) {
        row_step(cur, nxt, r);
        if (verbose)
            std::fprintf(stderr, "402560_01:   n=%d row %d/%d: %zu states, %lds\n", g_n, r + 1, g_rows, cur.cnt,
                         (long)(std::time(nullptr) - t0));
    }
    int L, R;
    row_range(g_rows - 1, L, R);
    for (int l = 0; l < LANES; l++) res[l] = 0;
    for (size_t h = 0; h < cur.cap; h++)
        if (cur.keys[h] != EMPTY && final_ok(cur.keys[h], L, R))
            for (int l = 0; l < LANES; l++) { uint64_t s = res[l] + cur.vals[h * LANES + l]; if (s >= g_p[l]) s -= g_p[l]; res[l] = s; }
}

static std::string compute_term(int n) {
    g_n = n;
    g_P = 2 * n;                                   // positions 0..P-1
    g_rows = n;
    if (g_P - 1 > CTX) die("internal: too many positions");
    // bound B(n) = prod over rows of F(row length)
    std::vector<uint64_t> F(80, 0);
    F[1] = 1; F[2] = 1;
    for (size_t k = 3; k < F.size(); k++) F[k] = F[k - 1] + F[k - 2];
    BigU bound; bound.d = { 1 };
    for (int r = 0; r < g_rows; r++) {
        int L, R; row_range(r, L, R);
        mul_u64(bound, F[(size_t)(R - L + 1)]);
    }
    std::vector<uint64_t> primes;
    {
        BigU Pp; Pp.d = { 1 };
        uint64_t c = (1ULL << 62) - 1;
        while (cmp(Pp, bound) <= 0) {
            while (!is_prime64(c)) c--;
            primes.push_back(c); mul_u64(Pp, c); c--;
        }
        while (!is_prime64(c)) c--;
        primes.push_back(c);                       // check prime
    }
    const size_t np = primes.size(), K = np - 1;
    std::fprintf(stderr, "402560_01: n=%d: %zu prime(s) + 1 check prime, %zu pass(es) (LANES=%d)\n",
                 n, K, (np + LANES - 1) / LANES, LANES);
    Map cur, nxt;
    map_alloc(cur, 1024);
    map_alloc(nxt, 1024);
    std::vector<uint64_t> Rv(np);
    time_t t0 = std::time(nullptr);
    for (size_t k0 = 0; k0 < np; k0 += LANES) {
        for (int l = 0; l < LANES; l++) g_p[l] = primes[k0 + (size_t)l < np ? k0 + (size_t)l : np - 1];
        uint64_t res[LANES] = { 0 };
        run_pass(cur, nxt, res, k0 == 0);
        for (int l = 0; l < LANES && k0 + (size_t)l < np; l++) Rv[k0 + (size_t)l] = res[l];
        size_t done = k0 + LANES < np ? k0 + LANES : np;
        std::fprintf(stderr, "402560_01: n=%d: primes %zu/%zu done, %lds\n", n, done, np, (long)(std::time(nullptr) - t0));
    }
    map_free(cur); map_free(nxt);
    std::vector<uint64_t> c(K);
    for (size_t j = 0; j < K; j++) {
        const uint64_t pj = primes[j];
        uint64_t v = 0, prod = 1;
        for (size_t t = 0; t < j; t++) {
            v = (v + mulmod(c[t] % pj, prod, pj)) % pj;
            prod = mulmod(prod, primes[t] % pj, pj);
        }
        uint64_t diff = (Rv[j] % pj + pj - v) % pj;
        c[j] = mulmod(diff, powmod(prod, pj - 2, pj), pj);
    }
    BigU x;
    for (size_t j = K; j-- > 0;) { mul_u64(x, primes[j]); add_u64(x, c[j]); }
    if (mod_u64(x, primes[K]) != Rv[K]) {
        std::fprintf(stderr, "402560_01: check prime mismatch at n=%d; nothing written for this n\n", n);
        std::exit(1);
    }
    if (cmp(x, bound) > 0) die("value exceeds proven bound; nothing written");
    return to_dec(x);
}

// ---------------- arguments and files ----------------
static void usage(FILE *f) {
    std::fprintf(f,
        "usage: 402560_01 N\n"
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
        std::fprintf(stderr, "402560_01: N must satisfy 1 <= N <= %d\n", MAXN);
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
            std::fprintf(stderr, "402560_01: note: ignoring incomplete last line of %s\n", OUTFILE);
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
        std::fprintf(stderr, "402560_01: note: keeping saved lines beyond N=%d (not re-verified)\n", N);

    for (int n = 1; n <= N; n++) {
        std::string v = compute_term(n);
        if ((size_t)n <= vals.size()) {
            if (vals[(size_t)n - 1] != v) {
                std::fprintf(stderr, "402560_01: saved a(%d) = %s but computed %s; file left unchanged\n",
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
