// A400958: a(n) = sum_{i=1..10^n} mu(i)*mu(i+1).
// Default: n=0..13. All results are computed from scratch (or local checkpoint).
// Standalone C++17 source: no local headers or source files are needed.
// macOS (Apple Silicon, Homebrew libomp):
// clang++ -O3 -std=c++17 -march=native -frounding-math -fno-strict-overflow -Wall -Wextra -Xpreprocessor -fopenmp -I/opt/homebrew/opt/libomp/include 400958_01.cpp -L/opt/homebrew/opt/libomp/lib -lomp -o 400958_01
// Linux: g++ -O3 -std=c++17 -march=native -fopenmp -frounding-math -fno-strict-overflow -Wall -Wextra 400958_01.cpp -o 400958_01
// Run: ./400958_01 --max-n 13
// Resume: repeat the same command; completed rows are reprinted to stdout.
// Progress goes to stderr. See --help and 400958_01.md.
//
// The sieve below is amalgamated from Greg Hurst's mertens project:
// https://github.com/greg-hurst/mertens
// Revision db5ef945cc64ff8df4feaff3d3d210c487f67b74.
// Local #include directives and #pragma once were removed.
// Warning-only edits: initializer order and [[maybe_unused]] annotations.
// The A400958 CLI/checkpoint driver follows the sieve implementation.
/*
MIT License

Copyright (c) 2026 Greg Hurst

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/

// BEGIN upstream types.h
// ============================================================================
// types.h — Fundamental type aliases, enums, and constants for the Mertens
//           function computation.
// ============================================================================

#include <cstdint>

using UInt128 = unsigned __int128;
using Int128  = __int128_t;

using UInt64 = uint64_t;
using Int64  = int64_t;

using UInt32 = uint32_t;
using Int32  = int32_t;

using UInt16 = uint16_t;
using Int16  = int16_t;

using UInt8 = uint8_t;
using Int8  = int8_t;

// Controls which parity of summation indices to include in S2 updates.
enum class ParityMode : UInt8 { All, Even, Odd };

// END upstream types.h

// BEGIN upstream simd_defs.h
// ============================================================================
// simd_defs.h — SIMD platform detection for the segmented Mertens/Mobius sieve.
//
// Detection hierarchy (first match wins, supersets also define their subsets):
//
//   ARM:
//     SIEVE_SIMD_SVE2  — ARM SVE2 (Graviton 3+, Neoverse V1+)
//     SIEVE_SIMD_NEON  — ARM NEON (Apple Silicon, AArch64, ARMv7+NEON)
//
//   x86:
//     SIEVE_SIMD_AVX512 — AVX-512BW (Skylake-X 2017+, Zen 4 2022+)
//     SIEVE_SIMD_AVX2   — AVX2 (Haswell 2013+, Zen 2017+)
//     SIEVE_SIMD_SSE    — SSE2 (baseline for all x86-64)
//
// When a wider tier is detected, all narrower tiers on the same architecture
// are also defined. This lets code that only needs 128-bit ops (e.g. prefix
// sum) test for SIEVE_SIMD_SSE or SIEVE_SIMD_NEON without caring about the
// exact tier.
//
// If nothing matches, no macros are defined and plain scalar C++ is used.
// ============================================================================

// --- ARM ---
#if defined(__ARM_FEATURE_SVE2)
    #define SIEVE_SIMD_SVE2 1
    #define SIEVE_SIMD_NEON 1      // SVE2 implies NEON on AArch64
    #include <arm_sve.h>
    #include <arm_neon.h>

#elif defined(__ARM_NEON) || defined(__ARM_NEON__)
    #define SIEVE_SIMD_NEON 1
    #include <arm_neon.h>

// --- x86 ---
#elif defined(__AVX512BW__)
    #define SIEVE_SIMD_AVX512 1
    #define SIEVE_SIMD_AVX2   1    // AVX-512 implies AVX2
    #define SIEVE_SIMD_SSE    1
    #include <immintrin.h>

#elif defined(__AVX2__)
    #define SIEVE_SIMD_AVX2 1
    #define SIEVE_SIMD_SSE  1      // AVX2 implies SSE2
    #include <immintrin.h>

#elif defined(__SSE2__) || (defined(_MSC_VER) && (defined(_M_X64) || defined(_M_AMD64)))
    #define SIEVE_SIMD_SSE 1
    #include <emmintrin.h>
    #if defined(__SSSE3__)
        #include <tmmintrin.h>   // pshufb, used for the prefix-sum carry broadcast
    #endif
#endif

// END upstream simd_defs.h

// BEGIN upstream QuotientCache.h
// ============================================================================
// QuotientCache.h — Quotients via precomputed magic multipliers (Granlund & Montgomery).
//
// Replaces floor(n / d) with a single 128-bit multiply + shifts, avoiding
// the expensive hardware division instruction (especially on Intel where
// 64-bit div is ~30-90 cycles vs ~5-7 for 128-bit mul).
//
// For each divisor d in [1, B], we precompute:
//   lg[d]  = ceil(log2(d+1))  (tracked via a doubling counter)
//   m[d]   = ceil(((2^lg - d) << SHIFT) / d)
//
// Then:  floor(n / d) = (n + (m[d-1] * (uint128)n) >> SHIFT) >> lg[d-1]
//
// Domain: with SHIFT = 60 the multiply-shift identity is exact only for
// arguments below 2^60. Callers must keep n (and ceilDiv's n + p - 1)
// under that bound; the Mobius sieve asserts this at its entry point.
//
// Two cache types:
//   QuotientCache      — covers a contiguous range [1..B] of divisors
//   SieveQuotientCache — covers only the primes (indexed by prime index)
//
// Compile-time control:
//   -DUSE_DIVISION_FREE=1  enables division-free quotient methods (default on x86)
//   -DUSE_DIVISION_FREE=0  uses direct hardware division (default on ARM)
// ============================================================================

#include <cstdlib>
#include <vector>

#ifndef USE_DIVISION_FREE
#define USE_DIVISION_FREE 0
#endif
static constexpr bool UseDivisionFree = USE_DIVISION_FREE;

// ============================================================================
// QuotientCache: contiguous divisor range [1..B]
//
// Used in S1/S2 to replace n/x for x <= cbrt(2n).
// ============================================================================

struct QuotientCache {
    static constexpr int SHIFT = 60;

    UInt8*  lgs   = nullptr;
    UInt64* ms    = nullptr;
    UInt32  count = 0;

    QuotientCache() = default;
    QuotientCache(const QuotientCache&) = delete;
    QuotientCache& operator=(const QuotientCache&) = delete;

    ~QuotientCache() {
        std::free(lgs);
        std::free(ms);
    }

    void init(UInt32 B) {
        std::free(lgs);
        std::free(ms);
        count = B;
        lgs = static_cast<UInt8*>(std::calloc(B, sizeof(UInt8)));
        ms  = static_cast<UInt64*>(std::calloc(B, sizeof(UInt64)));

        // d = 1: lg = 0
        UInt8 lg = 0;
        lgs[0] = lg;
        __uint128_t diff = (1ULL << lg) - 1;
        ms[0] = static_cast<UInt64>(diff << SHIFT) + 1;

        // d = 2..B: lg tracks ceil(log2(d+1)) via doubling
        lg = 1;
        UInt64 lgat = 0, lgtarget = 1;
        for (UInt64 i = 1; i < B; ++i) {
            lgs[i] = lg;
            __uint128_t diff2 = (1ULL << lg) - i - 1;
            ms[i] = static_cast<UInt64>((diff2 << SHIFT) / (i + 1)) + 1;
            lgat++;
            if (lgat == lgtarget) {
                lgat = 0;
                lgtarget <<= 1;
                lg++;
            }
        }
    }

    // floor(n / d) for 1 <= d <= count, using 128-bit multiply + shift.
    inline UInt64 quotient(UInt64 n, UInt64 d) const {
        return (n + static_cast<UInt64>(
            (static_cast<__uint128_t>(ms[d - 1]) * static_cast<__uint128_t>(n)) >> SHIFT
        )) >> lgs[d - 1];
    }
};

// ============================================================================
// SieveQuotientCache: magic multipliers indexed by prime index.
//
// Used in the Mobius sieve to replace ceil(lo / p) for each prime p.
// The shift amount is computed on-the-fly via __builtin_clzll (1 cycle).
// ============================================================================

struct SieveQuotientCache {
    static constexpr int SHIFT = 60;

    UInt64* ms    = nullptr;
    UInt32  count = 0;

    SieveQuotientCache() = default;
    SieveQuotientCache(const SieveQuotientCache&) = delete;
    SieveQuotientCache& operator=(const SieveQuotientCache&) = delete;

    ~SieveQuotientCache() {
        std::free(ms);
    }

    void init(const UInt32* primes, UInt32 numPrimes) {
        std::free(ms);
        count = numPrimes;
        ms = static_cast<UInt64*>(std::calloc(count, sizeof(UInt64)));

        // Each (diff << SHIFT) / p is a 128-bit division (__udivti3 on
        // x86-64, ~50-100 cycles). Iterations are independent, and at large
        // sieve ranges there are millions of primes — parallelize rather
        // than pay ~a second of serial setup.
        #pragma omp parallel for schedule(static)
        for (UInt32 i = 0; i < count; ++i) {
            UInt64 p = primes[i];
            UInt8 l = static_cast<UInt8>(64 - __builtin_clzll(p));
            __uint128_t diff = (1ULL << l) - p;
            ms[i] = static_cast<UInt64>((diff << SHIFT) / p) + 1;
        }
    }

    // ceil(lo / p) where primeIdx is the index into the primes array.
    // Equivalent to (lo + p - 1) / p but division-free.
    inline UInt64 ceilDiv(UInt64 lo, UInt32 primeIdx, UInt64 p) const {
        UInt8 slg = static_cast<UInt8>(64 - __builtin_clzll(p));
        UInt64 val = lo + p - 1;
        return (val + static_cast<UInt64>(
            (static_cast<__uint128_t>(ms[primeIdx]) * static_cast<__uint128_t>(val)) >> SHIFT
        )) >> slg;
    }
};

// END upstream QuotientCache.h

// BEGIN upstream SegmentedMobiusSieve.h
// ============================================================================
// SegmentedMobiusSieve.h — Segmented sieve of the Mobius function mu(n).
//
// Computes mu(k) for k in [lo, hi] using a three-phase approach:
//   Phase 1: Initialize M1 chunks with stencil, small primes, and M1 medium primes
//   Phase 2: Apply the remaining medium primes via tiled direct sieving
//   Phase 3: Apply large primes via a bucket scheduler
//
// Prime-range terminology:
//   stencil primes:  p <= 11
//   small primes:    13 <= p <= 353
//   M1 medium primes: 359 <= p <= M1_PRIME_CAP
//   M1-stage primes: collectively, p <= M1_PRIME_CAP
//   tiled medium primes: M1_PRIME_CAP < p <= the direct-sieve cutoff
//   large primes: p > the direct-sieve cutoff
//
// The sieve buffer stores packed Int8 values during sieving. A finalization
// step (finalizeMuVec when SIMD is available) converts these to actual mu ∈ {-1, 0, +1}.
//
// Arbitrary intervals [lo, hi] are supported — no alignment constraints.
//
// The prime list passed to sieve() must contain at least 71 entries (primes
// up to >= 353) due to the hardcoded sieveM1PrimeRange unrolling. Use
// primesUpTo(std::max(360u, sqrt_hi)) to guarantee this.
// ============================================================================

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <utility>
#include <vector>

class SegmentedMobiusSieveCore {
public:
    // --- Constants ---
    static constexpr UInt64 STENCIL_PERIOD = 13860;  // LCM(4, 9, 5, 7, 11)
    static constexpr UInt32 MIN_PRIMES_BOUND = 360;  // primesUpTo must include at least this

    // --- Construction ---
    SegmentedMobiusSieveCore();
    explicit SegmentedMobiusSieveCore(UInt64 segmentSize);

    // --- Setup ---

    // Resize buffers and prepare the pre-sieved stencil for the given segment size.
    void initialize(UInt64 segmentSize);

    // --- Sieving ---

    // Sieve mu over [lo, hi] using the given primes list.
    // After this call, operator[](k - lo) == mu(k) for k in [lo, hi].
    // Requires: primes.size() >= 71 (primes up to at least 353).
    //
    // Finalize (compile-time, default true): when true the packed sieve bytes
    // are converted to mu in {-1,0,+1} before returning (the normal path). When
    // false, finalization is skipped and the buffer is left holding the raw
    // packed log-prime sums; the caller must finalize (e.g. the fused
    // finalize+prefix scan in SegmentedMertensSieve). Both instantiations are
    // explicitly emitted in the .cpp.
    template<bool Finalize = true>
    void sieve(UInt64 lo, UInt64 hi, const std::vector<UInt32>& primes);

    // Fill the buffer with the stencil pattern (for Loop 2's large segments).
    // Fills the first `size` bytes of the mu buffer with repeating stencil data.
    void fillFromStencil(UInt64 size);

    // --- Access ---

    // mu at relative index i (0-based from the last sieve's lo).
    Int8 operator[](UInt64 i) const { return mMu[i]; }

    // Raw pointer access to the sieve buffer.
    const Int8* data() const { return mMu.data(); }
    Int8* data()             { return mMu.data(); }

    UInt64 capacity() const  { return mMu.size(); }

    // --- Utility ---

    // Generate all primes up to n using a simple sieve of Eratosthenes.
    // For use with sieve(), pass at least primesUpTo(max(MIN_PRIMES_BOUND, sqrt(hi))).
    static std::vector<UInt32> primesUpTo(UInt32 n);

    // Largest prime the bucket scheduler can reach ((LP_SIZE - 1) * M2).
    // When the bucket scheduler is enabled, the sieve endpoint must satisfy
    // sqrt(u) <= schedulerReach() — see MertensHurst/INPUT_BOUNDS.md.
    static constexpr UInt64 schedulerReach() {
        return (LargePrimeHitScheduler::LP_SIZE - 1) * M2;
    }

private:
    // Odd-valued ceil-log2 weight stored for each odd prime factor in the
    // packed sieve. Requires odd prime p. Keep synchronized with the stencil.
    static inline Int8 primeLogWeight(UInt32 p) noexcept {
        return static_cast<Int8>((32 - __builtin_clz(p)) | 1U);
    }

    // Precompute Granlund-Montgomery magic multipliers for the given prime list.
    // Auto-called by sieve() on first use when USE_DIVISION_FREE=1.
    void initSieveQuotientCache(const std::vector<UInt32>& primes);

    // --- Sieve phases ---

    // M1 stage: stencil + hardcoded small primes + M1 medium primes
    void sieveM1Primes(Int8* mu, const UInt32* primes, UInt64 lo, UInt64 hi);

    // Finalization: convert packed sieve values to mu ∈ {-1, 0, +1}
    void finalizeMu(Int8* mu, UInt64 lo, UInt64 hi);

    // Vectorized finalization over a constant-floor(log2 N) run, threshold fl.
#if SIEVE_SIMD_NEON || SIEVE_SIMD_SSE
    static void finalizeMuVec(Int8* mu, int fl, size_t n);
#endif

    // Apply hardcoded small primes 13..353, then M1 medium primes using
    // constant-stride and four-stream kernels.
    static void sieveM1PrimeRange(Int8* mu, const UInt32* primes, UInt64 lo, UInt64 hi,
                                  UInt32 stoppos, const SieveQuotientCache* cache);

    // Zero p^2 multiples for primes[fromIdx..toIdx) over the whole segment.
    // For p >= 359 (index 71+), p^2 exceeds every sub-segment length, so squares are
    // handled once per segment instead of per sub-segment.
    static void sieveSquaresPass(Int8* mu, const UInt32* primes, UInt64 lo, UInt64 hi,
                                 UInt32 fromIdx, UInt32 toIdx,
                                 const SieveQuotientCache* cache);

    // Apply medium-range primes to a sub-segment
    static void sieveMediumSubSegment(Int8* mu, const UInt32* primes, UInt64 lo, UInt64 hi,
                                      UInt64 fromIdx, UInt64 toIdx,
                                      const SieveQuotientCache* cache);

    // Apply medium primes while carrying each prime's next-hit offset across
    // a contiguous run of M2 sub-segments.
    static void sieveMediumSubSegmentRolling(Int8* mu, const UInt32* primes, UInt64 len,
                                             UInt64 fromIdx, UInt64 toIdx,
                                             std::vector<UInt32>& nextOff);

    // --- Bucket sieve for large primes ---
    struct LargePrimeHitScheduler {
        // Bucket entry layout (-DSIEVE_NARROW_ENTRY=0|1):
        //   narrow (default): the entry IS the prime (UInt32). The offset is
        //     recomputed per sub-segment by one divide, the log weight by CLZ.
        //     Half the persistent entry-stream footprint. Current hits are
        //     transiently grouped into cache-sized offset bands before their
        //     mu updates. Wins in the bandwidth-bound many-core regime.
        //   wide: self-contained 64-bit entry — bits 0..20 off, 21..41 p mod
        //     M2, 42..51 p / M2, 52..57 log weight. Forwarding is a branchless
        //     Bresenham step: cheapest per hit, but the 8-byte entry stream
        //     saturates memory bandwidth at scale. Machine-specific — on x86
        //     re-measure before trusting the default. See PERFORMANCE.md.
#ifndef SIEVE_NARROW_ENTRY
#define SIEVE_NARROW_ENTRY 1
#endif
#if SIEVE_NARROW_ENTRY
        using EntryT = UInt32;   // narrow: prime only, divide per hit (default)
#else
        using EntryT = UInt64;   // wide: packed, divide-free
#endif
        static constexpr int    LP_OFF_BITS  = 21;
        static constexpr UInt64 LP_OFF_MASK  = (UInt64(1) << LP_OFF_BITS) - 1;
        static constexpr int    LP_R_SHIFT   = 21;
        static constexpr int    LP_S_SHIFT   = 42;
        static constexpr UInt64 LP_S_MASK    = (UInt64(1) << 10) - 1;
        static constexpr int    LP_LOG_SHIFT = 52;

        using PVecT = std::vector<EntryT>;        // bucket storage
        using PrimesVecT = std::vector<UInt32>;   // the prime list

        // Full constructor: initializes bookkeeping AND scans all large primes
        // to populate buckets with first hits.
        LargePrimeHitScheduler(
            const UInt64& baseLo,
            const UInt64& lo,
            const UInt64& hi,
            const UInt64& subSegmentLen,
            const PrimesVecT& primes,
            const UInt32& pInd0,
            const UInt32& pInd1,
            std::vector<PVecT>& lpBucket,
            const SieveQuotientCache* cache
        );

        // Pre-populated constructor: initializes bookkeeping only.
        // Assumes buckets have already been populated by an external routing pass.
        struct PrePopulated {};
        LargePrimeHitScheduler(
            PrePopulated,
            const UInt64& baseLo,
            const UInt64& lo,
            const UInt64& hi,
            const UInt64& subSegmentLen,
            const PrimesVecT& primes,
            const UInt32& pInd0,
            const UInt32& pInd1,
            std::vector<PVecT>& lpBucket,
            const SieveQuotientCache* cache
        );

        UInt64 subSegLo(const UInt64& subSegIndex) const noexcept;
        UInt64 subSegIndexOf(const UInt64& x) const noexcept;
        bool emptySubSegment(const UInt64& subSeg) const noexcept;
        void bucketPush(const UInt64& subSeg, EntryT e) noexcept;
        static UInt64 skipStencilSquare4(UInt64 m, UInt64 p) noexcept;
        // Pack (p, first-hit offset) into the entry layout above. Seed-time
        // only — the per-hit path forwards entries without repacking from p.
        static EntryT packEntry(UInt32 p, UInt64 off) noexcept;
        void sieveSubSegment(Int8* __restrict muBase) noexcept;
        template<bool AllSkipsFit>
        void sieveSubSegmentImpl(Int8* __restrict muBase) noexcept;

        // Number of buckets in the circular buffer. Must be a power of 2
        // because bucket indexing uses (subSeg & (LP_SIZE - 1)) as a fast
        // modulo, and at least 2 because schedulerReach() subtracts one bucket.
        //
        // LP_SIZE bounds the largest schedulable prime to
        // (LP_SIZE - 1) * M2, so 512 covers u up to ~2.05e17. The wide entry's
        // 10-bit stride field supports LP_SIZE up to exactly 1024, and doubling
        // it is performance-neutral. 512 is the record-run configuration; see
        // PERFORMANCE.md section 6 and Section 7 of the paper.
#ifndef SIEVE_LP_SIZE
#define SIEVE_LP_SIZE 512
#endif
        static constexpr UInt64 LP_SIZE = SIEVE_LP_SIZE;
        static_assert(LP_SIZE >= 2 && (LP_SIZE & (LP_SIZE - 1)) == 0,
                      "LP_SIZE must be a power of two of at least 2");
        static_assert(LP_SIZE <= LP_S_MASK + 1,
                      "stride field must hold p / M2 for the largest schedulable prime");

        // Offset bands (default ON; disable with -DSIEVE_SUB_BUCKETS=0) keep
        // the mu RMW lines cache-local. Wide entries store their offset, so
        // the persistent ring itself is split into LP_SUBS bands. Narrow
        // entries remain prime-only in the ring and transiently group only
        // the current sub-segment's decoded hits below.
#ifndef SIEVE_SUB_BUCKETS
#define SIEVE_SUB_BUCKETS 1
#endif
#if SIEVE_SUB_BUCKETS && !SIEVE_NARROW_ENTRY
#ifndef SIEVE_SUB_SHIFT
#define SIEVE_SUB_SHIFT 17
#endif
        static constexpr int    LP_SUB_SHIFT = SIEVE_SUB_SHIFT;  // off >> shift selects the sub
        // 2^(LP_OFF_BITS - shift) covers every possible offset for any M2.
        static constexpr UInt64 LP_SUBS = UInt64(1) << (LP_OFF_BITS - LP_SUB_SHIFT);
#define SIEVE_SUBS_ACTIVE 1
#else
        static constexpr UInt64 LP_SUBS = 1;
#define SIEVE_SUBS_ACTIVE 0
#endif
        static constexpr UInt64 LP_NBUCKETS = LP_SIZE * LP_SUBS;

        // Narrow entries cannot be persistently offset-banded without growing
        // beyond four bytes. Materialize the current hit as (offset, log
        // weight) instead, then apply those hits in cache-sized bands. The
        // transient vectors retain their capacity between sub-segments.
#if SIEVE_SUB_BUCKETS && SIEVE_NARROW_ENTRY
#ifndef SIEVE_NARROW_SUB_SHIFT
#define SIEVE_NARROW_SUB_SHIFT 16
#endif
        static_assert(SIEVE_NARROW_SUB_SHIFT > 0
                   && SIEVE_NARROW_SUB_SHIFT <= LP_OFF_BITS,
                      "narrow sub-bucket shift must fit the offset field");
        static constexpr int LP_TRANSIENT_SHIFT = SIEVE_NARROW_SUB_SHIFT;
        static constexpr UInt64 LP_TRANSIENT_SUBS =
            UInt64(1) << (LP_OFF_BITS - LP_TRANSIENT_SHIFT);
        using TransientHitVecT = std::vector<UInt32>;
#define SIEVE_NARROW_SUBS_ACTIVE 1
#else
#define SIEVE_NARROW_SUBS_ACTIVE 0
#endif

        // Ring slot for an entry headed to `subSeg` (sub-bucket from its offset).
        static UInt64 ringIndex(const UInt64& subSeg, EntryT e) noexcept;

        const UInt64 mBaseLo, mLo, mHi, mSubSegmentLen;
        const UInt64 mFinalSubSegIndex;
        UInt64 mCurrentSubSegIndex;
        const UInt32* mP;
        const UInt32 mPInd0, mPInd1;
        const bool mAllSkipsFit;
        std::vector<PVecT>& mBuckets;
#if SIEVE_NARROW_SUBS_ACTIVE
        std::array<TransientHitVecT, LP_TRANSIENT_SUBS> mTransientHits;
#endif
        const SieveQuotientCache* mCache;
    };

    // --- Internal constants for chunk sizes ---
    // Must be multiples of STENCIL_PERIOD for memcpy alignment.
    // M1 ~ L1 cache, M2 ~ L2 cache, M3 = bucket sieve cutoff.
    // M2/M3 multipliers are build-time tunable (keep M3 ~ 1.4x M2):
    //   -DSIEVE_M2_MULT=8 -DSIEVE_M3_MULT=12 gives an L1-sized sub-segment.
    // NOTE: shrinking M2 shrinks the scheduler capacity (LP_SIZE - 1) * M2 and
    // grows the per-entry stride field s = p / M2 — check both limits
    // (LP_S_MASK and the LP_SIZE comment) before production use.
#ifndef SIEVE_M1_MULT
#define SIEVE_M1_MULT 8
#endif
    static constexpr UInt64 M1 = SIEVE_M1_MULT * STENCIL_PERIOD;   // ~111K — Phase 1 unit
#ifndef SIEVE_M2_MULT
#define SIEVE_M2_MULT 64
#endif
#ifndef SIEVE_M3_MULT
#define SIEVE_M3_MULT 90
#endif
    static constexpr UInt64 M2 = SIEVE_M2_MULT * STENCIL_PERIOD;   // ~887K default
    static_assert(M2 <= (UInt64(1) << LargePrimeHitScheduler::LP_OFF_BITS),
                  "sub-segment offset must fit in LP_OFF_BITS; raise LP_OFF_BITS if M2 grows");
    static constexpr UInt64 M3 = SIEVE_M3_MULT * STENCIL_PERIOD;   // optional block-walk direct cutoff
    static constexpr UInt64 BLOCK_SEGMENTS = 128;                  // contiguous M2 work unit
    static constexpr UInt64 BLOCK_WALK_MIN_SEGMENTS = 4096;        // ~3.6 billion values
    static_assert(M3 > M2, "large primes must exceed the sub-segment length (<= 1 hit per sub-segment)");
    // M1 medium primes through this boundary use the four-stream M1 walk;
    // larger primes use the wider medium tiles. This need not match the
    // stencil period and can be retuned independently for another machine.
#ifndef SIEVE_M1_PRIME_CAP
#define SIEVE_M1_PRIME_CAP 32000
#endif
    static constexpr UInt64 M1_PRIME_CAP = SIEVE_M1_PRIME_CAP;
    static_assert(M1_PRIME_CAP >= 353,
                  "M1-prime cap must include the fully unrolled small primes through 353");

    // M1 medium primes through this boundary use compile-time constant-stride
    // loops; the remaining M1 medium primes use the four-stream walk. The
    // default is tuned for Apple M3 Ultra. Values through 2,039 are available
    // for compile-time retuning on other machines.
#ifndef SIEVE_M1_CONSTANT_PRIME_CAP
#define SIEVE_M1_CONSTANT_PRIME_CAP 1021
#endif
    static constexpr UInt64 M1_CONSTANT_PRIME_CAP = SIEVE_M1_CONSTANT_PRIME_CAP;
    static_assert(M1_CONSTANT_PRIME_CAP >= 353 && M1_CONSTANT_PRIME_CAP <= 2039,
                  "constant-prime cap must be between 353 and 2,039");
    static_assert(M1_CONSTANT_PRIME_CAP <= M1_PRIME_CAP,
                  "constant-prime cap cannot exceed the M1-prime cap");

    // --- Data members ---
    std::vector<Int8> mMu;           // Main sieve buffer
    std::vector<Int8> mPreMu;        // Pre-sieved buffer (M1-sized, stencil copies)
    std::vector<Int8> mStencilData;  // The base stencil pattern (STENCIL_PERIOD entries)

    // Per-thread bucket storage for the large prime scheduler
    std::vector<std::vector<LargePrimeHitScheduler::PVecT>> mBuckets;

    // Index tracking for incremental prime range updates
    UInt32 mM1PrimeStopIdx;
    UInt32 mSqrtPrimeStopIdx;

    // Granlund-Montgomery quotient cache for prime offsets
    SieveQuotientCache mSieveQCache;

};

// ============================================================================
// SegmentedMobiusSieve — Iterator-style wrapper over SegmentedMobiusSieveCore.
//
// Construct with a segment size. Call next() to advance one segment at a time,
// starting from 1. Primes are grown automatically as needed.
//
// After each next() call:
//   getMobius(pos)         — look up mu(pos) within the current segment
//   getSegmentValues()     — all mu values in the current segment as Int8
//   getSegmentData()       — zero-copy pointer to the mu values
//   lo(), hi()             — current segment bounds
//   nextSegment()          — bounds of the upcoming segment
// ============================================================================

class SegmentedMobiusSieve {
public:
    explicit SegmentedMobiusSieve(UInt64 segmentSize)
        : mSegSize(segmentSize)
    {
        mCore.initialize(mSegSize);
    }

    // Advance to the next segment. Returns true if a segment was produced.
    bool next() {
        mLo = mNextLo;
        mHi = mLo + mSegSize - 1;

        growPrimes(mHi);
        mCore.sieve(mLo, mHi, mPrimes);
        mNextLo = mHi + 1;
        return true;
    }

    // Look up mu(pos) within the current segment. pos is absolute.
    Int8 getMobius(UInt64 pos) const {
        return mCore[pos - mLo];
    }

    // Fill vals with all mu values in the current segment.
    // Resizes vals if needed. Caller can reuse the same vector across segments.
    // The copy costs a full pass over the segment — in hot loops prefer
    // getSegmentData(), which is free.
    void getSegmentValues(std::vector<Int8>& vals) const {
        if ((UInt64)vals.size() < mSegSize) vals.resize(mSegSize);

        const Int8* src = mCore.data();
        #pragma omp parallel for schedule(static)
        for (UInt64 i = 0; i < mSegSize; ++i) {
            vals[i] = src[i];
        }
    }

    // Zero-copy access to the mu values in the current segment. Returns a
    // pointer to the core's existing buffer — nothing is copied. Valid until
    // the next next() call. getSegmentData()[i] = mu(lo() + i).
    const Int8* getSegmentData() const {
        return mCore.data();
    }

    UInt64 lo() const { return mLo; }
    UInt64 hi() const { return mHi; }

    // Inclusive bounds of the segment the next call to next() will sieve.
    std::pair<UInt64, UInt64> nextSegment() const {
        return {mNextLo, mNextLo + mSegSize - 1};
    }

    // Access the underlying core sieve.
    SegmentedMobiusSieveCore& core() { return mCore; }

private:
    void growPrimes(UInt64 hi) {
        UInt32 need = (UInt32)std::max((Int64)SegmentedMobiusSieveCore::MIN_PRIMES_BOUND,
                                       (Int64)std::round(std::sqrt((double)hi)));
        if (need > mPrimeBound) {
            UInt32 bound = std::max(need, mPrimeBound * 2);
            mPrimes = SegmentedMobiusSieveCore::primesUpTo(bound);
            mPrimeBound = bound;
        }
    }

    SegmentedMobiusSieveCore mCore;
    std::vector<UInt32> mPrimes;
    UInt64 mSegSize;
    UInt64 mLo = 1;
    UInt64 mHi = 0;
    UInt64 mNextLo = 1;
    UInt32 mPrimeBound = 0;
};

// ============================================================================
// Free function — simplest API, hides all implementation details.
// ============================================================================

// Compute mu(1), mu(2), ..., mu(N) and return as a vector of Int8.
// Result has size N, with result[k-1] = mu(k).
[[maybe_unused]] static inline std::vector<Int8> MobiusSieveValues(UInt64 N, UInt64 segSize = 13860000ULL) {
    if (N < 1) return {};

    std::vector<Int8> result(N);

    SegmentedMobiusSieveCore sieve(segSize);

    const UInt32 sqrtN = (UInt32)std::max((Int64)SegmentedMobiusSieveCore::MIN_PRIMES_BOUND,
                                          (Int64)std::round(std::sqrt((double)N)));
    auto primes = SegmentedMobiusSieveCore::primesUpTo(sqrtN);

    for (UInt64 slo = 1; slo <= N; slo += segSize) {
        UInt64 shi = std::min(slo + segSize - 1, N);
        sieve.sieve(slo, shi, primes);

        const Int8* mu = sieve.data();

        #pragma omp parallel for schedule(static)
        for (UInt64 k = slo; k <= shi; ++k) {
            result[k - 1] = mu[k - slo];
        }
    }

    return result;
}

// END upstream SegmentedMobiusSieve.h

// BEGIN upstream stencil_data.h
// ============================================================================
// stencil_data.h — Precomputed Mobius sieve stencil for small primes.
//
// The stencil encodes the combined effect of primes {2, 3, 5, 7, 11} on the
// Mobius function. Its period is LCM(4, 9, 5, 7, 11) = 13860.
//
// Each entry is a packed Int8 encoding (ceil-log2 scheme):
//   - byte = 0x80 | S, where bit 7 is the squarefree flag and the low 7 bits
//     hold S = sum of (ceil(log2 p) | 1) over the small-prime factors p|n.
//   - Entries divisible by 4 or 9 are zeroed (square factor). Squares of
//     5, 7, 11 are left intact here and zeroed later by sieveM1PrimeRange.
//   - The finalization step converts these packed values into mu in {-1,0,1}.
//
// The stencil is used to initialize sieve segments via memcpy, avoiding
// redundant computation for the small primes on every segment.
//
// This file is generated; the ceil-log2 weights are 2->1, 3->3, 5->3, 7->3, 11->5.
// This file is included only by SegmentedMobiusSieve.cpp.
// ============================================================================

#define c128 static_cast<Int8>(128)
#define c129 static_cast<Int8>(129)
#define c130 static_cast<Int8>(130)
#define c131 static_cast<Int8>(131)
#define c132 static_cast<Int8>(132)
#define c133 static_cast<Int8>(133)
#define c134 static_cast<Int8>(134)
#define c135 static_cast<Int8>(135)
#define c136 static_cast<Int8>(136)
#define c137 static_cast<Int8>(137)
#define c138 static_cast<Int8>(138)
#define c139 static_cast<Int8>(139)
#define c140 static_cast<Int8>(140)
#define c141 static_cast<Int8>(141)
#define c142 static_cast<Int8>(142)
#define c143 static_cast<Int8>(143)

Int8 stencil[] = {\
    c128, c129, c131, 0, c131, c132, c131, 0, 0, c132, c133, 0, c128, c132, c134, 0, \
    c128, 0, c128, 0, c134, c134, c128, 0, c131, c129, 0, 0, c128, c135, c128, 0, \
    c136, c129, c134, 0, c128, c129, c131, 0, c128, c135, c128, 0, 0, c129, c128, 0, \
    c131, c132, c131, 0, c128, 0, c136, 0, c131, c129, c128, 0, c128, c129, 0, 0, \
    c131, c137, c128, 0, c131, c135, c128, 0, c128, c129, c134, 0, c136, c132, c128, 0, \
    0, c129, c128, 0, c131, c129, c131, 0, c128, 0, c131, 0, c131, c129, c131, 0, \
    c128, c132, 0, 0, c128, c132, c128, 0, c137, c129, c128, 0, c128, c137, c131, 0, \
    c128, c132, c131, 0, 0, c129, c131, 0, c133, c129, c131, 0, c131, 0, c128, 0, \
    c131, c132, c128, 0, c131, c129, 0, 0, c128, c132, c128, 0, c131, c129, c133, 0, \
    c131, c129, c134, 0, c128, c135, c128, 0, 0, c137, c131, 0, c128, c129, c131, 0, \
    c131, 0, c128, 0, c139, c129, c128, 0, c128, c132, 0, 0, c128, c132, c134, 0, \
    c131, c129, c128, 0, c128, c132, c131, 0, c131, c132, c133, 0, 0, c132, c128, 0, \
    c128, c129, c134, 0, c128, 0, c128, 0, c131, c129, c131, 0, c131, c129, 0, 0, \
    c133, c138, c128, 0, c131, c129, c131, 0, c131, c129, c131, 0, c128, c132, c128, 0, \
    0, c129, c128, 0, c128, c132, c139, 0, c128, 0, c131, 0, c131, c132, c128, 0, \
    c128, c134, 0, 0, c134, c132, c128, 0, c131, c132, c128, 0, c133, c129, c134, 0, \
    c128, c132, c131, 0, 0, c129, c128, 0, c131, c132, c131, 0, c128, 0, c128, 0, \
    c134, c129, c136, 0, c128, c129, 0, 0, c128, c132, c128, 0, c134, c134, c131, 0, \
    c128, c132, c131, 0, c128, c135, c131, 0, 0, c129, c128, 0, c131, c129, c131, 0, \
    c131, 0, c128, 0, c131, c132, c128, 0, c128, c129, 0, 0, c128, c132, c133, 0, \
    c131, c132, c128, 0, c131, c129, c131, 0, c131, c140, c128, 0, 0, c129, c131, 0, \
    c128, c129, c131, 0, c133, 0, c131, 0, c134, c129, c128, 0, c128, c135, 0, 0, \
    c128, c132, c131, 0, c134, c129, c128, 0, c128, c129, c136, 0, c131, c132, c128, 0, \
    0, c132, c131, 0, c128, c134, c134, 0, c128, 0, c128, 0, c131, c129, c128, 0, \
    c139, c129, 0, 0, c128, c135, c128, 0, c131, c129, c131, 0, c128, c129, c134, 0, \
    c128, c132, c128, 0, 0, c132, c133, 0, c128, c132, c131, 0, c131, 0, c131, 0, \
    c131, c134, c128, 0, c128, c129, 0, 0, c131, c132, c131, 0, c136, c132, c128, 0, \
    c128, c132, c134, 0, c128, c132, c128, 0, 0, c129, c128, 0, c131, c129, c131, 0, \
    c128, 0, c133, 0, c131, c129, c134, 0, c128, c129, 0, 0, c128, c140, c128, 0, \
    c134, c129, c128, 0, c131, c132, c131, 0, c133, c132, c131, 0, 0, c129, c128, 0, \
    c128, c129, c134, 0, c131, 0, c128, 0, c131, c135, c128, 0, c128, c129, 0, 0, \
    c131, c132, c128, 0, c131, c129, c128, 0, c131, c134, c131, 0, c128, c135, c131, 0, \
    0, c129, c131, 0, c133, c132, c131, 0, c128, 0, c128, 0, c137, c129, c128, 0, \
    c128, c132, 0, 0, c128, c132, c131, 0, c131, c129, c136, 0, c128, c129, c131, 0, \
    c131, c135, c128, 0, 0, c137, c128, 0, c131, c129, c134, 0, c128, 0, c128, 0, \
    c136, c129, c128, 0, c131, c129, 0, 0, c128, c135, c128, 0, c131, c132, c131, 0, \
    c128, c129, c131, 0, c131, c132, c133, 0, 0, c129, c128, 0, c128, c132, c131, 0, \
    c128, 0, c134, 0, c131, c129, c128, 0, c128, c132, 0, 0, c136, c132, c128, 0, \
    c134, c132, c128, 0, c128, c129, c134, 0, c128, c132, c128, 0, 0, c129, c131, 0, \
    c131, c129, c136, 0, c128, 0, c128, 0, c131, c129, c131, 0, c131, c134, 0, 0, \
    c128, c132, c128, 0, c134, c129, c128, 0, c133, c132, c134, 0, c128, c132, c131, 0, \
    0, c132, c128, 0, c128, c129, c131, 0, c134, 0, c128, 0, c131, c132, c133, 0, \
    c128, c129, 0, 0, c128, c132, c131, 0, c131, c134, c128, 0, c131, c132, c131, 0, \
    c128, c135, c128, 0, 0, c129, c131, 0, c128, c129, c131, 0, c128, 0, c128, 0, \
    c134, c129, c131, 0, c128, c132, 0, 0, c128, c135, c136, 0, c131, c129, c128, 0, \
    c131, c129, c131, 0, c131, c137, c128, 0, 0, c132, c128, 0, c128, c129, c137, 0, \
    c133, 0, c128, 0, c131, c132, c128, 0, c131, c129, 0, 0, c131, c135, c128, 0, \
    c131, c129, c131, 0, c128, c129, c136, 0, c128, c132, c131, 0, 0, c129, c128, 0, \
    c128, c140, c131, 0, c128, 0, c131, 0, c134, c129, c128, 0, c133, c129, 0, 0, \
    c131, c132, c128, 0, c131, c132, c131, 0, c128, c129, c134, 0, c128, c135, c128, 0, \
    0, c129, c133, 0, c134, c129, c131, 0, c128, 0, c128, 0, c131, c134, c131, 0, \
    c128, c129, 0, 0, c128, c132, c128, 0, c139, c132, c128, 0, c128, c132, c131, 0, \
    c131, c132, c131, 0, 0, c129, c128, 0, c128, c129, c131, 0, c131, 0, c136, 0, \
    c131, c132, c128, 0, c128, c132, 0, 0, c128, c137, c128, 0, c134, c129, c128, 0, \
    c131, c129, c131, 0, c133, c135, c128, 0, 0, c129, c134, 0, c128, c129, c131, 0, \
    c128, 0, c128, 0, c134, c129, c128, 0, c131, c132, 0, 0, c128, c132, c131, 0, \
    c131, c129, c128, 0, c128, c134, c134, 0, c131, c132, c128, 0, 0, c135, c128, 0, \
    c133, c129, c134, 0, c131, 0, c128, 0, c131, c129, c128, 0, c131, c129, 0, 0, \
    c128, c135, c131, 0, c131, c129, c136, 0, c128, c132, c131, 0, c128, c132, c128, 0, \
    0, c134, c128, 0, c128, c132, c131, 0, c128, 0, c131, 0, c136, c129, c131, 0, \
    c128, c129, 0, 0, c131, c135, c128, 0, c131, c132, c128, 0, c131, c129, c134, 0, \
    c128, c132, c133, 0, 0, c129, c128, 0, c131, c129, c134, 0, c128, 0, c128, 0, \
    c131, c132, c131, 0, c128, c129, 0, 0, c136, c132, c128, 0, c134, c129, c128, 0, \
    c128, c132, c131, 0, c128, c132, c134, 0, 0, c129, c128, 0, c128, c132, c136, 0, \
    c131, 0, c128, 0, c134, c132, c128, 0, c128, c134, 0, 0, c128, c132, c128, 0, \
    c131, c129, c131, 0, c136, c129, c131, 0, c128, c138, c128, 0, 0, c129, c131, 0, \
    c131, c129, c131, 0, c128, 0, c128, 0, c134, c129, c133, 0, c128, c132, 0, 0, \
    c128, c132, c131, 0, c131, c137, c128, 0, c128, c129, c131, 0, c134, c132, c128, 0, \
    0, c132, c128, 0, c128, c129, c134, 0, c128, 0, c131, 0, c131, c129, c128, 0, \
    c131, c132, 0, 0, c128, c135, c133, 0, c134, c129, c131, 0, c128, c129, c131, 0, \
    c128, c137, c128, 0, 0, c129, c131, 0, c128, c132, c131, 0, c133, 0, c131, 0, \
    c131, c129, c128, 0, c131, c129, 0, 0, c131, c132, c128, 0, c131, c132, c128, 0, \
    c128, c129, c142, 0, c128, c132, c128, 0, 0, c132, c128, 0, c131, c134, c131, 0, \
    c131, 0, c128, 0, c131, c129, c131, 0, c133, c129, 0, 0, c128, c132, c131, 0, \
    c134, c129, c128, 0, c128, c135, c131, 0, c128, c132, c131, 0, 0, c129, c133, 0, \
    c128, c129, c131, 0, c131, 0, c128, 0, c131, c137, c131, 0, c128, c129, 0, 0, \
    c128, c135, c128, 0, c136, c129, c128, 0, c134, c129, c131, 0, c128, c135, c128, 0, \
    0, c129, c131, 0, c128, c129, c134, 0, c128, 0, c133, 0, c134, c132, c128, 0, \
    c128, c132, 0, 0, c131, c137, c131, 0, c131, c129, c128, 0, c128, c129, c131, 0, \
    c136, c132, c131, 0, 0, c132, c128, 0, c128, c132, c134, 0, c128, 0, c128, 0, \
    c134, c129, c128, 0, c131, c129, 0, 0, c128, c135, c128, 0, c131, c129, c134, 0, \
    c128, c134, c131, 0, c128, c135, c128, 0, 0, c129, c128, 0, c136, c132, c131, 0, \
    c128, 0, c131, 0, c131, c129, c128, 0, c128, c129, 0, 0, c131, c132, c128, 0, \
    c131, c135, c133, 0, c128, c129, c134, 0, c131, c132, c128, 0, 0, c134, c128, 0, \
    c131, c129, c131, 0, c128, 0, c131, 0, c136, c129, c131, 0, c128, c132, 0, 0, \
    c128, c132, c128, 0, c137, c129, c128, 0, c128, c132, c131, 0, c128, c132, c136, 0, \
    0, c129, c131, 0, c128, c129, c131, 0, c131, 0, c128, 0, c131, c132, c128, 0, \
    c131, c129, 0, 0, c133, c132, c128, 0, c131, c129, c128, 0, c131, c129, c134, 0, \
    c128, c135, c128, 0, 0, c132, c131, 0, c128, c129, c136, 0, c131, 0, c128, 0, \
    c134, c129, c128, 0, c128, c137, 0, 0, c128, c132, c134, 0, c131, c129, c128, 0, \
    c133, c132, c131, 0, c131, c132, c128, 0, 0, c132, c128, 0, c128, c129, c134, 0, \
    c128, 0, c128, 0, c131, c129, c136, 0, c131, c129, 0, 0, c128, c138, c128, 0, \
    c131, c134, c131, 0, c131, c129, c131, 0, c128, c132, c128, 0, 0, c129, c128, 0, \
    c128, c132, c134, 0, c128, 0, c131, 0, c131, c132, c128, 0, c128, c129, 0, 0, \
    c134, c132, c133, 0, c131, c132, c128, 0, c128, c129, c134, 0, c128, c137, c131, 0, \
    0, c129, c128, 0, c131, c132, c131, 0, c133, 0, c128, 0, c134, c129, c131, 0, \
    c128, c129, 0, 0, c128, c132, c128, 0, c134, c129, c131, 0, c128, c132, c136, 0, \
    c128, c135, c131, 0, 0, c129, c128, 0, c131, c134, c131, 0, c131, 0, c128, 0, \
    c131, c132, c128, 0, c133, c129, 0, 0, c128, c132, c128, 0, c131, c132, c128, 0, \
    c131, c129, c131, 0, c131, c135, c128, 0, 0, c129, c136, 0, c128, c129, c131, 0, \
    c128, 0, c131, 0, c134, c134, c128, 0, c128, c135, 0, 0, c128, c132, c131, 0, \
    c139, c129, c128, 0, c128, c129, c131, 0, c131, c132, c128, 0, 0, c132, c131, 0, \
    c128, c129, c134, 0, c128, 0, c133, 0, c131, c129, c128, 0, c134, c129, 0, 0, \
    c128, c140, c128, 0, c131, c129, c131, 0, c128, c129, c134, 0, c133, c132, c128, 0, \
    0, c132, c128, 0, c128, c132, c131, 0, c131, 0, c131, 0, c131, c129, c128, 0, \
    c128, c129, 0, 0, c131, c132, c131, 0, c131, c132, c128, 0, c128, c137, c134, 0, \
    c128, c132, c128, 0, 0, c129, c128, 0, c136, c129, c131, 0, c128, 0, c128, 0, \
    c131, c129, c134, 0, c128, c129, 0, 0, c128, c135, c128, 0, c134, c129, c133, 0, \
    c131, c132, c131, 0, c128, c132, c131, 0, 0, c134, c128, 0, c128, c129, c134, 0, \
    c131, 0, c128, 0, c136, c135, c128, 0, c128, c129, 0, 0, c131, c132, c128, 0, \
    c131, c129, c128, 0, c131, c129, c131, 0, c128, c135, c136, 0, 0, c129, c131, 0, \
    c128, c132, c131, 0, c128, 0, c128, 0, c137, c129, c128, 0, c128, c132, 0, 0, \
    c133, c132, c131, 0, c131, c129, c131, 0, c128, c129, c131, 0, c131, c135, c128, 0, \
    0, c132, c128, 0, c131, c129, c139, 0, c128, 0, c128, 0, c131, c129, c128, 0, \
    c131, c134, 0, 0, c128, c135, c128, 0, c131, c132, c131, 0, c133, c129, c131, 0, \
    c131, c132, c128, 0, 0, c129, c128, 0, c128, c132, c131, 0, c128, 0, c134, 0, \
    c131, c129, c133, 0, c128, c132, 0, 0, c131, c132, c128, 0, c134, c137, c128, 0, \
    c128, c129, c134, 0, c128, c132, c128, 0, 0, c129, c131, 0, c131, c129, c131, 0, \
    c128, 0, c128, 0, c131, c129, c131, 0, c131, c129, 0, 0, c128, c132, c133, 0, \
    c134, c129, c128, 0, c128, c132, c134, 0, c128, c137, c131, 0, 0, c132, c128, 0, \
    c128, c129, c131, 0, c139, 0, c128, 0, c131, c132, c128, 0, c128, c129, 0, 0, \
    c128, c132, c131, 0, c131, c129, c128, 0, c131, c132, c136, 0, c128, c135, c128, 0, \
    0, c129, c131, 0, c128, c134, c131, 0, c128, 0, c128, 0, c134, c129, c131, 0, \
    c133, c132, 0, 0, c128, c135, c131, 0, c131, c129, c128, 0, c131, c129, c131, 0, \
    c131, c132, c128, 0, 0, c132, c133, 0, c128, c129, c137, 0, c128, 0, c128, 0, \
    c131, c137, c128, 0, c131, c129, 0, 0, c131, c135, c128, 0, c136, c129, c131, 0, \
    c128, c129, c131, 0, c128, c132, c131, 0, 0, c129, c128, 0, c128, c135, c131, 0, \
    c128, 0, c136, 0, c134, c129, c128, 0, c128, c129, 0, 0, c131, c137, c128, 0, \
    c131, c132, c131, 0, c128, c129, c134, 0, c133, c135, c128, 0, 0, c129, c128, 0, \
    c134, c129, c131, 0, c128, 0, c128, 0, c131, c129, c131, 0, c128, c129, 0, 0, \
    c128, c132, c128, 0, c134, c132, c128, 0, c128, c137, c131, 0, c131, c132, c131, 0, \
    0, c129, c128, 0, c133, c129, c131, 0, c131, 0, c131, 0, c131, c132, c128, 0, \
    c128, c132, 0, 0, c128, c132, c128, 0, c134, c129, c133, 0, c131, c129, c131, 0, \
    c128, c135, c128, 0, 0, c134, c134, 0, c128, c129, c131, 0, c128, 0, c128, 0, \
    c139, c129, c128, 0, c131, c132, 0, 0, c128, c132, c131, 0, c131, c129, c128, 0, \
    c128, c129, c134, 0, c131, c132, c133, 0, 0, c135, c128, 0, c128, c129, c134, 0, \
    c131, 0, c128, 0, c131, c129, c128, 0, c131, c129, 0, 0, c133, c135, c131, 0, \
    c131, c129, c131, 0, c128, c132, c131, 0, c128, c132, c128, 0, 0, c129, c128, 0, \
    c128, c132, c136, 0, c128, 0, c131, 0, c131, c129, c131, 0, c128, c134, 0, 0, \
    c131, c135, c128, 0, c131, c132, c128, 0, c136, c129, c134, 0, c128, c132, c128, 0, \
    0, c129, c128, 0, c131, c129, c134, 0, c128, 0, c128, 0, c131, c132, c136, 0, \
    c128, c129, 0, 0, c131, c132, c128, 0, c134, c134, c128, 0, c128, c132, c131, 0, \
    c128, c132, c134, 0, 0, c129, c128, 0, c128, c132, c131, 0, c131, 0, c128, 0, \
    c134, c132, c128, 0, c128, c129, 0, 0, c128, c132, c133, 0, c131, c129, c131, 0, \
    c131, c129, c131, 0, c128, c143, c128, 0, 0, c129, c131, 0, c131, c129, c131, 0, \
    c133, 0, c128, 0, c134, c129, c128, 0, c128, c132, 0, 0, c128, c132, c131, 0, \
    c131, c132, c128, 0, c128, c129, c136, 0, c134, c132, c128, 0, 0, c132, c128, 0, \
    c128, c134, c134, 0, c128, 0, c131, 0, c131, c129, c128, 0, c136, c132, 0, 0, \
    c128, c135, c128, 0, c134, c129, c131, 0, c128, c129, c131, 0, c128, c132, c128, 0, \
    0, c129, c136, 0, c128, c132, c131, 0, c128, 0, c131, 0, c131, c134, c128, 0, \
    c131, c129, 0, 0, c131, c132, c128, 0, c136, c132, c128, 0, c128, c129, c137, 0, \
    c128, c132, c128, 0, 0, c132, c128, 0, c131, c129, c131, 0, c131, 0, c133, 0, \
    c131, c129, c131, 0, c128, c129, 0, 0, c128, c137, c131, 0, c134, c129, c128, 0, \
    c128, c135, c131, 0, c133, c132, c131, 0, 0, c129, c128, 0, c128, c129, c131, 0, \
    c131, 0, c128, 0, c131, c132, c131, 0, c128, c129, 0, 0, c128, c135, c128, 0, \
    c131, c129, c128, 0, c134, c134, c131, 0, c128, c135, c128, 0, 0, c129, c131, 0, \
    c133, c129, c134, 0, c128, 0, c128, 0, c134, c132, c128, 0, c128, c132, 0, 0, \
    c131, c132, c131, 0, c131, c129, c133, 0, c128, c129, c131, 0, c131, c132, c131, 0, \
    0, c137, c128, 0, c128, c132, c134, 0, c128, 0, c128, 0, c139, c129, c128, 0, \
    c131, c129, 0, 0, c128, c135, c128, 0, c131, c129, c134, 0, c128, c129, c131, 0, \
    c128, c135, c133, 0, 0, c129, c128, 0, c131, c132, c131, 0, c128, 0, c131, 0, \
    c131, c129, c128, 0, c128, c129, 0, 0, c136, c132, c128, 0, c131, c135, c128, 0, \
    c128, c129, c134, 0, c131, c132, c128, 0, 0, c129, c128, 0, c131, c129, c136, 0, \
    c128, 0, c131, 0, c131, c129, c131, 0, c128, c137, 0, 0, c128, c132, c128, 0, \
    c137, c129, c128, 0, c133, c132, c131, 0, c128, c132, c131, 0, 0, c129, c131, 0, \
    c128, c129, c131, 0, c131, 0, c128, 0, c131, c132, c133, 0, c131, c129, 0, 0, \
    c128, c132, c128, 0, c131, c134, c128, 0, c131, c129, c134, 0, c128, c135, c128, 0, \
    0, c132, c131, 0, c128, c129, c131, 0, c131, 0, c128, 0, c134, c129, c128, 0, \
    c128, c132, 0, 0, c128, c132, c139, 0, c131, c129, c128, 0, c128, c132, c131, 0, \
    c131, c137, c128, 0, 0, c132, c128, 0, c128, c129, c134, 0, c133, 0, c128, 0, \
    c131, c129, c131, 0, c131, c129, 0, 0, c128, c138, c128, 0, c131, c129, c131, 0, \
    c131, c129, c136, 0, c128, c132, c128, 0, 0, c129, c128, 0, c128, c137, c134, 0, \
    c128, 0, c131, 0, c131, c132, c128, 0, c133, c129, 0, 0, c134, c132, c128, 0, \
    c131, c132, c128, 0, c128, c129, c134, 0, c128, c132, c131, 0, 0, c129, c133, 0, \
    c131, c132, c131, 0, c128, 0, c128, 0, c134, c134, c131, 0, c128, c129, 0, 0, \
    c128, c132, c128, 0, c139, c129, c131, 0, c128, c132, c131, 0, c128, c135, c131, 0, \
    0, c129, c128, 0, c131, c129, c131, 0, c131, 0, c133, 0, c131, c132, c128, 0, \
    c128, c129, 0, 0, c128, c137, c128, 0, c131, c132, c128, 0, c131, c129, c131, 0, \
    c136, c135, c128, 0, 0, c129, c131, 0, c128, c129, c131, 0, c128, 0, c131, 0, \
    c134, c129, c128, 0, c128, c135, 0, 0, c128, c132, c131, 0, c134, c129, c128, 0, \
    c128, c134, c131, 0, c131, c132, c128, 0, 0, c132, c131, 0, c133, c129, c134, 0, \
    c128, 0, c128, 0, c131, c129, c128, 0, c134, c129, 0, 0, c128, c135, c128, 0, \
    c131, c129, c136, 0, c128, c129, c134, 0, c128, c132, c128, 0, 0, c137, c128, 0, \
    c128, c132, c131, 0, c131, 0, c131, 0, c136, c129, c128, 0, c128, c129, 0, 0, \
    c131, c132, c131, 0, c131, c132, c128, 0, c128, c132, c134, 0, c128, c132, c133, 0, \
    0, c129, c128, 0, c131, c129, c131, 0, c128, 0, c128, 0, c131, c129, c134, 0, \
    c128, c129, 0, 0, c133, c135, c128, 0, c134, c129, c128, 0, c131, c132, c131, 0, \
    c128, c132, c131, 0, 0, c129, c128, 0, c128, c129, c139, 0, c131, 0, c128, 0, \
    c131, c135, c128, 0, c128, c134, 0, 0, c131, c132, c128, 0, c131, c129, c128, 0, \
    c136, c129, c131, 0, c128, c135, c131, 0, 0, c129, c131, 0, c128, c132, c131, 0, \
    c128, 0, c128, 0, c137, c129, c133, 0, c128, c132, 0, 0, c128, c132, c131, 0, \
    c131, c134, c131, 0, c128, c129, c131, 0, c131, c135, c128, 0, 0, c132, c128, 0, \
    c131, c129, c134, 0, c128, 0, c128, 0, c131, c129, c128, 0, c131, c129, 0, 0, \
    c128, c135, c133, 0, c131, c132, c131, 0, c128, c129, c131, 0, c131, c137, c128, 0, \
    0, c129, c128, 0, c128, c132, c131, 0, c133, 0, c134, 0, c131, c129, c128, 0, \
    c128, c132, 0, 0, c131, c132, c128, 0, c134, c132, c128, 0, c128, c129, c139, 0, \
    c128, c132, c128, 0, 0, c129, c131, 0, c131, c134, c131, 0, c128, 0, c128, 0, \
    c131, c129, c131, 0, c136, c129, 0, 0, c128, c132, c128, 0, c134, c129, c128, 0, \
    c128, c132, c134, 0, c128, c132, c131, 0, 0, c132, c133, 0, c128, c129, c131, 0, \
    c134, 0, c128, 0, c131, c137, c128, 0, c128, c129, 0, 0, c128, c132, c131, 0, \
    c136, c129, c128, 0, c131, c132, c131, 0, c128, c135, c128, 0, 0, c129, c131, 0, \
    c128, c129, c131, 0, c128, 0, c133, 0, c134, c129, c131, 0, c128, c132, 0, 0, \
    c128, c140, c131, 0, c131, c129, c128, 0, c131, c129, c131, 0, c136, c132, c128, 0, \
    0, c132, c128, 0, c128, c129, c137, 0, c128, 0, c128, 0, c131, c132, c128, 0, \
    c131, c129, 0, 0, c131, c135, c128, 0, c131, c129, c131, 0, c128, c134, c131, 0, \
    c128, c132, c131, 0, 0, c129, c128, 0, c133, c135, c131, 0, c128, 0, c131, 0, \
    c134, c129, c128, 0, c128, c129, 0, 0, c131, c132, c128, 0, c131, c132, c136, 0, \
    c128, c129, c134, 0, c128, c135, c128, 0, 0, c134, c128, 0, c134, c129, c131, 0, \
    c128, 0, c128, 0, c136, c129, c131, 0, c128, c129, 0, 0, c128, c132, c128, 0, \
    c134, c132, c128, 0, c128, c132, c131, 0, c131, c132, c136, 0, 0, c129, c128, 0, \
    c128, c129, c131, 0, c131, 0, c131, 0, c131, c132, c128, 0, c128, c132, 0, 0, \
    c133, c132, c128, 0, c134, c129, c128, 0, c131, c129, c131, 0, c128, c135, c128, 0, \
    0, c129, c134, 0, c128, c129, c136, 0, c128, 0, c128, 0, c134, c129, c128, 0, \
    c131, c137, 0, 0, c128, c132, c131, 0, c131, c129, c128, 0, c133, c129, c134, 0, \
    c131, c132, c128, 0, 0, c135, c128, 0, c128, c129, c134, 0, c131, 0, c128, 0, \
    c131, c129, c133, 0, c131, c129, 0, 0, c128, c135, c131, 0, c131, c134, c131, 0, \
    c128, c132, c131, 0, c128, c132, c128, 0, 0, c129, c128, 0, c128, c132, c131, 0, \
    c128, 0, c131, 0, c131, c129, c131, 0, c128, c129, 0, 0, c131, c135, c133, 0, \
    c131, c132, c128, 0, c131, c129, c134, 0, c128, c137, c128, 0, 0, c129, c128, 0, \
    c131, c129, c134, 0, c133, 0, c128, 0, c131, c132, c131, 0, c128, c129, 0, 0, \
    c131, c132, c128, 0, c134, c129, c128, 0, c128, c132, c136, 0, c128, c132, c134, 0, \
    0, c129, c128, 0, c128, c137, c131, 0, c131, 0, c128, 0, c134, c132, c128, 0, \
    c133, c129, 0, 0, c128, c132, c128, 0, c131, c129, c131, 0, c131, c129, c131, 0, \
    c128, c138, c128, 0, 0, c129, c136, 0, c131, c129, c131, 0, c128, 0, c128, 0, \
    c134, c134, c128, 0, c128, c132, 0, 0, c128, c132, c131, 0, c136, c132, c128, 0, \
    c128, c129, c131, 0, c134, c132, c128, 0, 0, c132, c128, 0, c128, c129, c134, 0, \
    c128, 0, c136, 0, c131, c129, c128, 0, c131, c132, 0, 0, c128, c140, c128, 0, \
    c134, c129, c131, 0, c128, c129, c131, 0, c133, c132, c128, 0, 0, c129, c131, 0, \
    c128, c132, c131, 0, c128, 0, c131, 0, c131, c129, c128, 0, c131, c129, 0, 0, \
    c131, c132, c128, 0, c131, c132, c128, 0, c128, c134, c137, 0, c128, c132, c128, 0, \
    0, c132, c128, 0, c136, c129, c131, 0, c131, 0, c128, 0, c131, c129, c131, 0, \
    c128, c129, 0, 0, c128, c132, c131, 0, c134, c129, c133, 0, c128, c135, c131, 0, \
    c128, c132, c131, 0, 0, c134, c128, 0, c128, c129, c131, 0, c131, 0, c128, 0, \
    c136, c132, c131, 0, c128, c129, 0, 0, c128, c135, c128, 0, c131, c129, c128, 0, \
    c134, c129, c131, 0, c128, c135, c133, 0, 0, c129, c131, 0, c128, c129, c134, 0, \
    c128, 0, c128, 0, c134, c132, c128, 0, c128, c132, 0, 0, c136, c132, c131, 0, \
    c131, c129, c128, 0, c128, c129, c131, 0, c131, c132, c131, 0, 0, c132, c128, 0, \
    c128, c132, c139, 0, c128, 0, c128, 0, c134, c129, c128, 0, c131, c134, 0, 0, \
    c128, c135, c128, 0, c131, c129, c134, 0, c133, c129, c131, 0, c128, c135, c128, 0, \
    0, c129, c128, 0, c131, c132, c131, 0, c128, 0, c131, 0, c131, c129, c133, 0, \
    c128, c129, 0, 0, c131, c132, c128, 0, c131, c140, c128, 0, c128, c129, c134, 0, \
    c131, c132, c128, 0, 0, c129, c128, 0, c131, c129, c131, 0, c128, 0, c131, 0, \
    c131, c129, c131, 0, c128, c132, 0, 0, c128, c132, c133, 0, c137, c129, c128, 0, \
    c128, c132, c131, 0, c128, c137, c131, 0, 0, c129, c131, 0, c128, c129, c131, 0, \
    c136, 0, c128, 0, c131, c132, c128, 0, c131, c129, 0, 0, c128, c132, c128, 0, \
    c131, c129, c128, 0, c131, c129, c139, 0, c128, c135, c128, 0, 0, c132, c131, 0, \
    c128, c134, c131, 0, c131, 0, c128, 0, c134, c129, c128, 0, c133, c132, 0, 0, \
    c128, c132, c134, 0, c131, c129, c128, 0, c128, c132, c131, 0, c131, c132, c128, 0, \
    0, c132, c133, 0, c128, c129, c134, 0, c128, 0, c128, 0, c131, c134, c131, 0, \
    c131, c129, 0, 0, c128, c138, c128, 0, c136, c129, c131, 0, c131, c129, c131, 0, \
    c128, c132, c128, 0, 0, c129, c128, 0, c128, c132, c134, 0, c128, 0, c136, 0, \
    c131, c132, c128, 0, c128, c129, 0, 0, c134, c137, c128, 0, c131, c132, c128, 0, \
    c128, c129, c134, 0, c133, c132, c131, 0, 0, c129, c128, 0, c131, c132, c131, 0, \
    c128, 0, c128, 0, c134, c129, c131, 0, c128, c129, 0, 0, c128, c132, c128, 0, \
    c134, c129, c131, 0, c128, c137, c131, 0, c128, c135, c131, 0, 0, c129, c128, 0, \
    c136, c129, c131, 0, c131, 0, c128, 0, c131, c132, c128, 0, c128, c129, 0, 0, \
    c128, c132, c128, 0, c131, c132, c133, 0, c131, c129, c131, 0, c131, c135, c128, 0, \
    0, c134, c131, 0, c128, c129, c131, 0, c128, 0, c131, 0, c139, c129, c128, 0, \
    c128, c135, 0, 0, c128, c132, c131, 0, c134, c129, c128, 0, c128, c129, c131, 0, \
    c131, c132, c133, 0, 0, c132, c131, 0, c128, c129, c134, 0, c128, 0, c128, 0, \
    c131, c129, c128, 0, c134, c129, 0, 0, c133, c135, c128, 0, c131, c129, c131, 0, \
    c128, c129, c134, 0, c128, c132, c128, 0, 0, c132, c128, 0, c128, c132, c136, 0, \
    c131, 0, c131, 0, c131, c129, c128, 0, c128, c134, 0, 0, c131, c132, c131, 0, \
    c131, c132, c128, 0, c133, c132, c134, 0, c128, c132, c128, 0, 0, c129, c128, 0, \
    c131, c129, c131, 0, c128, 0, c128, 0, c131, c129, c139, 0, c128, c129, 0, 0, \
    c128, c135, c128, 0, c134, c134, c128, 0, c131, c132, c131, 0, c128, c132, c131, 0, \
    0, c129, c128, 0, c128, c129, c134, 0, c131, 0, c128, 0, c131, c135, c128, 0, \
    c128, c129, 0, 0, c131, c132, c133, 0, c131, c129, c128, 0, c131, c129, c131, 0, \
    c128, c140, c131, 0, 0, c129, c131, 0, c128, c132, c131, 0, c133, 0, c128, 0, \
    c137, c129, c128, 0, c128, c132, 0, 0, c128, c132, c131, 0, c131, c129, c131, 0, \
    c128, c129, c136, 0, c131, c135, c128, 0, 0, c132, c128, 0, c131, c134, c134, 0, \
    c128, 0, c128, 0, c131, c129, c128, 0, c136, c129, 0, 0, c128, c135, c128, 0, \
    c131, c132, c131, 0, c128, c129, c131, 0, c131, c132, c128, 0, 0, c129, c133, 0, \
    c128, c132, c131, 0, c128, 0, c134, 0, c131, c134, c128, 0, c128, c132, 0, 0, \
    c131, c132, c128, 0, c139, c132, c128, 0, c128, c129, c134, 0, c128, c132, c128, 0, \
    0, c129, c131, 0, c131, c129, c131, 0, c128, 0, c133, 0, c131, c129, c131, 0, \
    c131, c129, 0, 0, c128, c137, c128, 0, c134, c129, c128, 0, c128, c132, c134, 0, \
    c133, c132, c131, 0, 0, c132, c128, 0, c128, c129, c131, 0, c134, 0, c128, 0, \
    c131, c132, c128, 0, c128, c129, 0, 0, c128, c132, c131, 0, c131, c129, c128, 0, \
    c131, c137, c131, 0, c128, c135, c128, 0, 0, c129, c131, 0, c133, c129, c131, 0, \
    c128, 0, c128, 0, c134, c129, c131, 0, c128, c132, 0, 0, c128, c135, c131, 0, \
    c131, c129, c133, 0, c131, c129, c131, 0, c131, c132, c128, 0, 0, c137, c128, 0, \
    c128, c129, c137, 0, c128, 0, c128, 0, c136, c132, c128, 0, c131, c129, 0, 0, \
    c131, c135, c128, 0, c131, c129, c131, 0, c128, c129, c131, 0, c128, c132, c136, 0, \
    0, c129, c128, 0, c128, c135, c131, 0, c128, 0, c131, 0, c134, c129, c128, 0, \
    c128, c129, 0, 0, c136, c132, c128, 0, c131, c132, c131, 0, c128, c129, c134, 0, \
    c128, c135, c128, 0, 0, c129, c128, 0, c134, c129, c136, 0, c128, 0, c128, 0, \
    c131, c129, c131, 0, c128, c134, 0, 0, c128, c132, c128, 0, c134, c132, c128, 0, \
    c133, c132, c131, 0, c131, c132, c131, 0, 0, c129, c128, 0, c128, c129, c131, 0, \
    c131, 0, c131, 0, c131, c132, c133, 0, c128, c132, 0, 0, c128, c132, c128, 0, \
    c134, c134, c128, 0, c131, c129, c131, 0, c128, c135, c128, 0, 0, c129, c134, 0, \
    c128, c129, c131, 0, c128, 0, c128, 0, c134, c129, c128, 0, c131, c132, 0, 0, \
    c128, c132, c136, 0, c131, c129, c128, 0, c128, c129, c134, 0, c131, c137, c128, 0, \
    0, c135, c128, 0, c128, c129, c134, 0, c136, 0, c128, 0, c131, c129, c128, 0, \
    c131, c129, 0, 0, c128, c135, c131, 0, c131, c129, c131, 0, c128, c132, c136, 0, \
    c128, c132, c128, 0, 0, c129, c128, 0, c128, c137, c131, 0, c128, 0, c131, 0, \
    c131, c129, c131, 0, c133, c129, 0, 0, c131, c135, c128, 0, c131, c132, c128, 0, \
    c131, c129, c134, 0, c128, c132, c128, 0, 0, c129, c133, 0, c131, c129, c134, 0, \
    c128, 0, c128, 0, c131, c137, c131, 0, c128, c129, 0, 0, c131, c132, c128, 0, \
    c139, c129, c128, 0, c128, c132, c131, 0, c128, c132, c134, 0, 0, c129, c128, 0, \
    c128, c132, c131, 0, c131, 0, c133, 0, c134, c132, c128, 0, c128, c129, 0, 0, \
    c128, c137, c128, 0, c131, c129, c131, 0, c131, c129, c131, 0, c133, c138, c128, 0, \
    0, c129, c131, 0, c131, c129, c131, 0, c128, 0, c128, 0, c134, c129, c128, 0, \
    c128, c132, 0, 0, c128, c132, c131, 0, c131, c132, c128, 0, c128, c134, c131, 0, \
    c134, c132, c128, 0, 0, c132, c128, 0, c133, c129, c134, 0, c128, 0, c131, 0, \
    c131, c129, c128, 0, c131, c132, 0, 0, c128, c135, c128, 0, c134, c129, c136, 0, \
    c128, c129, c131, 0, c128, c132, c128, 0, 0, c134, c131, 0, c128, c132, c131, 0, \
    c128, 0, c131, 0, c136, c129, c128, 0, c131, c129, 0, 0, c131, c132, c128, 0, \
    c131, c132, c128, 0, c128, c129, c137, 0, c128, c132, c133, 0, 0, c132, c128, 0, \
    c131, c129, c131, 0, c131, 0, c128, 0, c131, c129, c131, 0, c128, c129, 0, 0, \
    c133, c132, c131, 0, c134, c129, c128, 0, c128, c135, c131, 0, c128, c132, c131, 0, \
    0, c129, c128, 0, c128, c129, c136, 0, c131, 0, c128, 0, c131, c132, c131, 0, \
    c128, c134, 0, 0, c128, c135, c128, 0, c131, c129, c128, 0, c139, c129, c131, 0, \
    c128, c135, c128, 0, 0, c129, c131, 0, c128, c129, c134, 0, c128, 0, c128, 0, \
    c134, c132, c133, 0, c128, c132, 0, 0, c131, c132, c131, 0, c131, c134, c128, 0, \
    c128, c129, c131, 0, c131, c132, c131, 0, 0, c132, c128, 0, c128, c132, c134, 0, \
    c128, 0, c128, 0, c134, c129, c128, 0, c131, c129, 0, 0, c128, c135, c133, 0, \
    c131, c129, c134, 0, c128, c129, c131, 0, c128, c140, c128, 0, 0, c129, c128, 0, \
    c131, c132, c131, 0, c133, 0, c131, 0, c131, c129, c128, 0, c128, c129, 0, 0, \
    c131, c132, c128, 0, c131, c135, c128, 0, c128, c129, c139, 0, c131, c132, c128, 0, \
    0, c129, c128, 0, c131, c134, c131, 0, c128, 0, c131, 0, c131, c129, c131, 0, \
    c133, c132, 0, 0, c128, c132, c128, 0, c137, c129, c128, 0, c128, c132, c131, 0, \
    c128, c132, c131, 0, 0, c129, c136, 0, c128, c129, c131, 0, c131, 0, c128, 0, \
    c131, c137, c128, 0, c131, c129, 0, 0, c128, c132, c128, 0, c136, c129, c128, 0, \
    c131, c129, c134, 0, c128, c135, c128, 0, 0, c132, c131, 0, c128, c129, c131, 0, \
    c131, 0, c133, 0, c134, c129, c128, 0, c128, c132, 0, 0, c128, c137, c134, 0, \
    c131, c129, c128, 0, c128, c132, c131, 0, c136, c132, c128, 0, 0, c132, c128, 0, \
    c128, c129, c134, 0, c128, 0, c128, 0, c131, c129, c131, 0, c131, c129, 0, 0, \
    c128, c138, c128, 0, c131, c129, c131, 0, c131, c134, c131, 0, c128, c132, c128, 0, \
    0, c129, c128, 0, c133, c132, c134, 0, c128, 0, c131, 0, c131, c132, c128, 0, \
    c128, c129, 0, 0, c134, c132, c128, 0, c131, c132, c133, 0, c128, c129, c134, 0, \
    c128, c132, c131, 0, 0, c134, c128, 0, c131, c132, c131, 0, c128, 0, c128, 0, \
    c139, c129, c131, 0, c128, c129, 0, 0, c128, c132, c128, 0, c134, c129, c131, 0, \
    c128, c132, c131, 0, c128, c135, c136, 0, 0, c129, c128, 0, c131, c129, c131, 0, \
    c131, 0, c128, 0, c131, c132, c128, 0, c128, c129, 0, 0, c133, c132, c128, 0, \
    c131, c132, c128, 0, c131, c129, c131, 0, c131, c135, c128, 0, 0, c129, c131, 0, \
    c128, c129, c136, 0, c128, 0, c131, 0, c134, c129, c128, 0, c128, c140, 0, 0, \
    c128, c132, c131, 0, c134, c129, c128, 0, c133, c129, c131, 0, c131, c132, c128, 0, \
    0, c132, c131, 0, c128, c129, c134, 0, c128, 0, c128, 0, c131, c129, c133, 0, \
    c134, c129, 0, 0, c128, c135, c128, 0, c131, c134, c131, 0, c128, c129, c134, 0, \
    c128, c132, c128, 0, 0, c132, c128, 0, c128, c132, c131, 0, c131, 0, c131, 0, \
    c131, c129, c128, 0, c128, c129, 0, 0, c131, c132, c136, 0, c131, c132, c128, 0, \
    c128, c132, c134, 0, c128, c137, c128, 0, 0, c129, c128, 0, c131, c129, c131, 0, \
    c133, 0, c128, 0, c131, c129, c134, 0, c128, c129, 0, 0, c128, c135, c128, 0, \
    c134, c129, c128, 0, c131, c132, c136, 0, c128, c132, c131, 0, 0, c129, c128, 0, \
    c128, c134, c134, 0, c131, 0, c128, 0, c131, c135, c128, 0, c133, c129, 0, 0, \
    c131, c132, c128, 0, c131, c129, c128, 0, c131, c129, c131, 0, c128, c135, c131, 0, \
    0, c129, c136, 0, c128, c132, c131, 0, c128, 0, c128, 0, c137, c134, c128, 0, \
    c128, c132, 0, 0, c128, c132, c131, 0, c136, c129, c131, 0, c128, c129, c131, 0, \
    c131, c135, c128, 0, 0, c132, c128, 0, c131, c129, c134, 0, c128, 0, c133, 0, \
    c131, c129, c128, 0, c131, c129, 0, 0, c128, c140, c128, 0, c131, c132, c131, 0, \
    c128, c129, c131, 0, c136, c132, c128, 0, 0, c129, c128, 0, c128, c132, c131, 0, \
    c128, 0, c134, 0, c131, c129, c128, 0, c128, c132, 0, 0, c131, c132, c128, 0, \
    c134, c132, c128, 0, c128, c134, c134, 0, c128, c132, c128, 0, 0, c129, c131, 0, \
    c136, c129, c131, 0, c128, 0, c128, 0, c131, c129, c131, 0, c131, c129, 0, 0, \
    c128, c132, c128, 0, c134, c129, c133, 0, c128, c132, c134, 0, c128, c132, c131, 0, \
    0, c137, c128, 0, c128, c129, c131, 0, c134, 0, c128, 0, c136, c132, c128, 0, \
    c128, c129, 0, 0, c128, c132, c131, 0, c131, c129, c128, 0, c131, c132, c131, 0, \
    c128, c135, c133, 0, 0, c129, c131, 0, c128, c129, c131, 0, c128, 0, c128, 0, \
    c134, c129, c131, 0, c128, c132, 0, 0, c133, c135, c131, 0, c131, c129, c128, 0, \
    c131, c129, c131, 0, c131, c132, c128, 0, 0, c132, c128, 0, c128, c129, c142, 0, \
    c128, 0, c128, 0, c131, c132, c128, 0, c131, c134, 0, 0, c131, c135, c128, 0, \
    c131, c129, c131, 0, c133, c129, c131, 0, c128, c132, c131, 0, 0, c129, c128, 0, \
    c128, c135, c131, 0, c128, 0, c131, 0, c134, c129, c133, 0, c128, c129, 0, 0, \
    c131, c132, c128, 0, c131, c137, c131, 0, c128, c129, c134, 0, c128, c135, c128, 0, \
    0, c129, c128, 0, c134, c129, c131, 0, c128, 0, c128, 0, c131, c129, c131, 0, \
    c128, c129, 0, 0, c128, c132, c133, 0, c134, c132, c128, 0, c128, c132, c131, 0, \
    c131, c137, c131, 0, 0, c129, c128, 0, c128, c129, c131, 0, c136, 0, c131, 0, \
    c131, c132, c128, 0, c128, c132, 0, 0, c128, c132, c128, 0, c134, c129, c128, 0, \
    c131, c129, c136, 0, c128, c135, c128, 0, 0, c129, c134, 0, c128, c134, c131, 0, \
    c128, 0, c128, 0, c134, c129, c128, 0, c136, c132, 0, 0, c128, c132, c131, 0, \
    c131, c129, c128, 0, c128, c129, c134, 0, c131, c132, c128, 0, 0, c135, c133, 0, \
    c128, c129, c134, 0, c131, 0, c128, 0, c131, c134, c128, 0, c131, c129, 0, 0, \
    c128, c135, c131, 0, c136, c129, c131, 0, c128, c132, c131, 0, c128, c132, c128, 0, \
    0, c129, c128, 0, c128, c132, c131, 0, c128, 0, c136, 0, c131, c129, c131, 0, \
    c128, c129, 0, 0, c131, c140, c128, 0, c131, c132, c128, 0, c131, c129, c134, 0, \
    c133, c132, c128, 0, 0, c129, c128, 0, c131, c129, c134, 0, c128, 0, c128, 0, \
    c131, c132, c131, 0, c128, c129, 0, 0, c131, c132, c128, 0, c134, c129, c128, 0, \
    c128, c137, c131, 0, c128, c132, c134, 0, 0, c129, c128, 0, c133, c132, c131, 0, \
    c131, 0, c128, 0, c134, c132, c128, 0, c128, c129, 0, 0, c128, c132, c128, 0, \
    c131, c129, c136, 0, c131, c129, c131, 0, c128, c138, c128, 0, 0, c134, c131, 0, \
    c131, c129, c131, 0, c128, 0, c128, 0, c139, c129, c128, 0, c128, c132, 0, 0, \
    c128, c132, c131, 0, c131, c132, c128, 0, c128, c129, c131, 0, c134, c132, c133, 0, \
    0, c132, c128, 0, c128, c129, c134, 0, c128, 0, c131, 0, c131, c129, c128, 0, \
    c131, c132, 0, 0, c133, c135, c128, 0, c134, c129, c131, 0, c128, c129, c131, 0, \
    c128, c132, c128, 0, 0, c129, c131, 0, c128, c132, c136, 0, c128, 0, c131, 0, \
    c131, c129, c128, 0, c131, c134, 0, 0, c131, c132, c128, 0, c131, c132, c128, 0, \
    c133, c129, c137, 0, c128, c132, c128, 0, 0, c132, c128, 0, c131, c129, c131, 0, \
    c131, 0, c128, 0, c131, c129, c136, 0, c128, c129, 0, 0, c128, c132, c131, 0, \
    c134, c134, c128, 0, c128, c135, c131, 0, c128, c132, c131, 0, 0, c129, c128, 0, \
    c128, c129, c131, 0, c131, 0, c128, 0, c131, c132, c131, 0, c128, c129, 0, 0, \
    c128, c135, c133, 0, c131, c129, c128, 0, c134, c129, c131, 0, c128, c140, c128, 0, \
    0, c129, c131, 0, c128, c129, c134, 0, c133, 0, c128, 0, c134, c132, c128, 0, \
    c128, c132, 0, 0, c131, c132, c131, 0, c131, c129, c128, 0, c128, c129, c136, 0, \
    c131, c132, c131, 0, 0, c132, c128, 0, c128, c137, c134, 0, c128, 0, c128, 0, \
    c134, c129, c128, 0, c136, c129, 0, 0, c128, c135, c128, 0, c131, c129, c134, 0, \
    c128, c129, c131, 0, c128, c135, c128, 0, 0, c129, c133, 0, c131, c132, c131, 0, \
    c128, 0, c131, 0, c131, c134, c128, 0, c128, c129, 0, 0, c131, c132, c128, 0, \
    c136, c135, c128, 0, c128, c129, c134, 0, c131, c132, c128, 0, 0, c129, c128, 0, \
    c131, c129, c131, 0, c128, 0, c136, 0, c131, c129, c131, 0, c128, c132, 0, 0, \
    c128, c137, c128, 0, c137, c129, c128, 0, c128, c132, c131, 0, c133, c132, c131, 0, \
    0, c129, c131, 0, c128, c129, c131, 0, c131, 0, c128, 0, c131, c132, c128, 0, \
    c131, c129, 0, 0, c128, c132, c128, 0, c131, c129, c128, 0, c131, c134, c134, 0, \
    c128, c135, c128, 0, 0, c132, c131, 0, c133, c129, c131, 0, c131, 0, c128, 0, \
    c134, c129, c128, 0, c128, c132, 0, 0, c128, c132, c134, 0, c131, c129, c133, 0, \
    c128, c132, c131, 0, c131, c132, c128, 0, 0, c137, c128, 0, c128, c129, c134, 0, \
    c128, 0, c128, 0, c136, c129, c131, 0, c131, c129, 0, 0, c128, c138, c128, 0, \
    c131, c129, c131, 0, c131, c129, c131, 0, c128, c132, c133, 0, 0, c129, c128, 0, \
    c128, c132, c134, 0, c128, 0, c131, 0, c131, c132, c128, 0, c128, c129, 0, 0, \
    c139, c132, c128, 0, c131, c132, c128, 0, c128, c129, c134, 0, c128, c132, c131, 0, \
    0, c129, c128, 0, c131, c132, c136, 0, c128, 0, c128, 0, c134, c129, c131, 0, \
    c128, c134, 0, 0, c128, c132, c128, 0, c134, c129, c131, 0, c133, c132, c131, 0, \
    c128, c135, c131, 0, 0, c129, c128, 0, c131, c129, c131, 0, c131, 0, c128, 0, \
    c131, c132, c133, 0, c128, c129, 0, 0, c128, c132, c128, 0, c131, c137, c128, 0, \
    c131, c129, c131, 0, c131, c135, c128, 0, 0, c129, c131, 0, c128, c129, c131, 0, \
    c128, 0, c131, 0, c134, c129, c128, 0, c128, c135, 0, 0, c128, c132, c136, 0, \
    c134, c129, c128, 0, c128, c129, c131, 0, c131, c137, c128, 0, 0, c132, c131, 0, \
    c128, c129, c134, 0, c133, 0, c128, 0, c131, c129, c128, 0, c134, c129, 0, 0, \
    c128, c135, c128, 0, c131, c129, c131, 0, c128, c129, c139, 0, c128, c132, c128, 0, \
    0, c132, c128, 0, c128, c137, c131, 0, c131, 0, c131, 0, c131, c129, c128, 0, \
    c133, c129, 0, 0, c131, c132, c131, 0, c131, c132, c128, 0, c128, c132, c134, 0, \
    c128, c132, c128, 0, 0, c129, c133, 0, c131, c129, c131, 0, c128, 0, c128, 0, \
    c131, c134, c134, 0, c128, c129, 0, 0, c128, c135, c128, 0, c139, c129, c128, 0, \
    c131, c132, c131, 0, c128, c132, c131, 0, 0, c129, c128, 0, c128, c129, c134, 0, \
    c131, 0, c133, 0, c131, c135, c128, 0, c128, c129, 0, 0, c131, c137, c128, 0, \
    c131, c129, c128, 0, c131, c129, c131, 0, c133, c135, c131, 0, 0, c129, c131, 0, \
    c128, c132, c131, 0, c128, 0, c128, 0, c137, c129, c128, 0, c128, c132, 0, 0, \
    c128, c132, c131, 0, c131, c129, c131, 0, c128, c134, c131, 0, c131, c135, c128, 0, \
    0, c132, c128, 0, c136, c129, c134, 0, c128, 0, c128, 0, c131, c129, c128, 0, \
    c131, c129, 0, 0, c128, c135, c128, 0, c131, c132, c136, 0, c128, c129, c131, 0, \
    c131, c132, c128, 0, 0, c134, c128, 0, c128, c132, c131, 0, c128, 0, c134, 0, \
    c136, c129, c128, 0, c128, c132, 0, 0, c131, c132, c128, 0, c134, c132, c128, 0, \
    c128, c129, c134, 0, c128, c132, c133, 0, 0, c129, c131, 0, c131, c129, c131, 0, \
    c128, 0, c128, 0, c131, c129, c131, 0, c131, c129, 0, 0, c133, c132, c128, 0, \
    c134, c129, c128, 0, c128, c132, c134, 0, c128, c132, c131, 0, 0, c132, c128, 0, \
    c128, c129, c136, 0, c134, 0, c128, 0, c131, c132, c128, 0, c128, c134, 0, 0, \
    c128, c132, c131, 0, c131, c129, c128, 0, c136, c132, c131, 0, c128, c135, c128, 0, \
    0, c129, c131, 0, c128, c129, c131, 0, c128, 0, c128, 0, c134, c129, c136, 0, \
    c128, c132, 0, 0, c128, c135, c131, 0, c131, c134, c128, 0, c131, c129, c131, 0, \
    c131, c132, c128, 0, 0, c132, c128, 0, c128, c129, c137, 0, c128, 0, c128, 0, \
    c131, c132, c128, 0, c131, c129, 0, 0, c131, c135, c133, 0, c131, c129, c131, 0, \
    c128, c129, c131, 0, c128, c137, c131, 0, 0, c129, c128, 0, c128, c135, c131, 0, \
    c133, 0, c131, 0, c134, c129, c128, 0, c128, c129, 0, 0, c131, c132, c128, 0, \
    c131, c132, c131, 0, c128, c129, c139, 0, c128, c135, c128, 0, 0, c129, c128, 0, \
    c134, c134, c131, 0, c128, 0, c128, 0, c131, c129, c131, 0, c133, c129, 0, 0, \
    c128, c132, c128, 0, c134, c132, c128, 0, c128, c132, c131, 0, c131, c132, c131, 0, \
    0, c129, c133, 0, c128, c129, c131, 0, c131, 0, c131, 0, c131, c137, c128, 0, \
    c128, c132, 0, 0, c128, c132, c128, 0, c139, c129, c128, 0, c131, c129, c131, 0, \
    c128, c135, c128, 0, 0, c129, c134, 0, c128, c129, c131, 0, c128, 0, c133, 0, \
    c134, c129, c128, 0, c131, c132, 0, 0, c128, c137, c131, 0, c131, c129, c128, 0, \
    c128, c129, c134, 0, c136, c132, c128, 0, 0, c135, c128, 0, c128, c129, c134, 0, \
    c131, 0, c128, 0, c131, c129, c128, 0, c131, c129, 0, 0, c128, c135, c131, 0, \
    c131, c129, c131, 0, c128, c137, c131, 0, c128, c132, c128, 0, 0, c129, c128, 0, \
    c133, c132, c131, 0, c128, 0, c131, 0, c131, c129, c131, 0, c128, c129, 0, 0, \
    c131, c135, c128, 0, c131, c132, c133, 0, c131, c129, c134, 0, c128, c132, c128, 0, \
    0, c134, c128, 0, c131, c129, c134, 0, c128, 0, c128, 0, c136, c132, c131, 0, \
    c128, c129, 0, 0, c131, c132, c128, 0, c134, c129, c128, 0, c128, c132, c131, 0, \
    c128, c132, c139, 0, 0, c129, c128, 0, c128, c132, c131, 0, c131, 0, c128, 0, \
    c134, c132, c128, 0, c128, c129, 0, 0, c133, c132, c128, 0, c131, c129, c131, 0, \
    c131, c129, c131, 0, c128, c138, c128, 0, 0, c129, c131, 0, c131, c129, c136, 0, \
    c128, 0, c128, 0, c134, c129, c128, 0, c128, c137, 0, 0, c128, c132, c131, 0, \
    c131, c132, c128, 0, c133, c129, c131, 0, c134, c132, c128, 0, 0, c132, c128, 0, \
    c128, c129, c134, 0, c128, 0, c131, 0, c131, c129, c133, 0, c131, c132, 0, 0, \
    c128, c135, c128, 0, c134, c134, c131, 0, c128, c129, c131, 0, c128, c132, c128, 0, \
    0, c129, c131, 0, c128, c132, c131, 0, c128, 0, c131, 0, c131, c129, c128, 0, \
    c131, c129, 0, 0, c131, c132, c133, 0, c131, c132, c128, 0, c128, c129, c137, 0, \
    c128, c137, c128, 0, 0, c132, c128, 0, c131, c129, c131, 0, c136, 0, c128, 0, \
    c131, c129, c131, 0, c128, c129, 0, 0, c128, c132, c131, 0, c134, c129, c128, 0, \
    c128, c135, c136, 0, c128, c132, c131, 0, 0, c129, c128, 0, c128, c134, c131, 0, \
    c131, 0, c128, 0, c131, c132, c131, 0, c133, c129, 0, 0, c128, c135, c128, 0, \
    c131, c129, c128, 0, c134, c129, c131, 0, c128, c135, c128, 0, 0, c129, c136, 0, \
    c128, c129, c134, 0, c128, 0, c128, 0, c134, c137, c128, 0, c128, c132, 0, 0, \
    c131, c132, c131, 0, c136, c129, c128, 0, c128, c129, c131, 0, c131, c132, c131, 0, \
    0, c132, c128, 0, c128, c132, c134, 0, c128, 0, c133, 0, c134, c129, c128, 0, \
    c131, c129, 0, 0, c128, c140, c128, 0, c131, c129, c134, 0, c128, c129, c131, 0, \
    c133, c135, c128, 0, 0, c129, c128, 0, c131, c132, c131, 0, c128, 0, c131, 0, \
    c131, c129, c128, 0, c128, c129, 0, 0, c131, c132, c128, 0, c131, c135, c128, 0, \
    c128, c134, c134, 0, c131, c132, c128, 0, 0, c129, c128, 0, c136, c129, c131, 0, \
    c128, 0, c131, 0, c131, c129, c131, 0, c128, c132, 0, 0, c128, c132, c128, 0, \
    c137, c129, c133, 0, c128, c132, c131, 0, c128, c132, c131, 0, 0, c134, c131, 0, \
    c128, c129, c131, 0, c131, 0, c128, 0, c136, c132, c128, 0, c131, c129, 0, 0, \
    c128, c132, c128, 0, c131, c129, c128, 0, c131, c129, c134, 0, c128, c135, c133, 0, \
    0, c132, c131, 0, c128, c129, c131, 0, c131, 0, c128, 0, c134, c129, c128, 0, \
    c128, c132, 0, 0, c133, c132, c134, 0, c131, c129, c128, 0, c128, c132, c131, 0, \
    c131, c132, c128, 0, 0, c132, c128, 0, c128, c129, c139, 0, c128, 0, c128, 0, \
    c131, c129, c131, 0, c131, c134, 0, 0, c128, c138, c128, 0, c131, c129, c131, 0, \
    c136, c129, c131, 0, c128, c132, c128, 0, 0, c129, c128, 0, c128, c132, c134, 0, \
    c128, 0, c131, 0, c131, c132, c133, 0, c128, c129, 0, 0, c134, c132, c128, 0, \
    c131, c137, c128, 0, c128, c129, c134, 0, c128, c132, c131, 0, 0, c129, c128, 0, \
    c131, c132, c131, 0, c128, 0, c128, 0, c134, c129, c131, 0, c128, c129, 0, 0, \
    c128, c132, c133, 0, c134, c129, c131, 0, c128, c132, c131, 0, c128, c140, c131, 0, \
    0, c129, c128, 0, c131, c129, c131, 0, c136, 0, c128, 0, c131, c132, c128, 0, \
    c128, c129, 0, 0, c128, c132, c128, 0, c131, c132, c128, 0, c131, c129, c136, 0, \
    c131, c135, c128, 0, 0, c129, c131, 0, c128, c134, c131, 0, c128, 0, c131, 0, \
    c134, c129, c128, 0, c133, c135, 0, 0, c128, c132, c131, 0, c134, c129, c128, 0, \
    c128, c129, c131, 0, c131, c132, c128, 0, 0, c132, c136, 0, c128, c129, c134, 0, \
    c128, 0, c128, 0, c131, c134, c128, 0, c134, c129, 0, 0, c128, c135, c128, 0, \
    c136, c129, c131, 0, c128, c129, c134, 0, c128, c132, c128, 0, 0, c132, c128, 0, \
    c128, c132, c131, 0, c131, 0, c136, 0, c131, c129, c128, 0, c128, c129, 0, 0, \
    c131, c137, c131, 0, c131, c132, c128, 0, c128, c132, c134, 0, c133, c132, c128, 0, \
    0, c129, c128, 0, c131, c129, c131, 0, c128, 0, c128, 0, c131, c129, c134, 0, \
    c128, c129, 0, 0, c128, c135, c128, 0, c134, c129, c128, 0, c131, c137, c131, 0, \
    c128, c132, c131, 0, 0, c129, c128, 0, c133, c129, c134, 0, c131, 0, c128, 0, \
    c131, c135, c128, 0, c128, c129, 0, 0, c131, c132, c128, 0, c131, c129, c133, 0, \
    c131, c129, c131, 0, c128, c135, c131, 0, 0, c134, c131, 0, c128, c132, c131, 0, \
    c128, 0, c128, 0, c142, c129, c128, 0, c128, c132, 0, 0, c128, c132, c131, 0, \
    c131, c129, c131, 0, c128, c129, c131, 0, c131, c135, c133, 0, 0, c132, c128, 0, \
    c131, c129, c134, 0, c128, 0, c128, 0, c131, c129, c128, 0, c131, c129, 0, 0, \
    c133, c135, c128, 0, c131, c132, c131, 0, c128, c129, c131, 0, c131, c132, c128, 0, \
    0, c129, c128, 0, c128, c132, c136, 0, c128, 0, c134, 0, c131, c129, c128, 0, \
    c128, c137, 0, 0, c131, c132, c128, 0, c134, c132, c128, 0, c133, c129, c134, 0, \
    c128, c132, c128, 0, 0, c129, c131, 0, c131, c129, c131, 0, c128, 0, c128, 0, \
    c131, c129, c136, 0, c131, c129, 0, 0, c128, c132, c128, 0, c134, c134, c128, 0, \
    c128, c132, c134, 0, c128, c132, c131, 0, 0, c132, c128, 0, c128, c129, c131, 0, \
    c134, 0, c128, 0, c131, c132, c128, 0, c128, c129, 0, 0, c128, c132, c136, 0, \
    c131, c129, c128, 0, c131, c132, c131, 0, c128, c140, c128, 0, 0, c129, c131, 0, \
    c128, c129, c131, 0, c133, 0, c128, 0, c134, c129, c131, 0, c128, c132, 0, 0, \
    c128, c135, c131, 0, c131, c129, c128, 0, c131, c129, c136, 0, c131, c132, c128, 0, \
    0, c132, c128, 0, c128, c134, c137, 0, c128, 0, c128, 0, c131, c132, c128, 0, \
    c136, c129, 0, 0, c131, c135, c128, 0, c131, c129, c131, 0, c128, c129, c131, 0, \
    c128, c132, c131, 0, 0, c129, c133, 0, c128, c135, c131, 0, c128, 0, c131, 0, \
    c134, c134, c128, 0, c128, c129, 0, 0, c131, c132, c128, 0, c136, c132, c131, 0, \
    c128, c129, c134, 0, c128, c135, c128, 0, 0, c129, c128, 0, c134, c129, c131, 0, \
    c128, 0, c133, 0, c131, c129, c131, 0, c128, c129, 0, 0, c128, c137, c128, 0, \
    c134, c132, c128, 0, c128, c132, c131, 0, c136, c132, c131, 0, 0, c129, c128, 0, \
    c128, c129, c131, 0, c131, 0, c131, 0, c131, c132, c128, 0, c128, c132, 0, 0, \
    c128, c132, c128, 0, c134, c129, c128, 0, c131, c134, c131, 0, c128, c135, c128, 0, \
    0, c129, c134, 0, c133, c129, c131, 0, c128, 0, c128, 0, c134, c129, c128, 0, \
    c131, c132, 0, 0, c128, c132, c131, 0, c131, c129, c133, 0, c128, c129, c134, 0, \
    c131, c132, c128, 0, 0, c140, c128, 0, c128, c129, c134, 0, c131, 0, c128, 0, \
    c136, c129, c128, 0, c131, c129, 0, 0, c128, c135, c131, 0, c131, c129, c131, 0, \
    c128, c132, c131, 0, c128, c132, c133, 0, 0, c129, c128, 0, c128, c132, c131, 0, \
    c128, 0, c131, 0, c131, c129, c131, 0, c128, c129, 0, 0, c136, c135, c128, 0, \
    c131, c132, c128, 0, c131, c129, c134, 0, c128, c132, c128, 0, 0, c129, c128, 0, \
    c131, c129, c139, 0, c128, 0, c128, 0, c131, c132, c131, 0, c128, c134, 0, 0, \
    c131, c132, c128, 0, c134, c129, c128, 0, c133, c132, c131, 0, c128, c132, c134, 0, \
    0, c129, c128, 0, c128, c132, c131, 0, c131, 0, c128, 0, c134, c132, c133, 0, \
    c128, c129, 0, 0, c128, c132, c128, 0, c131, c134, c131, 0, c131, c129, c131, 0, \
    c128, c138, c128, 0, 0, c129, c131, 0, c131, c129, c131, 0, c128, 0, c128, 0, \
    c134, c129, c128, 0, c128, c132, 0, 0, c128, c132, c136, 0, c131, c132, c128, 0, \
    c128, c129, c131, 0, c134, c137, c128, 0, 0, c132, c128, 0, c128, c129, c134, 0, \
    c133, 0, c131, 0, c131, c129, c128, 0, c131, c132, 0, 0, c128, c135, c128, 0, \
    c134, c129, c131, 0, c128, c129, c136, 0, c128, c132, c128, 0, 0, c129, c131, 0, \
    c128, c137, c131, 0, c128, 0, c131, 0, c131, c129, c128, 0, c136, c129, 0, 0, \
    c131, c132, c128, 0, c131, c132, c128, 0, c128, c129, c137, 0, c128, c132, c128, 0, \
    0, c132, c133, 0, c131, c129, c131, 0, c131, 0, c128, 0, c131, c134, c131, 0, \
    c128, c129, 0, 0, c128, c132, c131, 0, c139, c129, c128, 0, c128, c135, c131, 0, \
    c128, c132, c131, 0, 0, c129, c128, 0, c128, c129, c131, 0, c131, 0, c133, 0, \
    c131, c132, c131, 0, c128, c129, 0, 0, c128, c140, c128, 0, c131, c129, c128, 0, \
    c134, c129, c131, 0, c133, c135, c128, 0, 0, c129, c131, 0, c128, c129, c134, 0, \
    c128, 0, c128, 0, c134, c132, c128, 0, c128, c132, 0, 0, c131, c132, c131, 0, \
    c131, c129, c128, 0, c128, c134, c131, 0, c131, c132, c131, 0, 0, c132, c128, 0, \
    c133, c132, c134, 0, c128, 0, c128, 0, c134, c129, c128, 0, c131, c129, 0, 0, \
    c128, c135, c128, 0, c131, c129, c139, 0, c128, c129, c131, 0, c128, c135, c128, 0, \
    0, c134, c128, 0, c131, c132, c131, 0, c128, 0, c131, 0, c136, c129, c128, 0, \
    c128, c129, 0, 0, c131, c132, c128, 0, c131, c135, c128, 0, c128, c129, c134, 0, \
    c131, c132, c133, 0, 0, c129, c128, 0, c131, c129, c131, 0, c128, 0, c131, 0, \
    c131, c129, c131, 0, c128, c132, 0, 0, c133, c132, c128, 0, c137, c129, c128, 0, \
    c128, c132, c131, 0, c128, c132, c131, 0, 0, c129, c131, 0, c128, c129, c136, 0, \
    c131, 0, c128, 0, c131, c132, c128, 0, c131, c134, 0, 0, c128, c132, c128, 0, \
    c131, c129, c128, 0, c136, c129, c134, 0, c128, c135, c128, 0, 0, c132, c131, 0, \
    c128, c129, c131, 0, c131, 0, c128, 0, c134, c129, c133, 0, c128, c132, 0, 0, \
    c128, c132, c134, 0, c131, c134, c128, 0, c128, c132, c131, 0, c131, c132, c128, 0, \
    0, c132, c128, 0, c128, c129, c134, 0, c128, 0, c128, 0, c131, c129, c131, 0, \
    c131, c129, 0, 0, c128, c138, c133, 0, c131, c129, c131, 0, c131, c129, c131, 0, \
    c128, c137, c128, 0, 0, c129, c128, 0, c128, c132, c134, 0, c133, 0, c131, 0, \
    c131, c132, c128, 0, c128, c129, 0, 0, c134, c132, c128, 0, c131, c132, c128, 0, \
    c128, c129, c139, 0, c128, c132, c131, 0, 0, c129, c128, 0, c131, c137, c131, 0, \
    c128, 0, c128, 0, c134, c129, c131, 0, c133, c129, 0, 0, c128, c132, c128, 0, \
    c134, c129, c131, 0, c128, c132, c131, 0, c128, c135, c131, 0, 0, c129, c133, 0, \
    c131, c129, c131, 0, c131, 0, c128, 0, c131, c137, c128, 0, c128, c129, 0, 0, \
    c128, c132, c128, 0, c136, c132, c128, 0, c131, c129, c131, 0, c131, c135, c128, 0, \
    0, c129, c131, 0, c128, c129, c131, 0, c128, 0, c136, 0, c134, c129, c128, 0, \
    c128, c135, 0, 0, c128, c137, c131, 0, c134, c129, c128, 0, c128, c129, c131, 0, \
    c136, c132, c128, 0, 0, c132, c131, 0, c128, c129, c134, 0, c128, 0, c128, 0, \
    c131, c129, c128, 0, c134, c129, 0, 0, c128, c135, c128, 0, c131, c129, c131, 0, \
    c128, c134, c134, 0, c128, c132, c128, 0, 0, c132, c128, 0, c133, c132, c131, 0, \
    c131, 0, c131, 0, c131, c129, c128, 0, c128, c129, 0, 0, c131, c132, c131, 0, \
    c131, c132, c133, 0, c128, c132, c134, 0, c128, c132, c128, 0, 0, c134, c128, 0, \
    c131, c129, c131, 0, c128, 0, c128, 0, c136, c129, c134, 0, c128, c129, 0, 0, \
    c128, c135, c128, 0, c134, c129, c128, 0, c131, c132, c131, 0, c128, c132, c136, 0, \
    0, c129, c128, 0, c128, c129, c134, 0, c131, 0, c128, 0, c131, c135, c128, 0, \
    c128, c129, 0, 0, c136, c132, c128, 0, c131, c129, c128, 0, c131, c129, c131, 0, \
    c128, c135, c131, 0, 0, c129, c131, 0, c128, c132, c136, 0, c128, 0, c128, 0, \
    c137, c129, c128, 0, c128, c137, 0, 0, c128, c132, c131, 0, c131, c129, c131, 0, \
    c133, c129, c131, 0, c131, c135, c128, 0, 0, c132, c128, 0, c131, c129, c134, 0, \
    c128, 0, c128, 0, c131, c129, c133, 0, c131, c129, 0, 0, c128, c135, c128, 0, \
    c131, c137, c131, 0, c128, c129, c131, 0, c131, c132, c128, 0, 0, c129, c128, 0, \
    c128, c132, c131, 0, c128, 0, c134, 0, c131, c129, c128, 0, c128, c132, 0, 0, \
    c131, c132, c133, 0, c134, c132, c128, 0, c128, c129, c134, 0, c128, c137, c128, 0, \
    0, c129, c131, 0, c131, c129, c131, 0, c133, 0, c128, 0, c131, c129, c131, 0, \
    c131, c129, 0, 0, c128, c132, c128, 0, c134, c129, c128, 0, c128, c132, c139, 0, \
    c128, c132, c131, 0, 0, c132, c128, 0, c128, c134, c131, 0, c134, 0, c128, 0, \
    c131, c132, c128, 0, c133, c129, 0, 0, c128, c132, c131, 0, c131, c129, c128, 0, \
    c131, c132, c131, 0, c128, c135, c128, 0, 0, c129, c136, 0, c128, c129, c131, 0, \
    c128, 0, c128, 0, c134, c134, c131, 0, c128, c132, 0, 0, c128, c135, c131, 0, \
    c136, c129, c128, 0, c131, c129, c131, 0, c131, c132, c128, 0, 0, c132, c128, 0, \
    c128, c129, c137, 0, c128, 0, c133, 0, c131, c132, c128, 0, c131, c129, 0, 0, \
    c131, c140, c128, 0, c131, c129, c131, 0, c128, c129, c131, 0, c133, c132, c131, 0, \
    0, c129, c128, 0, c128, c135, c131, 0, c128, 0, c131, 0, c134, c129, c128, 0, \
    c128, c129, 0, 0, c131, c132, c128, 0, c131, c132, c131, 0, c128, c134, c134, 0, \
    c128, c135, c128, 0, 0, c129, c128, 0, c139, c129, c131, 0, c128, 0, c128, 0, \
    c131, c129, c131, 0, c128, c129, 0, 0, c128, c132, c128, 0, c134, c132, c133, 0, \
    c128, c132, c131, 0, c131, c132, c131, 0, 0, c134, c128, 0, c128, c129, c131, 0, \
    c131, 0, c131, 0, c136, c132, c128, 0, c128, c132, 0, 0, c128, c132, c128, 0, \
    c134, c129, c128, 0, c131, c129, c131, 0, c128, c135, c133, 0, 0, c129, c134, 0, \
    c128, c129, c131, 0, c128, 0, c128, 0, c134, c129, c128, 0, c131, c132, 0, 0, \
    c133, c132, c131, 0, c131, c129, c128, 0, c128, c129, c134, 0, c131, c132, c128, 0, \
    0, c135, c128, 0, c128, c129, c139, 0, c131, 0, c128, 0, c131, c129, c128, 0, \
    c131, c134, 0, 0, c128, c135, c131, 0, c131, c129, c131, 0, c133, c132, c131, 0, \
    c128, c132, c128, 0, 0, c129, c128, 0, c128, c132, c131, 0, c128, 0, c131, 0, \
    c131, c129, c136, 0, c128, c129, 0, 0, c131, c135, c128, 0, c131, c137, c128, 0, \
    c131, c129, c134, 0, c128, c132, c128, 0, 0, c129, c128, 0, c131, c129, c134, 0, \
    c128, 0, c128, 0, c131, c132, c131, 0, c128, c129, 0, 0, c131, c132, c133, 0, \
    c134, c129, c128, 0, c128, c132, c131, 0, c128, c137, c134, 0, 0, c129, c128, 0, \
    c128, c132, c131, 0, c136, 0, c128, 0, c134, c132, c128, 0, c128, c129, 0, 0, \
    c128, c132, c128, 0, c131, c129, c131, 0, c131, c129, c136, 0, c128, c138, c128, 0, \
    0, c129, c131, 0, c131, c134, c131, 0, c128, 0, c128, 0, c134, c129, c128, 0, \
    c133, c132, 0, 0, c128, c132, c131, 0, c131, c132, c128, 0, c128, c129, c131, 0, \
    c134, c132, c128, 0, 0, c132, c133, 0, c128, c129, c134, 0, c128, 0, c131, 0, \
    c131, c134, c128, 0, c131, c132, 0, 0, c128, c135, c128, 0, c139, c129, c131, 0, \
    c128, c129, c131, 0, c128, c132, c128, 0, 0, c129, c131, 0, c128, c132, c131, 0, \
    c128, 0, c136, 0, c131, c129, c128, 0, c131, c129, 0, 0, c131, c137, c128, 0, \
    c131, c132, c128, 0, c128, c129, c137, 0, c133, c132, c128, 0, 0, c132, c128, 0, \
    c131, c129, c131, 0, c131, 0, c128, 0, c131, c129, c131, 0, c128, c129, 0, 0, \
    c128, c132, c131, 0, c134, c129, c128, 0, c128, c140, c131, 0, c128, c132, c131, 0, \
    0, c129, c128, 0, c133, c129, c131, 0, c131, 0, c128, 0, c131, c132, c131, 0, \
    c128, c129, 0, 0, c128, c135, c128, 0, c131, c129, c133, 0, c134, c129, c131, 0, \
    c128, c135, c128, 0, 0, c134, c131, 0, c128, c129, c134, 0, c128, 0, c128, 0, \
    c139, c132, c128, 0, c128, c132, 0, 0, c131, c132, c131, 0, c131, c129, c128, 0, \
    c128, c129, c131, 0, c131, c132, c136, 0, 0, c132, c128, 0, c128, c132, c134, 0, \
    c128, 0, c128, 0, c134, c129, c128, 0, c131, c129, 0, 0, c133, c135, c128, 0, \
    c131, c129, c134, 0, c128, c129, c131, 0, c128, c135, c128, 0, 0, c129, c128, 0, \
    c131, c132, c136, 0, c128, 0, c131, 0, c131, c129, c128, 0, c128, c134, 0, 0, \
    c131, c132, c128, 0, c131, c135, c128, 0, c133, c129, c134, 0, c131, c132, c128, 0, \
    0, c129, c128, 0, c131, c129, c131, 0, c128, 0, c131, 0, c131, c129, c136, 0, \
    c128, c132, 0, 0, c128, c132, c128, 0, c137, c134, c128, 0, c128, c132, c131, 0, \
    c128, c132, c131, 0, 0, c129, c131, 0, c128, c129, c131, 0, c131, 0, c128, 0, \
    c131, c132, c128, 0, c131, c129, 0, 0, c128, c132, c133, 0, c131, c129, c128, 0, \
    c131, c129, c134, 0, c128, c140, c128, 0, 0, c132, c131, 0, c128, c129, c131, 0, \
    c136, 0, c128, 0, c134, c129, c128, 0, c128, c132, 0, 0, c128, c132, c134, 0, \
    c131, c129, c128, 0, c128, c132, c136, 0, c131, c132, c128, 0, 0, c132, c128, 0, \
    c128, c134, c134, 0, c128, 0, c128, 0, c131, c129, c131, 0, c136, c129, 0, 0, \
    c128, c138, c128, 0, c131, c129, c131, 0, c131, c129, c131, 0, c128, c132, c128, 0, \
    0, c129, c133, 0, c128, c132, c134, 0, c128, 0, c131, 0, c131, c137, c128, 0, \
    c128, c129, 0, 0, c134, c132, c128, 0, c136, c132, c128, 0, c128, c129, c134, 0, \
    c128, c132, c131, 0, 0, c129, c128, 0, c131, c132, c131, 0, c128, 0, c133, 0, \
    c134, c129, c131, 0, c128, c129, 0, 0, c128, c137, c128, 0, c134, c129, c131, 0, \
    c128, c132, c131, 0, c133, c135, c131, 0, 0, c129, c128, 0, c131, c129, c131, 0, \
    c131, 0, c128, 0, c131, c132, c128, 0, c128, c129, 0, 0, c128, c132, c128, 0, \
    c131, c132, c128, 0, c131, c134, c131, 0, c131, c135, c128, 0, 0, c129, c131, 0, \
    c133, c129, c131, 0, c128, 0, c131, 0, c134, c129, c128, 0, c128, c135, 0, 0, \
    c128, c132, c131, 0, c134, c129, c133, 0, c128, c129, c131, 0, c131, c132, c128, 0, \
    0, c137, c131, 0, c128, c129, c134, 0, c128, 0, c128, 0, c136, c129, c128, 0, \
    c134, c129, 0, 0, c128, c135, c128, 0, c131, c129, c131, 0, c128, c129, c134, 0, \
    c128, c132, c133, 0, 0, c132, c128, 0, c128, c132, c131, 0, c131, 0, c131, 0, \
    c131, c129, c128, 0, c128, c129, 0, 0, c136, c132, c131, 0, c131, c132, c128, 0, \
    c128, c132, c134, 0, c128, c132, c128, 0, 0, c129, c128, 0, c131, c129, c136, 0, \
    c128, 0, c128, 0, c131, c129, c134, 0, c128, c134, 0, 0, c128, c135, c128, 0, \
    c134, c129, c128, 0, c136, c132, c131, 0, c128, c132, c131, 0, 0, c129, c128, 0, \
    c128, c129, c134, 0, c131, 0, c128, 0, c131, c135, c133, 0, c128, c129, 0, 0, \
    c131, c132, c128, 0, c131, c134, c128, 0, c131, c129, c131, 0, c128, c135, c131, 0, \
    0, c129, c131, 0, c128, c132, c131, 0, c128, 0, c128, 0, c137, c129, c128, 0, \
    c128, c132, 0, 0, c128, c132, c136, 0, c131, c129, c131, 0, c128, c129, c131, 0, \
    c131, c140, c128, 0, 0, c132, c128, 0, c131, c129, c134, 0, c133, 0, c128, 0, \
    c131, c129, c128, 0, c131, c129, 0, 0, c128, c135, c128, 0, c131, c132, c131, 0, \
    c128, c129, c136, 0, c131, c132, c128, 0, 0, c129, c128, 0, c128, c137, c131, 0, \
    c128, 0, c134, 0, c131, c129, c128, 0, c133, c132, 0, 0, c131, c132, c128, 0, \
    c134, c132, c128, 0, c128, c129, c134, 0, c128, c132, c128, 0, 0, c129, c136, 0, \
    c131, c129, c131, 0, c128, 0, c128, 0, c131, c134, c131, 0, c131, c129, 0, 0, \
    c128, c132, c128, 0, c139, c129, c128, 0, c128, c132, c134, 0, c128, c132, c131, 0, \
    0, c132, c128, 0, c128, c129, c131, 0, c134, 0, c133, 0, c131, c132, c128, 0, \
    c128, c129, 0, 0, c128, c137, c131, 0, c131, c129, c128, 0, c131, c132, c131, 0, \
    c133, c135, c128, 0, 0, c129, c131, 0, c128, c129, c131, 0, c128, 0, c128, 0, \
    c134, c129, c131, 0, c128, c132, 0, 0, c128, c135, c131, 0, c131, c129, c128, 0, \
    c131, c134, c131, 0, c131, c132, c128, 0, 0, c132, c128, 0, c133, c129, c137, 0, \
    c128, 0, c128, 0, c131, c132, c128, 0, c131, c129, 0, 0, c131, c135, c128, 0, \
    c131, c129, c136, 0, c128, c129, c131, 0, c128, c132, c131, 0, 0, c134, c128, 0, \
    c128, c135, c131, 0, c128, 0, c131, 0, c139, c129, c128, 0, c128, c129, 0, 0, \
    c131, c132, c128, 0, c131, c132, c131, 0, c128, c129, c134, 0, c128, c135, c133, 0, \
    0, c129, c128, 0, c134, c129, c131, 0, c128, 0, c128, 0, c131, c129, c131, 0, \
    c128, c129, 0, 0, c133, c132, c128, 0, c134, c132, c128, 0, c128, c132, c131, 0, \
    c131, c132, c131, 0, 0, c129, c128, 0, c128, c129, c136, 0, c131, 0, c131, 0, \
    c131, c132, c128, 0, c128, c137, 0, 0, c128, c132, c128, 0, c134, c129, c128, 0, \
    c136, c129, c131, 0, c128, c135, c128, 0, 0, c129, c134, 0, c128, c129, c131, 0, \
    c128, 0, c128, 0, c134, c129, c133, 0, c131, c132, 0, 0, c128, c132, c131, 0, \
    c131, c134, c128, 0, c128, c129, c134, 0, c131, c132, c128, 0, 0, c135, c128, 0, \
    c128, c129, c134, 0, c131, 0, c128, 0, c131, c129, c128, 0, c131, c129, 0, 0, \
    c128, c135, c136, 0, c131, c129, c131, 0, c128, c132, c131, 0, c128, c137, c128, 0, \
    0, c129, c128, 0, c128, c132, c131, 0, c133, 0, c131, 0, c131, c129, c131, 0, \
    c128, c129, 0, 0, c131, c135, c128, 0, c131, c132, c128, 0, c131, c129, c139, 0, \
    c128, c132, c128, 0, 0, c129, c128, 0, c131, c134, c134, 0, c128, 0, c128, 0, \
    c131, c132, c131, 0, c133, c129, 0, 0, c131, c132, c128, 0, c134, c129, c128, 0, \
    c128, c132, c131, 0, c128, c132, c134, 0, 0, c129, c133, 0, c128, c132, c131, 0, \
    c131, 0, c128, 0, c134, c137, c128, 0, c128, c129, 0, 0, c128, c132, c128, 0, \
    c136, c129, c131, 0, c131, c129, c131, 0, c128, c138, c128, 0, 0, c129, c131, 0, \
    c131, c129, c131, 0, c128, 0, c133, 0, c134, c129, c128, 0, c128, c132, 0, 0, \
    c128, c137, c131, 0, c131, c132, c128, 0, c128, c129, c131, 0, c139, c132, c128, 0, \
    0, c132, c128, 0, c128, c129, c134, 0, c128, 0, c131, 0, c131, c129, c128, 0, \
    c131, c132, 0, 0, c128, c135, c128, 0, c134, c129, c131, 0, c128, c134, c131, 0, \
    c128, c132, c128, 0, 0, c129, c131, 0, c133, c132, c131, 0, c128, 0, c131, 0, \
    c131, c129, c128, 0, c131, c129, 0, 0, c131, c132, c128, 0, c131, c132, c133, 0, \
    c128, c129, c137, 0, c128, c132, c128, 0, 0, c137, c128, 0, c131, c129, c131, 0, \
    c131, 0, c128, 0, c136, c129, c131, 0, c128, c129, 0, 0, c128, c132, c131, 0, \
    c134, c129, c128, 0, c128, c135, c131, 0, c128, c132, c136, 0, 0, c129, c128, 0, \
    c128, c129, c131, 0, c131, 0, c128, 0, c131, c132, c131, 0, c128, c129, 0, 0, \
    c133, c135, c128, 0, c131, c129, c128, 0, c134, c129, c131, 0, c128, c135, c128, 0, \
    0, c129, c131, 0, c128, c129, c139, 0, c128, 0, c128, 0, c134, c132, c128, 0, \
    c128, c137, 0, 0, c131, c132, c131, 0, c131, c129, c128, 0, c133, c129, c131, 0, \
    c131, c132, c131, 0, 0, c132, c128, 0, c128, c132, c134, 0, c128, 0, c128, 0, \
    c134, c129, c133, 0, c131, c129, 0, 0, c128, c135, c128, 0, c131, c134, c134, 0, \
    c128, c129, c131, 0, c128, c135, c128, 0, 0, c129, c128, 0, c131, c132, c131, 0, \
    c128, 0, c131, 0, c131, c129, c128, 0, c128, c129, 0, 0, c131, c132, c133, 0, \
    c131, c135, c128, 0, c128, c129, c134, 0, c131, c137, c128, 0, 0, c129, c128, 0, \
    c131, c129, c131, 0, c133, 0, c131, 0, c131, c129, c131, 0, c128, c132, 0, 0, \
    c128, c132, c128, 0, c137, c129, c128, 0, c128, c132, c136, 0, c128, c132, c131, 0, \
    0, c129, c131, 0, c128, c134, c131, 0, c131, 0, c128, 0, c131, c132, c128, 0, \
    c136, c129, 0, 0, c128, c132, c128, 0, c131, c129, c128, 0, c131, c129, c134, 0, \
    c128, c135, c128, 0, 0, c132, c136, 0, c128, c129, c131, 0, c131, 0, c128, 0, \
    c134, c134, c128, 0, c128, c132, 0, 0, c128, c132, c134, 0, c136, c129, c128, 0, \
    c128, c132, c131, 0, c131, c132, c128, 0, 0, c132, c128, 0, c128, c129, c134, 0, \
    c128, 0, c133, 0, c131, c129, c131, 0, c131, c129, 0, 0, c128, c143, c128, 0, \
    c131, c129, c131, 0, c131, c129, c131, 0, c133, c132, c128, 0, 0, c129, c128, 0, \
    c128, c132, c134, 0, c128, 0, c131, 0, c131, c132, c128, 0, c128, c129, 0, 0, \
    c134, c132, c128, 0, c131, c132, c128, 0, c128, c134, c134, 0, c128, c132, c131, 0, \
    0, c129, c128, 0, c136, c132, c131, 0, c128, 0, c128, 0, c134, c129, c131, 0, \
    c128, c129, 0, 0, c128, c132, c128, 0, c134, c129, c136, 0, c128, c132, c131, 0, \
    c128, c135, c131, 0, 0, c134, c128, 0, c131, c129, c131, 0, c131, 0, c128, 0, \
    c136, c132, c128, 0, c128, c129, 0, 0, c128, c132, c128, 0, c131, c132, c128, 0, \
    c131, c129, c131, 0, c131, c135, c133, 0, 0, c129, c131, 0, c128, c129, c131, 0, \
    c128, 0, c131, 0, c134, c129, c128, 0, c128, c135, 0, 0, c133, c132, c131, 0, \
    c134, c129, c128, 0, c128, c129, c131, 0, c131, c132, c128, 0, 0, c132, c131, 0, \
    c128, c129, c139, 0, c128, 0, c128, 0, c131, c129, c128, 0, c134, c134, 0, 0, \
    c128, c135, c128, 0, c131, c129, c131, 0, c133, c129, c134, 0, c128, c132, c128, 0, \
    0, c132, c128, 0, c128, c132, c131, 0, c131, 0, c131, 0, c131, c129, c133, 0, \
    c128, c129, 0, 0, c131, c132, c131, 0, c131, c137, c128, 0, c128, c132, c134, 0, \
    c128, c132, c128, 0, 0, c129, c128, 0, c131, c129, c131, 0, c128, 0, c128, 0, \
    c131, c129, c134, 0, c128, c129, 0, 0, c128, c135, c133, 0, c134, c129, c128, 0, \
    c131, c132, c131, 0, c128, c137, c131, 0, 0, c129, c128, 0, c128, c129, c134, 0, \
    c136, 0, c128, 0, c131, c135, c128, 0, c128, c129, 0, 0, c131, c132, c128, 0, \
    c131, c129, c128, 0, c131, c129, c136, 0, c128, c135, c131, 0, 0, c129, c131, 0, \
    c128, c137, c131, 0, c128, 0, c128, 0, c137, c129, c128, 0, c133, c132, 0, 0, \
    c128, c132, c131, 0, c131, c129, c131, 0, c128, c129, c131, 0, c131, c135, c128, 0, \
    0, c132, c133, 0, c131, c129, c134, 0, c128, 0, c128, 0, c131, c134, c128, 0, \
    c131, c129, 0, 0, c128, c135, c128, 0, c136, c132, c131, 0, c128, c129, c131, 0, \
    c131, c132, c128, 0, 0, c129, c128, 0, c128, c132, c131, 0, c128, 0, c139, 0, \
    c131, c129, c128, 0, c128, c132, 0, 0, c131, c137, c128, 0, c134, c132, c128, 0, \
    c128, c129, c134, 0, c133, c132, c128, 0, 0, c129, c131, 0, c131, c129, c131, 0, \
    c128, 0, c128, 0, c131, c129, c131, 0, c131, c129, 0, 0, c128, c132, c128, 0, \
    c134, c129, c128, 0, c128, c137, c134, 0, c128, c132, c131, 0, 0, c132, c128, 0, \
    c133, c129, c131, 0, c134, 0, c128, 0, c131, c132, c128, 0, c128, c129, 0, 0, \
    c128, c132, c131, 0, c131, c129, c133, 0, c131, c132, c131, 0, c128, c135, c128, 0, \
    0, c134, c131, 0, c128, c129, c131, 0, c128, 0, c128, 0, c139, c129, c131, 0, \
    c128, c132, 0, 0, c128, c135, c131, 0, c131, c129, c128, 0, c131, c129, c131, 0, \
    c131, c132, c133, 0, 0, c132, c128, 0, c128, c129, c137, 0, c128, 0, c128, 0, \
    c131, c132, c128, 0, c131, c129, 0, 0, c136, c135, c128, 0, c131, c129, c131, 0, \
    c128, c129, c131, 0, c128, c132, c131, 0, 0, c129, c128, 0, c128, c135, c136, 0, \
    c128, 0, c131, 0, c134, c129, c128, 0, c128, c134, 0, 0, c131, c132, c128, 0, \
    c131, c132, c131, 0, c133, c129, c134, 0, c128, c135, c128, 0, 0, c129, c128, 0, \
    c134, c129, c131, 0, c128, 0, c128, 0, c131, c129, c136, 0, c128, c129, 0, 0, \
    c128, c132, c128, 0, c134, c137, c128, 0, c128, c132, c131, 0, c131, c132, c131, 0, \
    0, c129, c128, 0, c128, c129, c131, 0, c131, 0, c131, 0, c131, c132, c128, 0, \
    c128, c132, 0, 0, c128, c132, c133, 0, c134, c129, c128, 0, c131, c129, c131, 0, \
    c128, c140, c128, 0, 0, c129, c134, 0, c128, c129, c131, 0, c133, 0, c128, 0, \
    c134, c129, c128, 0, c131, c132, 0, 0, c128, c132, c131, 0, c131, c129, c128, 0, \
    c128, c129, c139, 0, c131, c132, c128, 0, 0, c135, c128, 0, c128, c134, c134, 0, \
    c131, 0, c128, 0, c131, c129, c128, 0, c136, c129, 0, 0, c128, c135, c131, 0, \
    c131, c129, c131, 0, c128, c132, c131, 0, c128, c132, c128, 0, 0, c129, c133, 0, \
    c128, c132, c131, 0, c128, 0, c131, 0, c131, c134, c131, 0, c128, c129, 0, 0, \
    c131, c135, c128, 0, c136, c132, c128, 0, c131, c129, c134, 0, c128, c132, c128, 0, \
    0, c129, c128, 0, c131, c129, c134, 0, c128, 0, c133, 0, c131, c132, c131, 0, \
    c128, c129, 0, 0, c131, c137, c128, 0, c134, c129, c128, 0, c128, c132, c131, 0, \
    c133, c132, c134, 0, 0, c129, c128, 0, c128, c132, c131, 0, c131, 0, c128, 0, \
    c134, c132, c128, 0, c128, c129, 0, 0, c128, c132, c128, 0, c131, c129, c131, 0, \
    c131, c134, c131, 0, c128, c138, c128, 0, 0, c129, c131, 0, c136, c129, c131, 0, \
    c128, 0, c128, 0, c134, c129, c128, 0, c128, c132, 0, 0, c128, c132, c131, 0, \
    c131, c132, c133, 0, c128, c129, c131, 0, c134, c132, c128, 0, 0, c137, c128, 0, \
    c128, c129, c134, 0, c128, 0, c131, 0, c136, c129, c128, 0, c131, c132, 0, 0, \
    c128, c135, c128, 0, c134, c129, c131, 0, c128, c129, c131, 0, c128, c132, c133, 0, \
    0, c129, c131, 0, c128, c132, c131, 0, c128, 0, c131, 0, c131, c129, c128, 0, \
    c131, c129, 0, 0, c136, c132, c128, 0, c131, c132, c128, 0, c128, c129, c137, 0, \
    c128, c132, c128, 0, 0, c132, c128, 0, c131, c129, c136, 0, c131, 0, c128, 0, \
    c131, c129, c131, 0, c128, c134, 0, 0, c128, c132, c131, 0, c134, c129, c128, 0, \
    c133, c135, c131, 0, c128, c132, c131, 0, 0, c129, c128, 0, c128, c129, c131, 0, \
    c131, 0, c128, 0, c131, c132, c136, 0, c128, c129, 0, 0, c128, c135, c128, 0, \
    c131, c134, c128, 0, c134, c129, c131, 0, c128, c135, c128, 0, 0, c129, c131, 0, \
    c128, c129, c134, 0, c128, 0, c128, 0, c134, c132, c128, 0, c128, c132, 0, 0, \
    c131, c132, c136, 0, c131, c129, c128, 0, c128, c129, c131, 0, c131, c137, c131, 0, \
    0, c132, c128, 0, c128, c132, c134, 0, c133, 0, c128, 0, c134, c129, c128, 0, \
    c131, c129, 0, 0, c128, c135, c128, 0, c131, c129, c134, 0, c128, c129, c136, 0, \
    c128, c135, c128, 0, 0, c129, c128, 0, c131, c137, c131, 0, c128, 0, c131, 0, \
    c131, c129, c128, 0, c133, c129, 0, 0, c131, c132, c128, 0, c131, c135, c128, 0, \
    c128, c129, c134, 0, c131, c132, c128, 0, 0, c129, c133, 0, c131, c129, c131, 0, \
    c128, 0, c131, 0, c131, c134, c131, 0, c128, c132, 0, 0, c128, c132, c128, 0, \
    c142, c129, c128, 0, c128, c132, c131, 0, c128, c132, c131, 0, 0, c129, c131, 0, \
    c128, c129, c131, 0, c131, 0, c133, 0, c131, c132, c128, 0, c131, c129, 0, 0, \
    c128, c137, c128, 0, c131, c129, c128, 0, c131, c129, c134, 0, c133, c135, c128, 0, \
    0, c132, c131, 0, c128, c129, c131, 0, c131, 0, c128, 0, c134, c129, c128, 0, \
    c128, c132, 0, 0, c128, c132, c134, 0, c131, c129, c128, 0, c128, c137, c131, 0, \
    c131, c132, c128, 0, 0, c132, c128, 0, c133, c129, c134, 0, c128, 0, c128, 0, \
    c131, c129, c131, 0, c131, c129, 0, 0, c128, c138, c128, 0, c131, c129, c136, 0, \
    c131, c129, c131, 0, c128, c132, c128, 0, 0, c134, c128, 0, c128, c132, c134, 0, \
    c128, 0, c131, 0, c136, c132, c128, 0, c128, c129, 0, 0, c134, c132, c128, 0, \
    c131, c132, c128, 0, c128, c129, c134, 0, c128, c132, c136, 0, 0, c129, c128, 0, \
    c131, c132, c131, 0, c128, 0, c128, 0, c134, c129, c131, 0, c128, c129, 0, 0, \
    c133, c132, c128, 0, c134, c129, c131, 0, c128, c132, c131, 0, c128, c135, c131, 0, \
    0, c129, c128, 0, c131, c129, c136, 0, c131, 0, c128, 0, c131, c132, c128, 0, \
    c128, c134, 0, 0, c128, c132, c128, 0, c131, c132, c128, 0, c136, c129, c131, 0, \
    c131, c135, c128, 0, 0, c129, c131, 0, c128, c129, c131, 0, c128, 0, c131, 0, \
    c134, c129, c133, 0, c128, c135, 0, 0, c128, c132, c131, 0, c134, c134, c128, 0, \
    c128, c129, c131, 0, c131, c132, c128, 0, 0, c132, c131, 0, c128, c129, c134, 0, \
    c128, 0, c128, 0, c131, c129, c128, 0, c134, c129, 0, 0, c128, c135, c133, 0, \
    c131, c129, c131, 0, c128, c129, c134, 0, c128, c137, c128, 0, 0, c132, c128, 0, \
    c128, c132, c131, 0, c136, 0, c131, 0, c131, c129, c128, 0, c128, c129, 0, 0, \
    c131, c132, c131, 0, c131, c132, c128, 0, c128, c132, c139, 0, c128, c132, c128, 0, \
    0, c129, c128, 0, c131, c134, c131, 0, c128, 0, c128, 0, c131, c129, c134, 0, \
    c133, c129, 0, 0, c128, c135, c128, 0, c134, c129, c128, 0, c131, c132, c131, 0, \
    c128, c132, c131, 0, 0, c129, c133, 0, c128, c129, c134, 0, c131, 0, c128, 0, \
    c131, c140, c128, 0, c128, c129, 0, 0, c131, c132, c128, 0, c136, c129, c128, 0, \
    c131, c129, c131, 0, c128, c135, c131, 0, 0, c129, c131, 0, c128, c132, c131, 0, \
    c128, 0, c133, 0, c137, c129, c128, 0, c128, c132, 0, 0, c128, c137, c131, 0, \
    c131, c129, c131, 0, c128, c129, c131, 0, c136, c135, c128, 0, 0, c132, c128, 0, \
    c131, c129, c134, 0, c128, 0, c128, 0, c131, c129, c128, 0, c131, c129, 0, 0, \
    c128, c135, c128, 0, c131, c132, c131, 0, c128, c134, c131, 0, c131, c132, c128, 0, \
    0, c129, c128, 0, c133, c132, c131, 0, c128, 0, c134, 0, c131, c129, c128, 0, \
    c128, c132, 0, 0, c131, c132, c128, 0, c134, c132, c133, 0, c128, c129, c134, 0, \
    c128, c132, c128, 0, 0, c134, c131, 0, c131, c129, c131, 0, c128, 0, c128, 0, \
    c136, c129, c131, 0, c131, c129, 0, 0, c128, c132, c128, 0, c134, c129, c128, 0, \
    c128, c132, c134, 0, c128, c132, c136, 0, 0, c132, c128, 0, c128, c129, c131, 0, \
    c134, 0, c128, 0, c131, c132, c128, 0, c128, c129, 0, 0, c133, c132, c131, 0, \
    c131, c129, c128, 0, c131, c132, c131, 0, c128, c135, c128, 0, 0, c129, c131, 0, \
    c128, c129, c136, 0, c128, 0, c128, 0, c134, c129, c131, 0, c128, c137, 0, 0, \
    c128, c135, c131, 0, c131, c129, c128, 0, c136, c129, c131, 0, c131, c132, c128, 0, \
    0, c132, c128, 0, c128, c129, c137, 0, c128, 0, c128, 0, c131, c132, c133, 0, \
    c131, c129, 0, 0, c131, c135, c128, 0, c131, c134, c131, 0, c128, c129, c131, 0, \
    c128, c132, c131, 0, 0, c129, c128, 0, c128, c135, c131, 0, c128, 0, c131, 0, \
    c134, c129, c128, 0, c128, c129, 0, 0, c131, c132, c133, 0, c131, c132, c131, 0, \
    c128, c129, c134, 0, c128, c140, c128, 0, 0, c129, c128, 0, c134, c129, c131, 0, \
    c133, 0, c128, 0, c131, c129, c131, 0, c128, c129, 0, 0, c128, c132, c128, 0, \
    c134, c132, c128, 0, c128, c132, c136, 0, c131, c132, c131, 0, 0, c129, c128, 0, \
    c128, c134, c131, 0, c131, 0, c131, 0, c131, c132, c128, 0, c133, c132, 0, 0, \
    c128, c132, c128, 0, c134, c129, c128, 0, c131, c129, c131, 0, c128, c135, c128, 0, \
    0, c129, c139, 0, c128, c129, c131, 0, c128, 0, c128, 0, c134, c134, c128, 0, \
    c131, c132, 0, 0, c128, c132, c131, 0, c136, c129, c128, 0, c128, c129, c134, 0, \
    c131, c132, c128, 0, 0, c135, c128, 0, c128, c129, c134, 0, c131, 0, c133, 0, \
    c131, c129, c128, 0, c131, c129, 0, 0, c128, c140, c131, 0, c131, c129, c131, 0, \
    c128, c132, c131, 0, c133, c132, c128, 0, 0, c129, c128, 0, c128, c132, c131, 0, \
    c128, 0, c131, 0, c131, c129, c131, 0, c128, c129, 0, 0, c131, c135, c128, 0, \
    c131, c132, c128, 0, c131, c134, c134, 0, c128, c132, c128, 0, 0, c129, c128, 0, \
    c136, c129, c134, 0, c128, 0, c128, 0, c131, c132, c131, 0, c128, c129, 0, 0, \
    c131, c132, c128, 0, c134, c129, c133, 0, c128, c132, c131, 0, c128, c132, c134, 0, \
    0, c134, c128, 0, c128, c132, c131, 0, c131, 0, c128, 0, c139, c132, c128, 0, \
    c128, c129, 0, 0, c128, c132, c128, 0, c131, c129, c131, 0, c131, c129, c131, 0, \
    c128, c138, c133, 0, 0, c129, c131, 0, c131, c129, c131, 0, c128, 0, c128, 0, \
    c134, c129, c128, 0, c128, c132, 0, 0, c133, c132, c131, 0, c131, c132, c128, 0, \
    c128, c129, c131, 0, c134, c132, c128, 0, 0, c132, c128, 0, c128, c129, c139, 0, \
    c128, 0, c131, 0, c131, c129, c128, 0, c131, c137, 0, 0, c128, c135, c128, 0, \
    c134, c129, c131, 0, c133, c129, c131, 0, c128, c132, c128, 0, 0, c129, c131, 0, \
    c128, c132, c131, 0, c128, 0, c131, 0, c131, c129, c133, 0, c131, c129, 0, 0, \
    c131, c132, c128, 0, c131, c137, c128, 0, c128, c129, c137, 0, c128, c132, c128, 0, \
    0, c132, c128, 0, c131, c129, c131, 0, c131, 0, c128, 0, c131, c129, c131, 0, \
    c128, c129, 0, 0, c128, c132, c136, 0, c134, c129, c128, 0, c128, c135, c131, 0, \
    c128, c137, c131, 0, 0, c129, c128, 0, c128, c129, c131, 0, c136, 0, c128, 0, \
    c131, c132, c131, 0, c128, c129, 0, 0, c128, c135, c128, 0, c131, c129, c128, 0, \
    c134, c129, c136, 0, c128, c135, c128, 0, 0, c129, c131, 0, c128, c134, c134, 0, \
    c128, 0, c128, 0, c134, c132, c128, 0, c133, c132, 0, 0, c131, c132, c131, 0, \
    c131, c129, c128, 0};

#undef c128
#undef c129
#undef c130
#undef c131
#undef c132
#undef c133
#undef c134
#undef c135
#undef c136
#undef c137
#undef c138
#undef c139
#undef c140
#undef c141
#undef c142
#undef c143

// END upstream stencil_data.h

// BEGIN upstream SegmentedMobiusSieve.cpp
#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstring>
#include <omp.h>

// Toggle the large-prime bucket scheduler. When disabled, all primes above
// M1_PRIME_CAP are sieved as tiled medium primes (direct iteration per sub-segment).
// Override at build time: -DUSE_BUCKET_SIEVE=0
#ifndef USE_BUCKET_SIEVE
#define USE_BUCKET_SIEVE 1
#endif
static constexpr bool UseBucketSieve = USE_BUCKET_SIEVE;

// Cutoffs for the tiled-medium path. At high sieve bounds,
// a larger direct tile exposes more independent memory traffic and the sparse
// top prime band is cheaper to traverse directly than to schedule in buckets.
static constexpr UInt64 MEDIUM_TILE_SWITCH     = UInt64(1) << 36;
static constexpr UInt64 MEDIUM_TILE_LARGE      = UInt64(168) * SegmentedMobiusSieveCore::STENCIL_PERIOD;
static constexpr UInt64 TILED_DIRECT_SIEVE_CUTOFF =
    UInt64(200) * SegmentedMobiusSieveCore::STENCIL_PERIOD;

// The rolling block walk predates the wider tiled-medium path. Retain it as a
// compile-time portability knob, but use the tiled path by default: the latter
// now wins for separately finalized Mobius sieves across tested segment sizes
// and sieve heights. Override at build time: -DSIEVE_FINALIZE_BLOCK_WALK=1
#ifndef SIEVE_FINALIZE_BLOCK_WALK
#define SIEVE_FINALIZE_BLOCK_WALK 0
#endif
static constexpr bool UseFinalizeBlockWalk = SIEVE_FINALIZE_BLOCK_WALK;

// Experimental: split sieveSubSegment's hit loop into a pure-scatter RMW pass and
// a pure-ALU forwarding pass. Override at build time: -DSIEVE_TWO_PASS=1
#ifndef SIEVE_TWO_PASS
#define SIEVE_TWO_PASS 0
#endif

// Adaptive threshold for large-prime routing strategy.
// When numSegments * LP_ROUTE_THRESHOLD >= numLargePrimes, use single-pass
// serial routing (Option A); otherwise use parallel per-thread constructors.
// On ARM the threshold defaults to 0 (parallel constructors always): serial
// routing runs on one core while the rest idle, and with fast hardware
// division the redundant parallel scan wins beyond a few threads. On x86 the
// division-free routing iterations are cheaper, so Option A keeps a threshold.
// Override at build time: -DLP_ROUTE_THRESHOLD=15000
#ifndef LP_ROUTE_THRESHOLD
#if defined(__aarch64__) || defined(__arm64__)
#define LP_ROUTE_THRESHOLD 0
#else
#define LP_ROUTE_THRESHOLD 15000
#endif
#endif

// ============================================================================
// Construction
// ============================================================================

SegmentedMobiusSieveCore::SegmentedMobiusSieveCore()
    : mStencilData(stencil, stencil + STENCIL_PERIOD)
    , mM1PrimeStopIdx(2)   // skip past primes 2,3 (indices 0,1 in typical prime list)
    , mSqrtPrimeStopIdx(2)
{}

SegmentedMobiusSieveCore::SegmentedMobiusSieveCore(UInt64 segmentSize)
    : SegmentedMobiusSieveCore()
{
    initialize(segmentSize);
}

// ============================================================================
// Setup
// ============================================================================

void SegmentedMobiusSieveCore::initialize(UInt64 segmentSize) {
    mBuckets.resize(0);
    mBuckets.resize(omp_get_max_threads());

    fillFromStencil(segmentSize);
    mMu.resize(segmentSize);

    mPreMu.resize(M1 + STENCIL_PERIOD);
    for (UInt64 off = 0; off < M1 + STENCIL_PERIOD; off += STENCIL_PERIOD)
        std::memcpy(mPreMu.data() + off, mStencilData.data(), STENCIL_PERIOD * sizeof(Int8));

    mM1PrimeStopIdx = 2;  // NUM_PRIME_SQUARES = 2 (skip 2, 3)
    mSqrtPrimeStopIdx = 2;
}

void SegmentedMobiusSieveCore::initSieveQuotientCache(const std::vector<UInt32>& primes) {
    if constexpr (UseDivisionFree) {
        mSieveQCache.init(primes.data(), primes.size());
    }
}

void SegmentedMobiusSieveCore::fillFromStencil(UInt64 size) {
    mMu.resize(size);
    Int8* dst = mMu.data();

    // Pick a tile size that makes memcpy hit peak throughput (~4 MiB).
    UInt64 tile = STENCIL_PERIOD * ((4u << 20) / STENCIL_PERIOD + 1);
    if (tile == 0) tile = STENCIL_PERIOD;
    tile = std::min(tile, size);

    // Build tile: one stencil copy + doubling-fill inside tile
    std::vector<Int8> T(tile);
    UInt64 initCopy = std::min(tile, (UInt64)STENCIL_PERIOD);
    std::memcpy(T.data(), mStencilData.data(), initCopy);
    UInt64 filled = initCopy;
    while (filled < tile) {
        UInt64 n = std::min(filled, tile - filled);
        std::memcpy(T.data() + filled, T.data(), n);
        filled += n;
    }

    // Parallel tile copies into destination
    const UInt64 nt = (size + tile - 1) / tile;

    #pragma omp parallel for schedule(static)
    for (UInt64 i = 0; i < nt; ++i) {
        UInt64 off = i * tile;
        UInt64 n   = std::min(tile, size - off);
        std::memcpy(dst + off, T.data(), n);
    }
}

// ============================================================================
// Utility: prime generation
// ============================================================================

std::vector<UInt32> SegmentedMobiusSieveCore::primesUpTo(UInt32 n) {
    std::vector<UInt32> S(n);

    for (Int32 i = 2; i <= (Int32)n; ++i)
        S[i - 2] = i;

    const Int32 sqrtn = static_cast<Int32>(std::sqrt((double)n));
    for (Int32 i = 1; i <= sqrtn; ++i) {
        if (S[i - 1] != 0) {
            for (Int32 k = 2 * i + 1; k <= (Int32)n - 1; k += i + 1)
                S[k - 1] = 0;
        }
    }

    S.erase(std::remove(S.begin(), S.end(), (UInt32)0), S.end());
    return S;
}

// ============================================================================
// Main sieve entry point
// ============================================================================

template<bool Finalize>
void SegmentedMobiusSieveCore::sieve(UInt64 lo, UInt64 hi, const std::vector<UInt32>& P) {
    assert(P.size() >= 71 && "prime list must have at least 71 entries (primes up to 353)");

    // Auto-initialize quotient cache on first use if needed
    if constexpr (UseDivisionFree) {
        if (mSieveQCache.count < P.size())
            initSieveQuotientCache(P);

        // The Granlund-Montgomery formulation with SHIFT=60 is exact only
        // for arguments below 2^60. ceilDiv computes val = x + p - 1 with
        // x <= hi and p < 2^32, so require hi < 2^60 - 2^32. The default
        // bucket-sieve range cap (2.05e17) is far below this; only
        // BUCKET_SIEVE=0 builds, where the encoding stays exact to ~1.8e19,
        // can reach it — those must use DIVISION_FREE=0 past this bound.
        assert(hi < (1ULL << 60) - (1ULL << 32) &&
               "DIVISION_FREE=1 requires hi < 2^60 - 2^32 (quotient cache domain)");
    }

    const UInt64 len = hi - lo + 1;
    Int8* MuP = mMu.data();
    const UInt64 stencilOff = (lo <= 1) ? 0 : (lo - 1) % STENCIL_PERIOD;

    const UInt64 sqrtHi = std::round(std::sqrt((double)hi));

    if (sqrtHi < M1_PRIME_CAP) {
        while (mM1PrimeStopIdx < P.size() && sqrtHi >= P[mM1PrimeStopIdx])
            ++mM1PrimeStopIdx;

        mSqrtPrimeStopIdx = mM1PrimeStopIdx;

        #pragma omp parallel for schedule(dynamic, 1)
        for (UInt64 l = 0; l < len; l += M1) {
            std::memcpy(MuP + l, mPreMu.data() + stencilOff,
                        sizeof(Int8) * std::min(static_cast<UInt64>(M1), len - l));
            sieveM1PrimeRange(MuP + l, P.data(), lo + l, std::min(lo + l + M1 - 1, hi),
                              mM1PrimeStopIdx, &mSieveQCache);
        }

        sieveSquaresPass(MuP, P.data(), lo, hi, 71, mSqrtPrimeStopIdx, &mSieveQCache);

        if constexpr (Finalize) {
            #pragma omp parallel for schedule(dynamic, 1)
            for (UInt64 l = 0; l < len; l += M1)
                finalizeMu(MuP + l, lo + l, std::min(lo + l + M1 - 1, hi));
        }

        return;
    }

    // Establish mM1PrimeStopIdx = first prime index with p > M1_PRIME_CAP.
    while (mM1PrimeStopIdx < P.size()
           && (UInt64)P[mM1PrimeStopIdx] <= (UInt64)M1_PRIME_CAP)
        ++mM1PrimeStopIdx;

    // establish mSqrtPrimeStopIdx = first prime index with p > sqrtHi
    mSqrtPrimeStopIdx = mM1PrimeStopIdx;
    while (mSqrtPrimeStopIdx < P.size() && (UInt64)P[mSqrtPrimeStopIdx] <= sqrtHi)
        ++mSqrtPrimeStopIdx;

    // Guard: the largest sieved prime must fit within the circular bucket
    // scheduler's capacity. If this fires, increase LP_SIZE to the next
    // power of two.
    assert(mSqrtPrimeStopIdx <= mM1PrimeStopIdx ||
           (UInt64)P[mSqrtPrimeStopIdx - 1] <= (LargePrimeHitScheduler::LP_SIZE - 1) * M2);

    UInt32 idxLargeBegin = mM1PrimeStopIdx;
    if constexpr (UseBucketSieve) {
        // The tiled path benefits from keeping its sparse upper prime band on
        // the direct four-stream path. The optional rolling block walk retains
        // its independently tunable lower cutoff.
        constexpr UInt64 directSieveCutoff = Finalize && UseFinalizeBlockWalk
            ? M3
            : TILED_DIRECT_SIEVE_CUTOFF;
        while (idxLargeBegin < mSqrtPrimeStopIdx
               && static_cast<UInt64>(P[idxLargeBegin]) <= directSieveCutoff)
            ++idxLargeBegin;
    } else {
        idxLargeBegin = mSqrtPrimeStopIdx;  // treat all primes as medium
    }

    const UInt64 numSeg = (len + M2 - 1) / M2;
    if (!Finalize || !UseFinalizeBlockWalk || numSeg < BLOCK_WALK_MIN_SEGMENTS) {
        // MertensHurst finalizes during its prefix scan, and separately
        // finalized callers now use this same tiled-medium geometry by
        // default. When the optional rolling block walk is enabled, short
        // standalone ranges still stay here because reseeding many small
        // bucket blocks costs more than rolling offsets save.
        const UInt64 mediumTile = hi >= MEDIUM_TILE_SWITCH
            ? MEDIUM_TILE_LARGE
            : M2;
        #pragma omp parallel for schedule(dynamic, 1)
        for (UInt64 tile = 0; tile < len; tile += mediumTile) {
            const UInt64 tileEnd = std::min(tile + mediumTile, len);
            for (UInt64 l = tile; l < tileEnd; l += M1) {
                const UInt64 L = lo + l;
                const UInt64 H = std::min({L + M1 - 1, lo + tileEnd - 1, hi});
                const UInt64 n = H - L + 1;
                std::memcpy(MuP + l, mPreMu.data() + stencilOff,
                            sizeof(Int8) * static_cast<size_t>(n));
                sieveM1Primes(MuP + l, P.data(), L, H);
            }

            if (mM1PrimeStopIdx < idxLargeBegin) {
                const UInt64 L = lo + tile;
                const UInt64 H = lo + tileEnd - 1;
                sieveMediumSubSegment(
                    MuP + tile, P.data(), L, H,
                    mM1PrimeStopIdx, idxLargeBegin, &mSieveQCache
                );
            }
        }
        sieveSquaresPass(MuP, P.data(), lo, hi, 71, mSqrtPrimeStopIdx, &mSieveQCache);
        if (idxLargeBegin < mSqrtPrimeStopIdx) {
            const UInt64 numSeg = (len + M2 - 1) / M2;
            const UInt32 numLP = mSqrtPrimeStopIdx - idxLargeBegin;
            const bool useSerialRouting = numSeg * LP_ROUTE_THRESHOLD >= numLP;

            if (useSerialRouting) {
                const int nt = omp_get_max_threads();
                std::vector<UInt64> threadStart(nt + 1);
                for (int t = 0; t <= nt; ++t) {
                    threadStart[t] = (numSeg * static_cast<UInt64>(t))
                                   / static_cast<UInt64>(nt);
                }

                for (int t = 0; t < nt; ++t) {
                    auto& buckets = mBuckets[t];
                    if (buckets.size() < LargePrimeHitScheduler::LP_NBUCKETS)
                        buckets.resize(LargePrimeHitScheduler::LP_NBUCKETS);
                    for (auto& bucket : buckets)
                        bucket.clear();
                }

                for (UInt32 i = idxLargeBegin; i < mSqrtPrimeStopIdx; ++i) {
                    const UInt64 p = P[i];
                    if (p > hi)
                        break;

                    for (int t = 0; t < nt; ++t) {
                        const UInt64 threadLo = lo + threadStart[t] * M2;
                        const UInt64 threadHi = (t + 1 < nt)
                            ? lo + threadStart[t + 1] * M2 - 1
                            : hi;

                        UInt64 m;
                        if constexpr (UseDivisionFree) {
                            m = p * mSieveQCache.ceilDiv(threadLo, i, p);
                        } else {
                            m = p * (((threadLo - 1) / p) + 1);
                        }
                        m = LargePrimeHitScheduler::skipStencilSquare4(m, p);
                        if (m > threadHi)
                            continue;

                        const UInt64 localSubSeg = (m - threadLo) / M2;
                        using Scheduler = LargePrimeHitScheduler;
                        const Scheduler::EntryT entry = Scheduler::packEntry(
                            static_cast<UInt32>(p), (m - threadLo) - localSubSeg * M2
                        );
                        mBuckets[t][Scheduler::ringIndex(localSubSeg, entry)].push_back(entry);
                    }
                }

                #pragma omp parallel num_threads(nt)
                {
                    const int tid = omp_get_thread_num();
                    const UInt64 s0 = threadStart[tid];
                    const UInt64 s1 = threadStart[tid + 1];

                    if (s0 < s1) {
                        LargePrimeHitScheduler scheduler(
                            LargePrimeHitScheduler::PrePopulated{},
                            lo, lo + s0 * M2, std::min(lo + s1 * M2 - 1, hi),
                            M2, P, idxLargeBegin, mSqrtPrimeStopIdx - 1,
                            mBuckets[tid], &mSieveQCache
                        );
                        for (UInt64 s = s0; s < s1; ++s) {
                            scheduler.sieveSubSegment(MuP);
                            if constexpr (Finalize) {
                                const UInt64 L = lo + s * M2;
                                finalizeMu(MuP + s * M2, L, std::min(L + M2 - 1, hi));
                            }
                        }
                    }
                }
            } else {
                #pragma omp parallel
                {
                    const int tid = omp_get_thread_num();
                    const int nt = omp_get_num_threads();
                    const UInt64 s0 = (numSeg * static_cast<UInt64>(tid))
                                          / static_cast<UInt64>(nt);
                    const UInt64 s1 = (numSeg * static_cast<UInt64>(tid + 1))
                                          / static_cast<UInt64>(nt);

                    if (s0 < s1) {
                        LargePrimeHitScheduler scheduler(
                            lo, lo + s0 * M2, std::min(lo + s1 * M2 - 1, hi),
                            M2, P, idxLargeBegin, mSqrtPrimeStopIdx - 1,
                            mBuckets[tid], &mSieveQCache
                        );
                        for (UInt64 s = s0; s < s1; ++s) {
                            scheduler.sieveSubSegment(MuP);
                            if constexpr (Finalize) {
                                const UInt64 L = lo + s * M2;
                                finalizeMu(MuP + s * M2, L, std::min(L + M2 - 1, hi));
                            }
                        }
                    }
                }
            }
        } else if constexpr (Finalize) {
            #pragma omp parallel for schedule(dynamic, 1)
            for (UInt64 l = 0; l < len; l += M2)
                finalizeMu(MuP + l, lo + l, std::min(lo + l + M2 - 1, hi));
        }
        return;
    }

    // M1 stage: copy the stencil, then apply small and M1 medium primes.
    #pragma omp parallel for schedule(dynamic, 1)
    for (UInt64 l = 0; l < len; l += M1) {
        const UInt64 L = lo + l;
        const UInt64 H = std::min(L + M1 - 1, hi);
        const UInt64 n = H - L + 1;
        std::memcpy(MuP + l, mPreMu.data() + stencilOff,
                    sizeof(Int8) * static_cast<size_t>(n));
        sieveM1Primes(MuP + l, P.data(), L, H);
    }

    // Zero squareful entries before the contiguous medium/bucket walk. Later
    // log additions leave them nonnegative, so finalization still maps them
    // to zero.
    sieveSquaresPass(MuP, P.data(), lo, hi, 71, mSqrtPrimeStopIdx, &mSieveQCache);

    if (idxLargeBegin >= mSqrtPrimeStopIdx) {
        if (mM1PrimeStopIdx < idxLargeBegin) {
            #pragma omp parallel for schedule(dynamic, 1)
            for (UInt64 l = 0; l < len; l += M2) {
                const UInt64 L = lo + l;
                const UInt64 H = std::min(L + M2 - 1, hi);
                sieveMediumSubSegment(MuP + l, P.data(), L, H,
                                      mM1PrimeStopIdx, idxLargeBegin, &mSieveQCache);
                if constexpr (Finalize)
                    finalizeMu(MuP + l, L, H);
            }
        } else if constexpr (Finalize) {
            #pragma omp parallel for schedule(dynamic, 1)
            for (UInt64 l = 0; l < len; l += M2)
                finalizeMu(MuP + l, lo + l, std::min(lo + l + M2 - 1, hi));
        }

    } else {
        // Dynamic contiguous blocks keep medium-prime next-hit state hot and
        // carry each large-prime scheduler only across the range it owns.
        const UInt64 targetBlocks = 2 * static_cast<UInt64>(omp_get_max_threads());
        const UInt64 balancedBlock = (numSeg + targetBlocks - 1) / targetBlocks;
        const UInt64 blockSegments = std::max<UInt64>(
            1, std::min(BLOCK_SEGMENTS, balancedBlock)
        );
        const UInt64 numBlocks = (numSeg + blockSegments - 1) / blockSegments;

        #pragma omp parallel
        {
            const int tid = omp_get_thread_num();
            std::vector<UInt32> nextOff;

            #pragma omp for schedule(dynamic, 1)
            for (UInt64 block = 0; block < numBlocks; ++block) {
                const UInt64 s0 = block * blockSegments;
                const UInt64 s1 = std::min(s0 + blockSegments, numSeg);
                const UInt64 blockLo = lo + s0 * M2;
                const UInt64 blockHi = std::min(lo + s1 * M2 - 1, hi);

                LargePrimeHitScheduler sched(
                    lo, blockLo, blockHi, M2, P,
                    idxLargeBegin, mSqrtPrimeStopIdx - 1,
                    mBuckets[tid], &mSieveQCache
                );

                const UInt64 mediumCount = idxLargeBegin - mM1PrimeStopIdx;
                nextOff.resize(static_cast<size_t>(mediumCount));
                for (UInt64 i = mM1PrimeStopIdx; i < idxLargeBegin; ++i) {
                    const UInt64 p = P[i];
                    UInt64 first;
                    if constexpr (UseDivisionFree) {
                        first = p * mSieveQCache.ceilDiv(blockLo, i, p);
                    } else {
                        first = p * (((blockLo - 1) / p) + 1);
                    }
                    nextOff[i - mM1PrimeStopIdx] = static_cast<UInt32>(first - blockLo);
                }

                for (UInt64 s = s0; s < s1; ++s) {
                    const UInt64 L = lo + s * M2;
                    const UInt64 H = std::min(L + M2 - 1, hi);
                    sieveMediumSubSegmentRolling(
                        MuP + s * M2, P.data(), H - L + 1,
                        mM1PrimeStopIdx, idxLargeBegin, nextOff
                    );
                    sched.sieveSubSegment(MuP);
                    if constexpr (Finalize)
                        finalizeMu(MuP + s * M2, L, H);
                }
            }
        }
    }
}

// Explicit instantiations: <true> is the normal mu-finalizing path used by all
// existing callers; <false> leaves the raw packed bytes for the fused
// finalize+prefix scan (SegmentedMertensSieve.h).
template void SegmentedMobiusSieveCore::sieve<true>(UInt64, UInt64, const std::vector<UInt32>&);
template void SegmentedMobiusSieveCore::sieve<false>(UInt64, UInt64, const std::vector<UInt32>&);

// ============================================================================
// M1 stage: hardcoded small primes, then M1 medium primes
// ============================================================================

void SegmentedMobiusSieveCore::sieveM1Primes(Int8* mu, const UInt32* primes,
                                             UInt64 lo, UInt64 hi) {
    sieveM1PrimeRange(mu, primes, lo, hi, mM1PrimeStopIdx, &mSieveQCache);
}

void SegmentedMobiusSieveCore::sieveM1PrimeRange(
    Int8* __restrict Mu, const UInt32* __restrict primes,
    UInt64 lo, UInt64 hi, UInt32 stoppos,
    const SieveQuotientCache* cache) {
    const UInt64 len = hi - lo + 1;

    // Log-space sieve: each entry gets (ceil(log2(p)) | 1) added per prime
    // factor p. For an odd prime ceil(log2 p) == numbits(p), so each group
    // below shares one constant (the bit width, made odd):
    //   add5: primes 13..31   -> 5
    //   add7: primes 37..127  -> 7
    //   add9: primes 131..353 -> 9
    // OR with 1 keeps the value odd so finalizeMu can read the factor count
    // parity from bit 0 (that's how it figures out the sign of mu). The ceil
    // weighting is what lets finalizeMu compare against floor(log2 N) exactly,
    // with no slack margin. The stencil (primes 2,3,5,7,11) uses the same
    // ceil(log2 p)|1 weights so the encoding is uniform across all primes.
    auto add5Stride = [&](UInt64 st, UInt64 step) {
        UInt64 i = st;
        for (; i + 4*step < len; i += 4*step) {
            Mu[i] += 5;
            Mu[i + step] += 5;
            Mu[i + 2*step] += 5;
            Mu[i + 3*step] += 5;
        }
        for (; i < len; i += step) Mu[i] += 5;
    };

    auto add7Stride = [&](UInt64 st, UInt64 step) {
        UInt64 i = st;
        for (; i + 4*step < len; i += 4*step) {
            Mu[i] += 7;
            Mu[i + step] += 7;
            Mu[i + 2*step] += 7;
            Mu[i + 3*step] += 7;
        }
        for (; i < len; i += step) Mu[i] += 7;
    };

    auto add9Stride = [&](UInt64 st, UInt64 step) {
        UInt64 i = st;
        for (; i + 4*step < len; i += 4*step) {
            Mu[i] += 9;
            Mu[i + step] += 9;
            Mu[i + 2*step] += 9;
            Mu[i + 3*step] += 9;
        }
        for (; i < len; i += step) Mu[i] += 9;
    };

    auto add11Stride = [&](UInt64 st, UInt64 step) {
        UInt64 i = st;
        for (; i + 4*step < len; i += 4*step) {
            Mu[i] += 11;
            Mu[i + step] += 11;
            Mu[i + 2*step] += 11;
            Mu[i + 3*step] += 11;
        }
        for (; i < len; i += step) Mu[i] += 11;
    };

    auto zerooutStride = [&](UInt64 st, UInt64 step) {
        UInt64 i = st;
        for (; i + 4*step < len; i += 4*step) {
            Mu[i] = 0;
            Mu[i + step] = 0;
            Mu[i + 2*step] = 0;
            Mu[i + 3*step] = 0;
        }
        for (; i < len; i += step) Mu[i] = 0;
    };

    // ----------- Sieve multiples of p & p^2 < 350 -----------
    // Primes 13..353 are fully unrolled to avoid loop/branch overhead.
    // These dominate the inner loop since small prime multiples are dense.
    // Primes 2,3,5,7,11 are handled by the pre-computed stencil (period 13860).
    add5Stride(13*((lo + 12)/13) - lo, 13);      add5Stride(17*((lo + 16)/17) - lo, 17);
    add5Stride(19*((lo + 18)/19) - lo, 19);      add5Stride(23*((lo + 22)/23) - lo, 23);
    add5Stride(29*((lo + 28)/29) - lo, 29);      add5Stride(31*((lo + 30)/31) - lo, 31);
    add7Stride(37*((lo + 36)/37) - lo, 37);      add7Stride(41*((lo + 40)/41) - lo, 41);
    add7Stride(43*((lo + 42)/43) - lo, 43);      add7Stride(47*((lo + 46)/47) - lo, 47);
    add7Stride(53*((lo + 52)/53) - lo, 53);      add7Stride(59*((lo + 58)/59) - lo, 59);
    add7Stride(61*((lo + 60)/61) - lo, 61);      add7Stride(67*((lo + 66)/67) - lo, 67);
    add7Stride(71*((lo + 70)/71) - lo, 71);      add7Stride(73*((lo + 72)/73) - lo, 73);
    add7Stride(79*((lo + 78)/79) - lo, 79);      add7Stride(83*((lo + 82)/83) - lo, 83);
    add7Stride(89*((lo + 88)/89) - lo, 89);      add7Stride(97*((lo + 96)/97) - lo, 97);
    add7Stride(101*((lo + 100)/101) - lo, 101);  add7Stride(103*((lo + 102)/103) - lo, 103);
    add7Stride(107*((lo + 106)/107) - lo, 107);  add7Stride(109*((lo + 108)/109) - lo, 109);
    add7Stride(113*((lo + 112)/113) - lo, 113);  add7Stride(127*((lo + 126)/127) - lo, 127);
    add9Stride(131*((lo + 130)/131) - lo, 131);  add9Stride(137*((lo + 136)/137) - lo, 137);
    add9Stride(139*((lo + 138)/139) - lo, 139);  add9Stride(149*((lo + 148)/149) - lo, 149);
    add9Stride(151*((lo + 150)/151) - lo, 151);  add9Stride(157*((lo + 156)/157) - lo, 157);
    add9Stride(163*((lo + 162)/163) - lo, 163);  add9Stride(167*((lo + 166)/167) - lo, 167);
    add9Stride(173*((lo + 172)/173) - lo, 173);  add9Stride(179*((lo + 178)/179) - lo, 179);
    add9Stride(181*((lo + 180)/181) - lo, 181);  add9Stride(191*((lo + 190)/191) - lo, 191);
    add9Stride(193*((lo + 192)/193) - lo, 193);  add9Stride(197*((lo + 196)/197) - lo, 197);
    add9Stride(199*((lo + 198)/199) - lo, 199);  add9Stride(211*((lo + 210)/211) - lo, 211);
    add9Stride(223*((lo + 222)/223) - lo, 223);  add9Stride(227*((lo + 226)/227) - lo, 227);
    add9Stride(229*((lo + 228)/229) - lo, 229);  add9Stride(233*((lo + 232)/233) - lo, 233);
    add9Stride(239*((lo + 238)/239) - lo, 239);  add9Stride(241*((lo + 240)/241) - lo, 241);
    add9Stride(251*((lo + 250)/251) - lo, 251);  add9Stride(257*((lo + 256)/257) - lo, 257);
    add9Stride(263*((lo + 262)/263) - lo, 263);  add9Stride(269*((lo + 268)/269) - lo, 269);
    add9Stride(271*((lo + 270)/271) - lo, 271);  add9Stride(277*((lo + 276)/277) - lo, 277);
    add9Stride(281*((lo + 280)/281) - lo, 281);  add9Stride(283*((lo + 282)/283) - lo, 283);
    add9Stride(293*((lo + 292)/293) - lo, 293);  add9Stride(307*((lo + 306)/307) - lo, 307);
    add9Stride(311*((lo + 310)/311) - lo, 311);  add9Stride(313*((lo + 312)/313) - lo, 313);
    add9Stride(317*((lo + 316)/317) - lo, 317);  add9Stride(331*((lo + 330)/331) - lo, 331);
    add9Stride(337*((lo + 336)/337) - lo, 337);  add9Stride(347*((lo + 346)/347) - lo, 347);
    add9Stride(349*((lo + 348)/349) - lo, 349);  add9Stride(353*((lo + 352)/353) - lo, 353);

    // Constant-stride M1 medium primes. Fully unrolling these compact tables
    // lets the compiler strength-reduce every quotient without maintaining a
    // separate source-level call for each prime. The compile-time counts also
    // make M1_CONSTANT_PRIME_CAP independently retunable.
    static constexpr UInt16 add9Primes[] = {
        359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431,
        433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499,
        503, 509,
    };
    static constexpr UInt16 add11Primes[] = {
        521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599,
        601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661,
        673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751,
        757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829,
        839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919,
        929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009,
        1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063,
        1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129,
        1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217,
        1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289,
        1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367,
        1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447,
        1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499,
        1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579,
        1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637,
        1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723,
        1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801,
        1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879,
        1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979,
        1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039,
    };
    static constexpr UInt64 add9PrimeCount = []() constexpr {
        UInt64 count = 0;
        while (count < sizeof(add9Primes) / sizeof(add9Primes[0])
               && add9Primes[count] <= M1_CONSTANT_PRIME_CAP)
            ++count;
        return count;
    }();
    static constexpr UInt64 add11PrimeCount = []() constexpr {
        UInt64 count = 0;
        while (count < sizeof(add11Primes) / sizeof(add11Primes[0])
               && add11Primes[count] <= M1_CONSTANT_PRIME_CAP)
            ++count;
        return count;
    }();
    static constexpr UInt64 firstM1FourStreamIdx =
        71 + add9PrimeCount + add11PrimeCount;

#if defined(__clang__)
    #pragma clang loop unroll(full)
#elif defined(__GNUC__)
    #pragma GCC unroll 256
#endif
    for (UInt64 i = 0; i < add9PrimeCount; ++i) {
        const UInt64 p = add9Primes[i];
        add9Stride(p * ((lo + p - 1) / p) - lo, p);
    }

#if defined(__clang__)
    #pragma clang loop unroll(full)
#elif defined(__GNUC__)
    #pragma GCC unroll 256
#endif
    for (UInt64 i = 0; i < add11PrimeCount; ++i) {
        const UInt64 p = add11Primes[i];
        add11Stride(p * ((lo + p - 1) / p) - lo, p);
    }

    // Zero out multiples of p^2 for p=5,7,11,13,17,19 (the squares < 361).
    // mu(n) = 0 whenever n has a squared prime factor.
    zerooutStride(25*((lo  + 24 )/25 ) - lo,  25);
    zerooutStride(49*((lo  + 48 )/49 ) - lo,  49);
    zerooutStride(121*((lo + 120)/121) - lo, 121);
    zerooutStride(169*((lo + 168)/169) - lo, 169);
    zerooutStride(289*((lo + 288)/289) - lo, 289);
    zerooutStride(361*((lo + 360)/361) - lo, 361);

    // ----------- Sieve the above's prime squares -----------

    for (UInt64 i = 8; i < std::min((UInt32)71, stoppos); ++i) {
        const UInt64 p = primes[i];
        const UInt64 p2 = p * p;

        UInt64 st2;
        if constexpr (UseDivisionFree) {
            // ceil(lo / p^2) = ceil(ceil(lo / p) / p)
            const UInt64 q1 = cache->ceilDiv(lo, i, p);
            const UInt64 q2 = cache->ceilDiv(q1, i, p);
            st2 = p2 * q2 - lo;
        } else {
            st2 = p2 * (((lo - 1) / p2) + 1) - lo;
        }

        for (UInt64 pos2 = st2; pos2 < len; pos2 += p2)
            Mu[pos2] = 0;
    }

    // ----------- Sieve remaining M1 medium primes -----------

    auto firstOffset = [&](UInt64 index, UInt64 p) {
        if constexpr (UseDivisionFree)
            return p * cache->ceilDiv(lo, index, p) - lo;
        else
            return p * (((lo - 1) / p) + 1) - lo;
    };

    auto finishStream = [&](UInt64 pos, UInt64 p, Int8 logp) {
        for (; pos + 3 * p < len; pos += 4 * p) {
            Mu[pos] += logp;
            Mu[pos + p] += logp;
            Mu[pos + 2 * p] += logp;
            Mu[pos + 3 * p] += logp;
        }
        for (; pos < len; pos += p)
            Mu[pos] += logp;
    };

    UInt64 i = firstM1FourStreamIdx;
    for (; i + 3 < stoppos; i += 4) {
        const UInt64 p0 = primes[i];
        const UInt64 p1 = primes[i + 1];
        const UInt64 p2 = primes[i + 2];
        const UInt64 p3 = primes[i + 3];
        UInt64 pos0 = firstOffset(i, p0);
        UInt64 pos1 = firstOffset(i + 1, p1);
        UInt64 pos2 = firstOffset(i + 2, p2);
        UInt64 pos3 = firstOffset(i + 3, p3);
        const Int8 logp0 = primeLogWeight(static_cast<UInt32>(p0));
        const Int8 logp1 = primeLogWeight(static_cast<UInt32>(p1));
        const Int8 logp2 = primeLogWeight(static_cast<UInt32>(p2));
        const Int8 logp3 = primeLogWeight(static_cast<UInt32>(p3));

        while (pos0 < len && pos1 < len && pos2 < len && pos3 < len) {
            Mu[pos0] += logp0;
            Mu[pos1] += logp1;
            Mu[pos2] += logp2;
            Mu[pos3] += logp3;
            pos0 += p0;
            pos1 += p1;
            pos2 += p2;
            pos3 += p3;
        }

        finishStream(pos0, p0, logp0);
        finishStream(pos1, p1, logp1);
        finishStream(pos2, p2, logp2);
        finishStream(pos3, p3, logp3);
    }

    for (; i < stoppos; ++i) {
        const UInt64 p = primes[i];
        const Int8 logp = primeLogWeight(static_cast<UInt32>(p));
        finishStream(firstOffset(i, p), p, logp);
    }

    // p^2 multiples for these primes are handled once per full segment by
    // sieveSquaresPass, not once per M1 sub-segment.
}

// ============================================================================
// Squares pass: zero p^2 multiples for primes >= 359, once per segment
// ============================================================================

// For p >= 359, p^2 > M1, so per-sub-segment square handling pays a quotient per
// prime per sub-segment for almost no hits; one pass over the whole segment pays
// one quotient per prime total. Zeroing commutes with the log-prime adds of
// other primes: a zeroed byte plus small positive adds stays non-negative,
// which finalizeMu decodes as mu = 0. (The per-sub-segment code already relied on
// this ordering tolerance — primes later in the loop add onto positions
// zeroed by earlier primes.)
void SegmentedMobiusSieveCore::sieveSquaresPass(Int8* __restrict Mu,
                                                const UInt32* __restrict primes,
                                                UInt64 lo, UInt64 hi,
                                                UInt32 fromIdx, UInt32 toIdx,
                                                const SieveQuotientCache* cache) {
    const UInt64 len = hi - lo + 1;

    // Work per prime is ~len/p^2, so a flat parallel-for over primes leaves
    // one thread with nearly all the hits while the rest idle (~30% of sieve
    // time at large segments). Split instead:
    //   dense primes  (p <= P_SPLIT): parallelize over range chunks;
    //   sparse primes (p >  P_SPLIT): parallelize over primes.
    static constexpr UInt32 P_SPLIT  = 1u << 16;
    static constexpr UInt64 SQ_CHUNK = UInt64(1) << 26;   // 64 MB

    UInt32 splitIdx = fromIdx;
    while (splitIdx < toIdx && primes[splitIdx] <= P_SPLIT)
        ++splitIdx;

    // Dense group: range-chunked. Costs one extra quotient per (prime, chunk),
    // negligible next to the removed serialization.
    const UInt64 nChunks = (len + SQ_CHUNK - 1) / SQ_CHUNK;
    #pragma omp parallel for schedule(dynamic, 1)
    for (UInt64 c = 0; c < nChunks; ++c) {
        const UInt64 cLo   = lo + c * SQ_CHUNK;                       // absolute
        const UInt64 cEndR = std::min(c * SQ_CHUNK + SQ_CHUNK, len);  // relative, exclusive

        for (UInt32 i = fromIdx; i < splitIdx; ++i) {
            const UInt64 p = primes[i];
            const UInt64 p2 = p * p;

            UInt64 st2;
            if constexpr (UseDivisionFree) {
                // ceil(cLo / p^2) = ceil(ceil(cLo / p) / p)
                const UInt64 q1 = cache->ceilDiv(cLo, i, p);
                const UInt64 q2 = cache->ceilDiv(q1, i, p);
                st2 = p2 * q2 - lo;
            } else {
                st2 = p2 * (((cLo - 1) / p2) + 1) - lo;
            }

            for (UInt64 pos2 = st2; pos2 < cEndR; pos2 += p2)
                Mu[pos2] = 0;
        }
    }

    // Sparse group: per-prime over the whole segment.
    #pragma omp parallel for schedule(dynamic, 256)
    for (UInt32 i = splitIdx; i < toIdx; ++i) {
        const UInt64 p = primes[i];
        const UInt64 p2 = p * p;

        UInt64 st2;
        if constexpr (UseDivisionFree) {
            const UInt64 q1 = cache->ceilDiv(lo, i, p);
            const UInt64 q2 = cache->ceilDiv(q1, i, p);
            st2 = p2 * q2 - lo;
        } else {
            st2 = p2 * (((lo - 1) / p2) + 1) - lo;
        }

        for (UInt64 pos2 = st2; pos2 < len; pos2 += p2)
            Mu[pos2] = 0;
    }
}

// ============================================================================
// Phase 2: Medium primes
// ============================================================================

void SegmentedMobiusSieveCore::sieveMediumSubSegment(Int8* __restrict Mu, const UInt32* __restrict primes,
                                                     UInt64 lo, UInt64 hi,
                                                     UInt64 fromIdx, UInt64 toIdx,
                                                     const SieveQuotientCache* cache) {
    const UInt64 len = hi - lo + 1;

    auto firstOffset = [&](UInt64 i, UInt64 p) {
        if constexpr (UseDivisionFree) {
            return p * cache->ceilDiv(lo, i, p) - lo;
        } else {
            return p * (((lo - 1) / p) + 1) - lo;
        }
    };

    auto finishStream = [&](UInt64 pos, UInt64 p, Int8 logp) {
        for (; pos + 3 * p < len; pos += 4 * p) {
            Mu[pos] += logp;
            Mu[pos + p] += logp;
            Mu[pos + 2 * p] += logp;
            Mu[pos + 3 * p] += logp;
        }
        for (; pos < len; pos += p)
            Mu[pos] += logp;
    };

    UInt64 i = fromIdx;
    for (; i + 3 < toIdx; i += 4) {
        const UInt64 p0 = primes[i];
        const UInt64 p1 = primes[i + 1];
        const UInt64 p2 = primes[i + 2];
        const UInt64 p3 = primes[i + 3];
        UInt64 pos0 = firstOffset(i, p0);
        UInt64 pos1 = firstOffset(i + 1, p1);
        UInt64 pos2 = firstOffset(i + 2, p2);
        UInt64 pos3 = firstOffset(i + 3, p3);
        const Int8 l0 = primeLogWeight(static_cast<UInt32>(p0));
        const Int8 l1 = primeLogWeight(static_cast<UInt32>(p1));
        const Int8 l2 = primeLogWeight(static_cast<UInt32>(p2));
        const Int8 l3 = primeLogWeight(static_cast<UInt32>(p3));

        while (pos0 < len && pos1 < len && pos2 < len && pos3 < len) {
            Mu[pos0] += l0;
            Mu[pos1] += l1;
            Mu[pos2] += l2;
            Mu[pos3] += l3;
            pos0 += p0;
            pos1 += p1;
            pos2 += p2;
            pos3 += p3;
        }
        finishStream(pos0, p0, l0);
        finishStream(pos1, p1, l1);
        finishStream(pos2, p2, l2);
        finishStream(pos3, p3, l3);
    }
    for (; i < toIdx; ++i) {
        const UInt64 p = primes[i];
        const UInt64 pos = firstOffset(i, p);
        const Int8 logp = primeLogWeight(static_cast<UInt32>(p));
        finishStream(pos, p, logp);
    }
}

void SegmentedMobiusSieveCore::sieveMediumSubSegmentRolling(
    Int8* __restrict Mu, const UInt32* __restrict primes, UInt64 len,
    UInt64 fromIdx, UInt64 toIdx, std::vector<UInt32>& nextOff) {
    auto finishStream = [&](UInt64 pos, UInt64 p, Int8 logp) {
        for (; pos + 3 * p < len; pos += 4 * p) {
            Mu[pos] += logp;
            Mu[pos + p] += logp;
            Mu[pos + 2 * p] += logp;
            Mu[pos + 3 * p] += logp;
        }
        for (; pos < len; pos += p)
            Mu[pos] += logp;
        return pos;
    };

    UInt64 i = fromIdx;
    for (; i + 3 < toIdx; i += 4) {
        const UInt64 p0 = primes[i];
        const UInt64 p1 = primes[i + 1];
        const UInt64 p2 = primes[i + 2];
        const UInt64 p3 = primes[i + 3];
        UInt64 pos0 = nextOff[i - fromIdx];
        UInt64 pos1 = nextOff[i + 1 - fromIdx];
        UInt64 pos2 = nextOff[i + 2 - fromIdx];
        UInt64 pos3 = nextOff[i + 3 - fromIdx];
        const Int8 l0 = primeLogWeight(static_cast<UInt32>(p0));
        const Int8 l1 = primeLogWeight(static_cast<UInt32>(p1));
        const Int8 l2 = primeLogWeight(static_cast<UInt32>(p2));
        const Int8 l3 = primeLogWeight(static_cast<UInt32>(p3));

        while (pos0 < len && pos1 < len && pos2 < len && pos3 < len) {
            Mu[pos0] += l0;
            Mu[pos1] += l1;
            Mu[pos2] += l2;
            Mu[pos3] += l3;
            pos0 += p0;
            pos1 += p1;
            pos2 += p2;
            pos3 += p3;
        }
        pos0 = finishStream(pos0, p0, l0);
        pos1 = finishStream(pos1, p1, l1);
        pos2 = finishStream(pos2, p2, l2);
        pos3 = finishStream(pos3, p3, l3);
        nextOff[i - fromIdx] = static_cast<UInt32>(pos0 - len);
        nextOff[i + 1 - fromIdx] = static_cast<UInt32>(pos1 - len);
        nextOff[i + 2 - fromIdx] = static_cast<UInt32>(pos2 - len);
        nextOff[i + 3 - fromIdx] = static_cast<UInt32>(pos3 - len);
    }
    for (; i < toIdx; ++i) {
        const UInt64 p = primes[i];
        const Int8 logp = primeLogWeight(static_cast<UInt32>(p));
        const UInt64 pos = finishStream(nextOff[i - fromIdx], p, logp);
        nextOff[i - fromIdx] = static_cast<UInt32>(pos - len);
    }
}

// ============================================================================
// Finalization: packed sieve values -> mu ∈ {-1, 0, +1}
// ============================================================================

#if SIEVE_SIMD_NEON || SIEVE_SIMD_SSE
// Constant-threshold finalize kernel (ceil-log2 scheme).
//
// For each byte v: squarefree iff v < 0 (bit 7 set). Then S = v & 0x7F is the
// summed (ceil(log2 p) | 1) weights and par = v & 1 the factor-count parity.
// fl = floor(log2 N) is constant across [Mu, Mu+n) — the caller splits the
// segment at powers of two so a single broadcast threshold is exact here.
//
//   mu = squarefree ? ( (S > fl) ? 1 - 2*par : 2*par - 1 ) : 0
//
// Both S (0..127) and fl (0..63) are non-negative, so the S > fl test is a
// plain signed-byte compare — no unsigned bias trick needed. The caller
// guarantees N >= 3 for every lane (N <= 2 is handled separately).
void SegmentedMobiusSieveCore::finalizeMuVec(
    Int8* __restrict Mu, int fl, size_t n) {
    size_t i = 0;
    const Int8 flb = static_cast<Int8>(fl);

#if SIEVE_SIMD_SVE2
    const svint8_t svZero  = svdup_n_s8(0);
    const svint8_t svOne   = svdup_n_s8(1);
    const svint8_t svMask7 = svdup_n_s8(0x7F);
    const svint8_t svFl    = svdup_n_s8(flb);

    for (; i < n; i += svcntb()) {
        svbool_t pg = svwhilelt_b8((uint64_t)i, (uint64_t)n);

        svint8_t v = svld1_s8(pg, Mu + i);

        // sf = (v < 0) — squarefree
        svbool_t sf = svcmplt_s8(pg, v, svZero);

        // S = v & 0x7F
        svint8_t S = svand_s8_x(pg, v, svMask7);

        // base = 2*(v & 1) - 1
        svint8_t lsb  = svand_s8_x(pg, v, svOne);
        svint8_t base = svsub_s8_x(pg, svadd_s8_x(pg, lsb, lsb), svOne);
        svint8_t negBase = svneg_s8_x(pg, base);

        // ff = (S > fl) — fully factored; r = ff ? -base : base
        svbool_t ff = svcmpgt_s8(pg, S, svFl);
        svint8_t r  = svsel_s8(ff, negBase, base);

        svint8_t out = svsel_s8(sf, r, svZero);
        svst1_s8(pg, Mu + i, out);
    }

#elif SIEVE_SIMD_NEON
    const int8x16_t vZero  = vdupq_n_s8(0);
    const int8x16_t vOne   = vdupq_n_s8(1);
    const int8x16_t vMask7 = vdupq_n_s8(0x7F);
    const int8x16_t vFl    = vdupq_n_s8(flb);

    for (; i + 16 <= n; i += 16) {
        int8x16_t v = vld1q_s8(Mu + i);

        uint8x16_t sf = vcltq_s8(v, vZero);          // v < 0
        int8x16_t  S  = vandq_s8(v, vMask7);

        int8x16_t lsb  = vandq_s8(v, vOne);
        int8x16_t base = vsubq_s8(vshlq_n_s8(lsb, 1), vOne);
        int8x16_t negBase = vnegq_s8(base);

        uint8x16_t ff = vcgtq_s8(S, vFl);            // S > fl (signed)
        int8x16_t  r  = vbslq_s8(ff, negBase, base);

        int8x16_t out = vbslq_s8(sf, r, vZero);
        vst1q_s8(Mu + i, out);
    }

#elif SIEVE_SIMD_AVX512
    const __m512i vZero  = _mm512_setzero_si512();
    const __m512i vOne   = _mm512_set1_epi8(1);
    const __m512i vMask7 = _mm512_set1_epi8(0x7F);
    const __m512i vFl    = _mm512_set1_epi8(flb);

    for (; i + 64 <= n; i += 64) {
        __m512i v = _mm512_loadu_si512((const __m512i*)(Mu + i));

        __mmask64 sf = _mm512_cmplt_epi8_mask(v, vZero);   // v < 0
        __m512i   S  = _mm512_and_si512(v, vMask7);

        __m512i lsb  = _mm512_and_si512(v, vOne);
        __m512i base = _mm512_sub_epi8(_mm512_add_epi8(lsb, lsb), vOne);
        __m512i negBase = _mm512_sub_epi8(vZero, base);

        __mmask64 ff = _mm512_cmpgt_epi8_mask(S, vFl);     // S > fl
        // r = ff ? negBase : base
        __m512i r = _mm512_mask_blend_epi8(ff, base, negBase);

        // out = sf ? r : 0
        __m512i out = _mm512_maskz_mov_epi8(sf, r);
        _mm512_storeu_si512((__m512i*)(Mu + i), out);
    }

#elif SIEVE_SIMD_AVX2
    const __m256i vZero  = _mm256_setzero_si256();
    const __m256i vOne   = _mm256_set1_epi8(1);
    const __m256i vMask7 = _mm256_set1_epi8(0x7F);
    const __m256i vFl    = _mm256_set1_epi8(flb);

    for (; i + 32 <= n; i += 32) {
        __m256i v = _mm256_loadu_si256((const __m256i*)(Mu + i));

        __m256i sf = _mm256_cmpgt_epi8(vZero, v);          // v < 0
        __m256i S  = _mm256_and_si256(v, vMask7);

        __m256i lsb  = _mm256_and_si256(v, vOne);
        __m256i base = _mm256_sub_epi8(_mm256_add_epi8(lsb, lsb), vOne);
        __m256i negBase = _mm256_sub_epi8(vZero, base);

        __m256i ff = _mm256_cmpgt_epi8(S, vFl);            // S > fl (signed; both >= 0)
        __m256i r  = _mm256_or_si256(_mm256_and_si256(ff, negBase),
                                     _mm256_andnot_si256(ff, base));

        __m256i out = _mm256_and_si256(sf, r);
        _mm256_storeu_si256((__m256i*)(Mu + i), out);
    }

#elif SIEVE_SIMD_SSE
    const __m128i vZero  = _mm_setzero_si128();
    const __m128i vOne   = _mm_set1_epi8(1);
    const __m128i vMask7 = _mm_set1_epi8(0x7F);
    const __m128i vFl    = _mm_set1_epi8(flb);

    for (; i + 16 <= n; i += 16) {
        __m128i v = _mm_loadu_si128((const __m128i*)(Mu + i));

        __m128i sf = _mm_cmplt_epi8(v, vZero);             // v < 0
        __m128i S  = _mm_and_si128(v, vMask7);

        __m128i lsb  = _mm_and_si128(v, vOne);
        __m128i base = _mm_sub_epi8(_mm_add_epi8(lsb, lsb), vOne);
        __m128i negBase = _mm_sub_epi8(vZero, base);

        __m128i ff = _mm_cmpgt_epi8(S, vFl);               // S > fl (signed; both >= 0)
        __m128i r  = _mm_or_si128(_mm_and_si128(ff, negBase),
                                  _mm_andnot_si128(ff, base));

        __m128i out = _mm_and_si128(sf, r);
        _mm_storeu_si128((__m128i*)(Mu + i), out);
    }
#endif

    // Scalar tail for SIMD remainder (N >= 3 guaranteed by caller).
    for (; i < n; ++i) {
        const Int8 v = Mu[i];
        if (v >= 0) { Mu[i] = 0; continue; }     // square factor -> mu = 0
        const int S    = v & 0x7F;
        const int base = ((v & 1) << 1) - 1;     // 2*par - 1 in {-1,+1}
        Mu[i] = static_cast<Int8>((S > fl) ? -base : base);
    }
}
#endif // SIEVE_SIMD_NEON || SIEVE_SIMD_SSE

// Convert packed log-prime sums to mu in {-1, 0, +1} (ceil-log2 scheme).
//
// Each Mu[i] holds 0x80 | S for squarefree lo+i (bit 7 set, low 7 bits hold
// S = sum of (ceil(log2 p) | 1) over the sieved prime factors), or 0 if a
// square factor was found. With ceil weights, S > floor(log2 N) exactly when
// N is fully factored by the sieved primes; otherwise an unsieved prime
// cofactor (> sqrt N) remains. par = bit 0 carries the factor-count parity.
//
//   mu = !squarefree ? 0
//      : N <= 2       ? (N == 1 ? 1 : -1)            // S-vs-floor misreads these
//      : (S > floor_log2(N)) ? 1 - 2*par : 2*par - 1
//
// floor_log2(N) is constant between consecutive powers of two, so the segment
// is finalized in constant-threshold runs; the SIMD kernel applies one
// broadcast threshold per run. Within a typical large-lo sub-segment the run is the
// whole sub-segment (powers of two are spaced far wider than M2).
void SegmentedMobiusSieveCore::finalizeMu(Int8* __restrict Mu, UInt64 lo, UInt64 hi) {
    const UInt64 len = hi - lo + 1;
    UInt64 pos = 0;

    // Small-N guard: mu(1) = 1, mu(2) = -1 (only ever the very first segment).
    for (; pos < len && lo + pos <= 2; ++pos)
        Mu[pos] = (lo + pos == 1) ? Int8(1) : Int8(-1);

    // Constant-floor(log2 N) runs, split at each power of two.
    while (pos < len) {
        const UInt64 N0 = lo + pos;
        const int fl = 63 - __builtin_clzll(N0);
        const UInt64 runHi = (fl < 63) ? std::min(hi, (UInt64(1) << (fl + 1)) - 1) : hi;
        const size_t runLen = static_cast<size_t>(runHi - N0 + 1);

#if SIEVE_SIMD_NEON || SIEVE_SIMD_SSE
        finalizeMuVec(Mu + pos, fl, runLen);
#else
        for (size_t j = 0; j < runLen; ++j) {
            const Int8 v = Mu[pos + j];
            if (v >= 0) { Mu[pos + j] = 0; continue; }   // square factor -> mu = 0
            const int S    = v & 0x7F;
            const int base = ((v & 1) << 1) - 1;         // 2*par - 1 in {-1,+1}
            Mu[pos + j] = static_cast<Int8>((S > fl) ? -base : base);
        }
#endif
        pos += runLen;
    }
}

// ============================================================================
// LargePrimeHitScheduler — bucket sieve for primes > segment size
// ============================================================================

UInt64 SegmentedMobiusSieveCore::LargePrimeHitScheduler::skipStencilSquare4(
    UInt64 m, UInt64 p) noexcept {
    // The ring was sized for a p-wide jump.  A skipped hit makes that 2p,
    // so skip the skip when 2p is too large.
    constexpr UInt64 maxSkipPrime = (LP_SIZE - 1) * M2 / 2;
    if (__builtin_expect((m & 3) == 0, false) && p <= maxSkipPrime)
        m += p;
    return m;
}

SegmentedMobiusSieveCore::LargePrimeHitScheduler::LargePrimeHitScheduler(
    const UInt64& baseLo,
    const UInt64& lo,
    const UInt64& hi,
    const UInt64& subSegmentLen,
    const PrimesVecT& primes,
    const UInt32& pInd0,
    const UInt32& pInd1,
    std::vector<PVecT>& lpBucket,
    const SieveQuotientCache* cache
)
    : mBaseLo(baseLo)
    , mLo(lo)
    , mHi(hi)
    , mSubSegmentLen(subSegmentLen)
    , mFinalSubSegIndex((hi - lo) / subSegmentLen)
    , mCurrentSubSegIndex(0)
    , mP(primes.data())
    , mPInd0(pInd0)
    , mPInd1(pInd1)
    , mAllSkipsFit(static_cast<UInt64>(primes[pInd1]) <= (LP_SIZE - 1) * M2 / 2)
    , mBuckets(lpBucket)
    , mCache(cache)
{
    if (mBuckets.size() < LP_NBUCKETS)
        mBuckets.resize(LP_NBUCKETS);

    const UInt64 L = subSegLo(mCurrentSubSegIndex);

    for (UInt32 i = mPInd0; i <= mPInd1; ++i) {
        const UInt32 p = mP[i];

        if (p > mHi)
            break;

        UInt64 m;
        if constexpr (UseDivisionFree) {
            m = p * mCache->ceilDiv(L, i, p);
        } else {
            m = p * (((L - 1) / p) + 1);
        }
        m = skipStencilSquare4(m, p);
        const UInt64 subSeg = subSegIndexOf(m);
        if (subSeg < mFinalSubSegIndex || (subSeg == mFinalSubSegIndex && m <= mHi))
            bucketPush(subSeg, packEntry(p, (m - mLo) - subSeg * M2));
    }
}

// Pre-populated constructor: bookkeeping only, no prime scan.
SegmentedMobiusSieveCore::LargePrimeHitScheduler::LargePrimeHitScheduler(
    PrePopulated,
    const UInt64& baseLo,
    const UInt64& lo,
    const UInt64& hi,
    const UInt64& subSegmentLen,
    const PrimesVecT& primes,
    const UInt32& pInd0,
    const UInt32& pInd1,
    std::vector<PVecT>& lpBucket,
    const SieveQuotientCache* cache
)
    : mBaseLo(baseLo)
    , mLo(lo)
    , mHi(hi)
    , mSubSegmentLen(subSegmentLen)
    , mFinalSubSegIndex((hi - lo) / subSegmentLen)
    , mCurrentSubSegIndex(0)
    , mP(primes.data())
    , mPInd0(pInd0)
    , mPInd1(pInd1)
    , mAllSkipsFit(static_cast<UInt64>(primes[pInd1]) <= (LP_SIZE - 1) * M2 / 2)
    , mBuckets(lpBucket)
    , mCache(cache)
{
    // Buckets are already populated by the external routing pass.
    // Just ensure the array is sized.
    if (mBuckets.size() < LP_NBUCKETS)
        mBuckets.resize(LP_NBUCKETS);
}

// subSegLo/subSegIndexOf use the compile-time constant M2 rather than the
// mSubSegmentLen member (always M2 in practice — both construction sites pass
// it). With a constant divisor the compiler strength-reduces the division
// in subSegIndexOf, which sits on the per-hit path of sieveSubSegment, to a
// multiply + shift.
UInt64 SegmentedMobiusSieveCore::LargePrimeHitScheduler::subSegLo(
    const UInt64& subSegIndex) const noexcept {
    return mLo + subSegIndex * M2;
}

UInt64 SegmentedMobiusSieveCore::LargePrimeHitScheduler::subSegIndexOf(
    const UInt64& x) const noexcept {
    return (x - mLo) / M2;
}

UInt64 SegmentedMobiusSieveCore::LargePrimeHitScheduler::ringIndex(
    const UInt64& subSeg, EntryT e) noexcept {
#if SIEVE_SUBS_ACTIVE
    return (subSeg & (LP_SIZE - 1)) * LP_SUBS + ((e & LP_OFF_MASK) >> LP_SUB_SHIFT);
#else
    (void)e;
    return subSeg & (LP_SIZE - 1);
#endif
}

bool SegmentedMobiusSieveCore::LargePrimeHitScheduler::emptySubSegment(
    const UInt64& subSeg) const noexcept {
#if SIEVE_SUBS_ACTIVE
    const UInt64 b0 = (subSeg & (LP_SIZE - 1)) * LP_SUBS;
    for (UInt64 sb = 0; sb < LP_SUBS; ++sb)
        if (!mBuckets[b0 + sb].empty()) return false;
    return true;
#else
    return mBuckets[subSeg & (LP_SIZE - 1)].empty();
#endif
}

void SegmentedMobiusSieveCore::LargePrimeHitScheduler::bucketPush(
    const UInt64& subSeg, EntryT e) noexcept {
    mBuckets[ringIndex(subSeg, e)].push_back(e);
}

SegmentedMobiusSieveCore::LargePrimeHitScheduler::EntryT
SegmentedMobiusSieveCore::LargePrimeHitScheduler::packEntry(UInt32 p, UInt64 off) noexcept {
#if SIEVE_NARROW_ENTRY
    (void)off;                      // offset recomputed per hit from p
    return (EntryT)p;
#else
    const UInt64 s = p / M2;        // constant divisor — strength-reduced
    const UInt64 r = p - s * M2;
    return (EntryT(UInt8(SegmentedMobiusSieveCore::primeLogWeight(p))) << LP_LOG_SHIFT)
         | (s << LP_S_SHIFT) | (r << LP_R_SHIFT) | off;
#endif
}

template<bool AllSkipsFit>
void SegmentedMobiusSieveCore::LargePrimeHitScheduler::sieveSubSegmentImpl(
    Int8* __restrict muBase) noexcept {
    if (__builtin_expect(mCurrentSubSegIndex > mFinalSubSegIndex, false)) {
        return;
    }

    if (__builtin_expect(emptySubSegment(mCurrentSubSegIndex), false)) {
        ++mCurrentSubSegIndex;
        return;
    }

    const UInt64 L = subSegLo(mCurrentSubSegIndex);

    // Process each prime in this sub-segment's bucket: apply its hit, then
    // forward the prime to the bucket containing its next multiple.
    // This ensures each large prime is touched at most once per sub-segment.
    //
    // Squared factors are handled once per segment by sieveSquaresPass,
    // so no per-hit divisibility check is needed here.
    //
    // Entries are self-contained (off, p mod M2, p / M2, log weight), so a
    // hit is a byte RMW with the entry's log field, and forwarding is the
    // Bresenham step off' = off + r with the carry advancing the sub-segment
    // stride — no division, no multiply, no CLZ, no prime-array load.
    const UInt64 base    = L - mBaseLo;    // muBase index of this sub-segment's start
    [[maybe_unused]] const UInt64 lastOff = (mHi - mLo) - mFinalSubSegIndex * M2;  // last valid
                                           // offset within the final sub-segment

    // The mu RMW targets are random offsets within the sub-segment — invisible to
    // hardware prefetchers — but the entry stream is sequential, so each
    // future target is known PF entries in advance. Prefetch with write
    // intent; the line is reused by later hits and by the fused finalize.
    [[maybe_unused]] constexpr size_t PF = 16;

    // With sub-buckets, process the sub-segment's LP_SUBS offset bands in order:
    // each band's RMWs land in a ~128 KB window, so the mu lines stay
    // kept in L1 across the band. Without them, LP_SUBS == 1 and this
    // loop runs once over the sub-segment's single bucket.
    const UInt64 ring0 = (mCurrentSubSegIndex & (LP_SIZE - 1)) * LP_SUBS;
    for (UInt64 sb = 0; sb < LP_SUBS; ++sb) {
        PVecT& pvec = mBuckets[ring0 + sb];
        const EntryT* e = pvec.data();
        const size_t  n = pvec.size();

#if SIEVE_NARROW_ENTRY
        // Narrow entries hold only the prime: one raw divide per hit
        // recomputes the offset, CLZ recomputes the log weight. The quotient
        // cache cannot help — it is keyed by prime index, which the entry
        // does not store, and carrying the index would grow the entry back
        // toward 8 bytes.
#if SIEVE_NARROW_SUBS_ACTIVE
        // Decode and forward the prime stream first, staging each current hit
        // by its offset band. The second pass then applies cache-local mu RMWs.
        for (size_t i = 0; i < n; ++i) {
            const UInt64 p = e[i];
            const UInt64 m = p * ((L - 1) / p + 1);
            const UInt64 off = m - L;
            const UInt32 hit = static_cast<UInt32>(off)
                | (static_cast<UInt32>(SegmentedMobiusSieveCore::primeLogWeight(
                       static_cast<UInt32>(p))) << LP_OFF_BITS);
            mTransientHits[off >> LP_TRANSIENT_SHIFT].push_back(hit);

            UInt64 nextM = m + p;
            if constexpr (AllSkipsFit) {
                if (__builtin_expect((nextM & 3) == 0, false))
                    nextM += p;
            } else {
                nextM = skipStencilSquare4(nextM, p);
            }
            if (nextM <= mHi)
                bucketPush((nextM - mLo) / M2, (EntryT)p);
        }

        for (TransientHitVecT& hits : mTransientHits) {
            for (const UInt32 hit : hits) {
                muBase[base + (hit & LP_OFF_MASK)]
                    += static_cast<Int8>(hit >> LP_OFF_BITS);
            }
            hits.clear();
        }
#else
        // Without offset bands, apply each random target immediately. No
        // useful target prefetch is available before the divide computes it.
        for (size_t i = 0; i < n; ++i) {
            const UInt64 p = e[i];
            const UInt64 m = p * ((L - 1) / p + 1);   // smallest multiple of p >= L
            muBase[base + (m - L)] += SegmentedMobiusSieveCore::primeLogWeight(
                static_cast<UInt32>(p)
            );
            UInt64 nextM = m + p;
            if constexpr (AllSkipsFit) {
                if (__builtin_expect((nextM & 3) == 0, false))
                    nextM += p;
            } else {
                nextM = skipStencilSquare4(nextM, p);
            }
            if (nextM <= mHi)
                bucketPush((nextM - mLo) / M2, (EntryT)p);
        }
#endif
#elif SIEVE_TWO_PASS
        // Pass 1: apply all mu RMWs — a pure scatter loop, so the out-of-order
        // window holds the maximum number of outstanding misses.
        for (size_t i = 0; i < n; ++i) {
            const size_t ipf = (i + PF < n) ? i + PF : n - 1;
            __builtin_prefetch(&muBase[base + (e[ipf] & LP_OFF_MASK)], 1, 3);
            const EntryT entry = e[i];
            muBase[base + (entry & LP_OFF_MASK)] += (Int8)(entry >> LP_LOG_SHIFT);
        }
        // Pass 2: forward entries — pure ALU plus bucket appends; the entry
        // stream is cache-hot from pass 1.
        for (size_t i = 0; i < n; ++i) {
            const EntryT entry = e[i];
            const UInt64 r = (entry >> LP_R_SHIFT) & LP_OFF_MASK;
            const UInt64 s = (entry >> LP_S_SHIFT) & LP_S_MASK;
            UInt64 noff = (entry & LP_OFF_MASK) + r;
            const UInt64 carry = noff >= M2;
            noff -= M2 & (UInt64(0) - carry);
            UInt64 nSubSeg = mCurrentSubSegIndex + s + carry;

            // M2 is divisible by 4, so the absolute residue depends only on
            // mLo and noff.  A second packed step skips the squareful hit.
            if (__builtin_expect(((mLo + noff) & 3) == 0, false)) {
                bool canSkip = true;
                if constexpr (!AllSkipsFit) {
                    constexpr UInt64 maxSkipStride = (LP_SIZE - 1) / 2;
                    canSkip = s < maxSkipStride
                           || (s == maxSkipStride && r <= M2 / 2);
                }
                if (canSkip) {
                    noff += r;
                    const UInt64 carry2 = noff >= M2;
                    noff -= M2 & (UInt64(0) - carry2);
                    nSubSeg += s + carry2;
                }
            }

            if (nSubSeg < mFinalSubSegIndex || (nSubSeg == mFinalSubSegIndex && noff <= lastOff))
                bucketPush(nSubSeg, (entry & ~LP_OFF_MASK) | noff);
        }
#else
        for (size_t i = 0; i < n; ++i) {
            const size_t ipf = (i + PF < n) ? i + PF : n - 1;
            __builtin_prefetch(&muBase[base + (e[ipf] & LP_OFF_MASK)], 1, 3);

            const EntryT entry = e[i];
            const UInt64 off = entry & LP_OFF_MASK;

            muBase[base + off] += (Int8)(entry >> LP_LOG_SHIFT);

            // The carry is data-random (~50/50), so keep it branchless.
            const UInt64 r = (entry >> LP_R_SHIFT) & LP_OFF_MASK;
            const UInt64 s = (entry >> LP_S_SHIFT) & LP_S_MASK;
            UInt64 noff = off + r;
            const UInt64 carry = noff >= M2;
            noff -= M2 & (UInt64(0) - carry);
            UInt64 nSubSeg = mCurrentSubSegIndex + s + carry;

            // M2 is divisible by 4, so the absolute residue depends only on
            // mLo and noff.  A second packed step skips the squareful hit.
            if (__builtin_expect(((mLo + noff) & 3) == 0, false)) {
                bool canSkip = true;
                if constexpr (!AllSkipsFit) {
                    constexpr UInt64 maxSkipStride = (LP_SIZE - 1) / 2;
                    canSkip = s < maxSkipStride
                           || (s == maxSkipStride && r <= M2 / 2);
                }
                if (canSkip) {
                    noff += r;
                    const UInt64 carry2 = noff >= M2;
                    noff -= M2 & (UInt64(0) - carry2);
                    nSubSeg += s + carry2;
                }
            }

            if (nSubSeg < mFinalSubSegIndex || (nSubSeg == mFinalSubSegIndex && noff <= lastOff))
                bucketPush(nSubSeg, (entry & ~LP_OFF_MASK) | noff);
        }
#endif

        pvec.clear();
    }  // sub-bucket loop

    ++mCurrentSubSegIndex;
}

void SegmentedMobiusSieveCore::LargePrimeHitScheduler::sieveSubSegment(
    Int8* __restrict muBase) noexcept {
#if SIEVE_NARROW_ENTRY
    if (__builtin_expect(mAllSkipsFit, true))
        sieveSubSegmentImpl<true>(muBase);
    else
        sieveSubSegmentImpl<false>(muBase);
#else
    sieveSubSegmentImpl<false>(muBase);
#endif
}

// END upstream SegmentedMobiusSieve.cpp

// Driver for the standalone amalgamation 400958_01.cpp.
#include <charconv>
#include <chrono>
#include <csignal>
#include <cstdio>
#include <cstring>
#include <fcntl.h>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <sys/file.h>
#include <unistd.h>

namespace a400958 {
using Clock = std::chrono::steady_clock;
volatile std::sig_atomic_t stopped = 0;
void stop(int signum) { stopped = signum; }

UInt64 number(std::string_view s) {
    UInt64 v = 0;
    auto r = std::from_chars(s.data(), s.data() + s.size(), v);
    if (r.ec != std::errc() || r.ptr != s.data() + s.size())
        throw std::runtime_error("invalid nonnegative integer: " + std::string(s));
    return v;
}
UInt64 power10(unsigned n) {
    UInt64 v = 1;
    while (n--) v *= 10;
    return v;
}
UInt64 integer_sqrt(UInt64 n) {
    UInt64 r = static_cast<UInt64>(std::sqrt(static_cast<long double>(n)));
    while (r + 1 <= n / (r + 1)) ++r;
    while (r > n / r) --r;
    return r;
}

struct Options {
    unsigned max_n = 13;
    unsigned threads = 4;
    UInt64 segment = 138600000;
    UInt64 stop_after_blocks = 0;
    std::string checkpoint = "400958_01.checkpoint";
    bool no_checkpoint = false;
};
Options options(int argc, char** argv) {
    Options o;
    for (int i = 1; i < argc; ++i) {
        std::string_view a(argv[i]);
        if (a == "--help" || a == "-h") {
            std::cout << "Usage: " << argv[0] << " [options]\n"
                "  --max-n N              output a(0)..a(N), default 13, range 0..16\n"
                "  --threads T            OpenMP threads, default 4, range 1..256\n"
                "  --segment B            pairs per block, default 138600000\n"
                "  --checkpoint FILE      default 400958_01.checkpoint\n"
                "  --no-checkpoint        start from 1, do not read/write a checkpoint\n"
                "  --stop-after-blocks K  stop cleanly after K new blocks (0: unlimited)\n"
                "Results (n a(n)) go to stdout; progress goes to stderr.\n"
                "A resumed run reprints all completed rows; redirect with >, not >>.\n";
            std::exit(0);
        }
        if (a == "--no-checkpoint") { o.no_checkpoint = true; continue; }
        if (i + 1 == argc) throw std::runtime_error("missing option value");
        const std::string_view value(argv[++i]);
        if (a == "--checkpoint") {
            if (value.empty()) throw std::runtime_error("empty checkpoint path");
            o.checkpoint = value;
        } else if (a == "--max-n") {
            UInt64 n = number(value);
            if (n > 16) throw std::runtime_error("max-n must be in 0..16");
            o.max_n = static_cast<unsigned>(n);
        } else if (a == "--threads") {
            UInt64 t = number(value);
            if (t < 1 || t > 256) throw std::runtime_error("threads must be in 1..256");
            o.threads = static_cast<unsigned>(t);
        } else if (a == "--segment") {
            o.segment = number(value);
            if (o.segment < 1 || o.segment > 2000000000)
                throw std::runtime_error("segment must be in 1..2000000000");
        } else if (a == "--stop-after-blocks") {
            o.stop_after_blocks = number(value);
        } else {
            throw std::runtime_error("unknown option: " + std::string(a));
        }
    }
    return o;
}

// One writer per checkpoint. Lock is retained until the process exits.
class Lock {
    int fd_ = -1;
public:
    explicit Lock(const std::string& path, bool disabled) {
        if (disabled) return;
        fd_ = ::open((path + ".lock").c_str(), O_RDWR | O_CREAT, 0600);
        if (fd_ < 0) throw std::runtime_error("cannot open checkpoint lock");
        if (::flock(fd_, LOCK_EX | LOCK_NB) != 0) {
            ::close(fd_);
            fd_ = -1;
            throw std::runtime_error("checkpoint is locked by another process");
        }
    }
    Lock(const Lock&) = delete;
    Lock& operator=(const Lock&) = delete;
    ~Lock() { if (fd_ >= 0) ::close(fd_); }
};

struct State {
    UInt64 next = 1;       // Next pair index, so sum = C(next - 1).
    Int64 sum = 0;
    std::vector<Int64> rows;
};

UInt64 checksum(std::string_view s) {
    UInt64 h = 14695981039346656037ULL;
    for (unsigned char c : s) { h ^= c; h *= 1099511628211ULL; }
    return h;
}

State load(const Options& o) {
    State s;
    if (o.no_checkpoint) return s;
    errno = 0;
    std::ifstream f(o.checkpoint, std::ios::binary);
    if (!f) {
        if (errno == ENOENT) return s;
        throw std::runtime_error("cannot read checkpoint");
    }
    f.seekg(0, std::ios::end);
    auto length = f.tellg();
    if (length < 0 || length > 4096) throw std::runtime_error("invalid checkpoint size");
    f.seekg(0);
    std::string all(static_cast<std::size_t>(length), '\0');
    if (!f.read(all.data(), static_cast<std::streamsize>(all.size())))
        throw std::runtime_error("cannot read complete checkpoint");
    const auto mark = all.rfind("checksum ");
    if (mark == std::string::npos) throw std::runtime_error("checkpoint has no checksum");
    const std::string body = all.substr(0, mark);
    std::istringstream tail(all.substr(mark + 9));
    UInt64 digest = 0;
    std::string junk;
    if (!(tail >> std::hex >> digest) || (tail >> junk) || digest != checksum(body))
        throw std::runtime_error("checkpoint checksum mismatch");
    std::istringstream data(body);
    std::string magic;
    unsigned count = 0;
    if (!(data >> magic >> s.next >> s.sum >> count) || magic != "A400958-01-v1" ||
        s.next < 1 || s.next > power10(16) + 1 || count > 17)
        throw std::runtime_error("invalid checkpoint header");
    for (unsigned n = 0; n < count; ++n) {
        unsigned index = 100;
        Int64 v = 0;
        if (!(data >> index >> v) || index != n ||
            v < -static_cast<Int64>(power10(n)) || v > static_cast<Int64>(power10(n)))
            throw std::runtime_error("invalid checkpoint result rows");
        s.rows.push_back(v);
    }
    if (data >> junk) throw std::runtime_error("extra checkpoint data");
    unsigned expected = 0;
    while (expected <= 16 && power10(expected) < s.next) ++expected;
    if (count != expected || s.sum < -static_cast<Int64>(s.next - 1) ||
        s.sum > static_cast<Int64>(s.next - 1) ||
        (!s.rows.empty() && s.next == power10(count - 1) + 1 && s.sum != s.rows.back()))
        throw std::runtime_error("inconsistent checkpoint state");
    if (s.next > power10(o.max_n) + 1)
        throw std::runtime_error("checkpoint is beyond requested max-n; use another file");
    return s;
}

void save(const Options& o, const State& s) {
    if (o.no_checkpoint) return;
    std::ostringstream data;
    data << "A400958-01-v1\n" << s.next << ' ' << s.sum << ' ' << s.rows.size() << '\n';
    for (std::size_t n = 0; n < s.rows.size(); ++n) data << n << ' ' << s.rows[n] << '\n';
    const std::string body = data.str();
    data << "checksum " << std::hex << checksum(body) << '\n';
    const std::string bytes = data.str();
    const std::string temp = o.checkpoint + ".tmp." + std::to_string(::getpid());
    int fd = ::open(temp.c_str(), O_WRONLY | O_CREAT | O_EXCL, 0600);
    if (fd < 0) throw std::runtime_error("cannot create temporary checkpoint");
    std::size_t done = 0;
    bool ok = true;
    while (done < bytes.size()) {
        ssize_t written = ::write(fd, bytes.data() + done, bytes.size() - done);
        if (written < 0 && errno == EINTR) continue;
        if (written <= 0) { ok = false; break; }
        done += static_cast<std::size_t>(written);
    }
    if (ok && ::fsync(fd) != 0) ok = false;
    if (::close(fd) != 0) ok = false;
    if (!ok || ::rename(temp.c_str(), o.checkpoint.c_str()) != 0) {
        ::unlink(temp.c_str());
        throw std::runtime_error("checkpoint write/rename failed");
    }
    // Persist the rename where directory fsync is supported.
    const auto slash = o.checkpoint.find_last_of('/');
    const std::string parent = slash == std::string::npos ? "." :
                               slash == 0 ? "/" : o.checkpoint.substr(0, slash);
    fd = ::open(parent.c_str(), O_RDONLY);
    if (fd < 0) throw std::runtime_error("cannot open checkpoint directory");
    const int synced = ::fsync(fd);
    const int sync_error = errno;
    ::close(fd);
    if (synced != 0 && sync_error != EINVAL && sync_error != ENOTSUP)
        throw std::runtime_error("checkpoint directory sync failed");
}

void row(unsigned n, Int64 value) {
    if (std::printf("%u %lld\n", n, static_cast<long long>(value)) < 0 ||
        std::fflush(stdout) != 0) throw std::runtime_error("stdout write failed");
}

int run(int argc, char** argv) {
    const Options o = options(argc, argv);
    const Lock lock(o.checkpoint, o.no_checkpoint);
    State s = load(o);
    for (unsigned n = 0; n < s.rows.size(); ++n) row(n, s.rows[n]);
    const UInt64 limit = power10(o.max_n);
    if (s.next > limit) {
        std::fprintf(stderr, "Already complete through n=%u.\n", o.max_n);
        return 0;
    }
    std::signal(SIGINT, stop);
    std::signal(SIGTERM, stop);
    omp_set_dynamic(0);
    omp_set_num_threads(static_cast<int>(o.threads));
    const UInt64 initial = s.next;
    const auto begin = Clock::now();
    auto last_save = begin;
    auto last_progress = begin;
    const UInt64 root = integer_sqrt(limit + 1);
    if (root > SegmentedMobiusSieveCore::schedulerReach())
        throw std::runtime_error("sieve endpoint exceeds bucket scheduler range");
    auto primes = SegmentedMobiusSieveCore::primesUpTo(
        static_cast<UInt32>(std::max<UInt64>(360, root)));
    SegmentedMobiusSieveCore sieve(std::min(o.segment, limit - s.next + 1) + 1);
    std::fprintf(stderr, "A400958 n=0..%u, next=%llu, threads=%u, segment=%llu\n",
                 o.max_n, static_cast<unsigned long long>(s.next), o.threads,
                 static_cast<unsigned long long>(o.segment));
    UInt64 blocks = 0;
    while (s.next <= limit && !stopped) {
        const unsigned n = static_cast<unsigned>(s.rows.size());
        const UInt64 end = std::min(s.next + o.segment - 1, power10(n));
        sieve.sieve(s.next, end + 1, primes);
        const Int8* mu = sieve.data();
        const UInt64 size = end - s.next + 1;
        Int64 part = 0;
        #pragma omp parallel for schedule(static) reduction(+:part) if(size >= 100000)
        for (UInt64 i = 0; i < size; ++i) part += static_cast<Int64>(mu[i]) * mu[i + 1];
        s.sum += part;
        s.next = end + 1;
        ++blocks;
        const auto now = Clock::now();
        const bool reached = end == power10(n);
        if (reached) s.rows.push_back(s.sum);
        const bool requested_stop = o.stop_after_blocks && blocks >= o.stop_after_blocks;
        if (reached || stopped || requested_stop || now - last_save >= std::chrono::seconds(30)) {
            save(o, s);
            last_save = now;
        }
        if (reached) row(n, s.sum);
        if (reached || now - last_progress >= std::chrono::seconds(30)) {
            const double elapsed = std::chrono::duration<double>(now - begin).count();
            std::fprintf(stderr, "done=%llu/%llu (%.6f%%), sum=%lld, elapsed=%.1fs, rate=%.3f Gpairs/s\n",
                static_cast<unsigned long long>(end), static_cast<unsigned long long>(limit),
                100.0 * static_cast<double>(end) / static_cast<double>(limit),
                static_cast<long long>(s.sum), elapsed,
                static_cast<double>(s.next - initial) / std::max(1e-9, elapsed) / 1e9);
            last_progress = now;
        }
        if (requested_stop) break;
    }
    save(o, s);
    if (std::ferror(stderr)) throw std::runtime_error("stderr write failed");
    std::fprintf(stderr, "%s: next=%llu, completed through n=%d\n",
                 s.next > limit ? "Complete" : "Stopped",
                 static_cast<unsigned long long>(s.next), static_cast<int>(s.rows.size()) - 1);
    return stopped ? 128 + stopped : 0;
}
} // namespace a400958

int main(int argc, char** argv) {
    try { return a400958::run(argc, argv); }
    catch (const std::exception& e) {
        std::fprintf(stderr, "error: %s\n", e.what());
        return 1;
    }
}
