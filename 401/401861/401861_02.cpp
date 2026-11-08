// A401861: maximum size of a family of distinct subsets of {1,...,n}
// whose pairwise intersections are nonempty arithmetic progressions.
// Singletons and two-element sets count as arithmetic progressions.
// Variant _02 selects coloring candidates in descending vertex-index order.
// The graph, lower bound, and pruning formulas are unchanged from _01.
//
// Independent C++17 implementation; no third-party source code is used.
// Usage: ./401861_02 [N] [--progress] (default N=9; 1 <= N <= 14)
// Prints a(1),...,a(N), flushing each completed term. No files are written.
// Optional progress goes to stderr. Interrupting preserves completed terms.
//
// Mathematical reductions:
// * Vertices are all nonempty subsets; two vertices are adjacent exactly
//   when their intersection is a nonempty AP. The answer is the clique
//   number. Omitting the empty set is harmless: a family containing it
//   has at most one member, also attainable with a nonempty set.
// * Szabo's explicit construction supplies an initial clique (lower bound),
//   checked directly before use. Its size is never used as an upper bound.
//   The search does NOT assume that all family members share one element.
// * Greedy proper coloring of the candidate graph bounds any extra clique
//   by its number of colors. Vertices are appended by color class and
//   processed backwards, so each remaining prefix has the recorded bound.
// * The number of remaining candidates is another valid upper bound.
//
// Resource limits are not mathematical pruning: reaching them stops the
// unfinished term with a nonzero exit status, without printing its value.
// Graph storage is <32 MiB at n=14. Frame payload is limited to 128 MiB;
// an explicit heap stack avoids recursion-depth/stack-overflow problems.
// At n<=14: V<=16383, words<=256, graph words<=4194048; products,
// counters, vertex/color IDs and subset shifts fit their declared types.
// Search visits are counted with saturation, never unsigned wraparound.

#include <algorithm>
#include <chrono>
#include <csignal>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {
using Word = std::uint64_t;
using Bits = std::vector<Word>;
using Clock = std::chrono::steady_clock;
constexpr unsigned max_n = 14;
constexpr std::size_t frame_budget = 128U * 1024U * 1024U;
volatile std::sig_atomic_t stop_signal = 0;

void signal_handler(int signum) { stop_signal = signum; }
struct Interrupted final : std::exception {};

unsigned checked_n(unsigned n) {
    if (n < 1 || n > max_n) throw std::invalid_argument("N must be in 1..14");
    return n;
}
std::uint32_t element_bit(unsigned x) {
    if (x < 1 || x > max_n) throw std::logic_error("element outside supported range");
    return std::uint32_t{1} << (x - 1U);
}

std::size_t population(const Bits& bits) {
    std::size_t count = 0;
    for (Word x : bits) count += static_cast<unsigned>(__builtin_popcountll(x));
    return count;
}
void erase(Bits& bits, std::size_t vertex) {
    bits[vertex / 64U] &= ~(Word{1} << (vertex % 64U));
}
std::size_t first(const Bits& bits) {
    // Select the greatest vertex index. The builtin is never given zero.
    for (std::size_t w = bits.size(); w != 0; --w)
        if (bits[w-1U] != 0)
            return (w-1U)*64U + 63U - static_cast<unsigned>(__builtin_clzll(bits[w-1U]));
    throw std::logic_error("first() called on an empty bitset");
}
bool is_progression(std::uint32_t mask, unsigned n) {
    unsigned seen = 0, previous = 0, difference = 0;
    for (unsigned x = 1; x <= n; ++x) {
        if ((mask & (std::uint32_t{1} << (x - 1U))) == 0) continue;
        if (seen == 1) difference = x - previous;
        if (seen >= 2 && x - previous != difference) return false;
        previous = x;
        ++seen;
    }
    return seen != 0;
}

struct Frame {
    Bits candidates;
    std::vector<std::uint16_t> order;
    std::vector<std::uint16_t> colors;
    std::size_t remaining = 0;
    std::size_t bytes = 0;
};

class Search {
    unsigned n_;
    std::size_t vertices_, words_;
    std::vector<Word> edges_;
    std::vector<std::size_t> path_, witness_;
    std::uint64_t nodes_ = 0;
    std::size_t best_ = 0;
    bool progress_;
    Clock::time_point started_ = Clock::now(), last_report_ = started_;

    const Word* row(std::size_t v) const { return edges_.data() + v * words_; }
    void poll(bool force = false) {
        if (stop_signal != 0) throw Interrupted{};
        if (!progress_) return;
        if (!force && (nodes_ % 4096U) != 0) return;
        const auto now = Clock::now();
        if (now - last_report_ >= std::chrono::seconds(5)) {
            std::cerr << "n=" << n_ << ", lower=" << best_
                      << ", nodes=" << nodes_ << ", seconds="
                      << std::chrono::duration<double>(now - started_).count() << '\n';
            last_report_ = now;
        }
    }

    void build_graph() {
        const std::size_t size = std::size_t{1} << n_;
        std::vector<unsigned char> ap(size, 0);
        for (unsigned start = 1; start <= n_; ++start) {
            ap[std::size_t{1} << (start - 1U)] = 1;
            for (unsigned d = 1; d < n_; ++d) {
                std::uint32_t mask = std::uint32_t{1} << (start - 1U);
                for (unsigned x = start + d; x <= n_; x += d) {
                    mask |= std::uint32_t{1} << (x - 1U);
                    ap[mask] = 1;
                }
            }
        }
        // Independently validate the lookup predicate for every subset mask.
        for (std::size_t mask = 0; mask < size; ++mask)
            if ((ap[mask] != 0) != is_progression(static_cast<std::uint32_t>(mask), n_))
                throw std::logic_error("AP lookup validation failed");
        for (std::size_t u = 0; u < vertices_; ++u) {
            if ((u % 128U) == 0) poll(true);
            for (std::size_t v = 0; v < u; ++v) {
                if (ap[(u + 1U) & (v + 1U)] == 0) continue;
                edges_[u * words_ + v / 64U] |= Word{1} << (v % 64U);
                edges_[v * words_ + u / 64U] |= Word{1} << (u % 64U);
            }
        }
    }

    void seed_construction() {
        const unsigned center = (n_ + 1U) / 2U;
        const auto bit = element_bit;
        std::vector<unsigned char> selected(vertices_ + 1U, 0);
        selected[bit(center)] = 1;
        for (unsigned x = 1; x <= n_; ++x) {
            selected[bit(center) | bit(x)] = 1;
            for (unsigned y = x + 1U; y <= n_; ++y)
                selected[bit(center) | bit(x) | bit(y)] = 1;
        }
        for (unsigned d = 1; d <= (n_ - 1U) / 4U; ++d) {
            selected[bit(center - 2U*d) | bit(center) | bit(center + d)] = 0;
            selected[bit(center - d) | bit(center) | bit(center + 2U*d)] = 0;
            const auto a = bit(center - 2U*d);
            const auto b = bit(center - d);
            const auto c = bit(center);
            const auto e = bit(center + d);
            const auto f = bit(center + 2U*d);
            selected[a | b | c | e | f] = 1;
            selected[a | b | c | e] = 1;
            selected[b | c | e | f] = 1;
        }
        for (std::size_t mask = 1; mask <= vertices_; ++mask)
            if (selected[mask] != 0) witness_.push_back(mask - 1U);
        verify_witness(witness_);
        best_ = witness_.size();
    }

    void verify_witness(const std::vector<std::size_t>& family) const {
        Bits seen(words_, 0);
        for (std::size_t i = 0; i < family.size(); ++i) {
            const auto u = family[i];
            if (u >= vertices_ || (seen[u/64U] & (Word{1} << (u%64U))) != 0)
                throw std::logic_error("invalid or duplicate witness vertex");
            seen[u/64U] |= Word{1} << (u%64U);
            for (std::size_t j = 0; j < i; ++j)
                if (!is_progression(static_cast<std::uint32_t>((u+1U) & (family[j]+1U)), n_))
                    throw std::logic_error("invalid witness intersection");
        }
    }

    Frame color(Bits candidates, std::size_t live_bytes) {
        const std::size_t count = population(candidates);
        const std::size_t bytes = words_*sizeof(Word) + count*2U*sizeof(std::uint16_t);
        if (bytes > frame_budget - live_bytes)
            throw std::runtime_error("search memory limit reached; unfinished term not printed");
        Frame f;
        f.candidates = std::move(candidates);
        f.order.reserve(count);
        f.colors.reserve(count);
        f.bytes = f.candidates.capacity()*sizeof(Word)
                + (f.order.capacity()+f.colors.capacity())*sizeof(std::uint16_t);
        if (f.bytes > frame_budget - live_bytes)
            throw std::runtime_error("search memory limit reached; unfinished term not printed");
        Bits rest = f.candidates;
        std::size_t left = count;
        std::uint16_t number = 0;
        while (left != 0) {
            poll(true);
            ++number;  // <=count<=16383, fits uint16_t.
            Bits available = rest;
            while (population(available) != 0) {
                const std::size_t v = first(available);
                f.order.push_back(static_cast<std::uint16_t>(v));
                f.colors.push_back(number);
                erase(rest, v);
                erase(available, v);
                --left;
                const Word* adjacent = row(v);
                for (std::size_t w = 0; w < words_; ++w) available[w] &= ~adjacent[w];
            }
        }
        f.remaining = count;
        return f;
    }

public:
    explicit Search(unsigned n, bool progress)
        : n_(checked_n(n)), vertices_((std::size_t{1} << n_)-1U),
          words_((vertices_+63U)/64U), edges_(vertices_*words_, 0), progress_(progress) {
        // Also validate n inside the constructor before size arithmetic.
        build_graph();
        seed_construction();
    }

    std::size_t run() {
        Bits all(words_, std::numeric_limits<Word>::max());
        if ((vertices_ % 64U) != 0)
            all.back() = (Word{1} << (vertices_ % 64U))-1U;
        std::vector<Frame> stack;
        stack.reserve(vertices_+1U);
        path_.reserve(vertices_);
        stack.push_back(color(std::move(all), 0));
        std::size_t live_bytes = stack.back().bytes;
        while (!stack.empty()) {
            poll();
            Frame& f = stack.back();
            if (f.remaining == 0 || path_.size()+f.colors[f.remaining-1U] <= best_) {
                live_bytes -= f.bytes;
                stack.pop_back();
                if (!stack.empty()) path_.pop_back();
                continue;
            }
            const std::size_t v = f.order[--f.remaining];
            Bits child(words_);
            const Word* adjacent = row(v);
            for (std::size_t w = 0; w < words_; ++w) child[w] = f.candidates[w] & adjacent[w];
            erase(f.candidates, v);
            if (nodes_ != std::numeric_limits<std::uint64_t>::max()) ++nodes_;
            if (path_.size()+1U > best_) {
                witness_ = path_;
                witness_.push_back(v);
                best_ = witness_.size();
            }
            if (path_.size()+1U+population(child) <= best_) continue;
            Frame next = color(std::move(child), live_bytes);
            live_bytes += next.bytes;
            path_.push_back(v);
            stack.push_back(std::move(next));
        }
        poll(true);
        verify_witness(witness_);
        if (progress_)
            std::cerr << "n=" << n_ << ": " << best_ << " (optimal), nodes=" << nodes_
                      << ", seconds=" << std::chrono::duration<double>(Clock::now()-started_).count() << '\n';
        return best_;
    }
};

unsigned parse_n(const std::string& text) {
    if (text.empty()) throw std::invalid_argument("N must be an integer in 1..14");
    unsigned value = 0;
    for (char c : text) {
        if (c < '0' || c > '9') throw std::invalid_argument("N must be an integer in 1..14");
        const unsigned digit = static_cast<unsigned>(c - '0');
        if (value > max_n/10U || (value == max_n/10U && digit > max_n%10U))
            throw std::invalid_argument("N must be an integer in 1..14");
        value = value*10U + digit;
    }
    if (value == 0) throw std::invalid_argument("N must be an integer in 1..14");
    return value;
}
} // namespace

int main(int argc, char** argv) {
    bool printed = false;
    try {
        if (argc > 3) throw std::invalid_argument("usage: ./401861_02 [N] [--progress], 1 <= N <= 14");
        unsigned limit = 9U;
        bool progress = false, have_limit = false;
        for (int i = 1; i < argc; ++i) {
            const std::string arg(argv[i]);
            if (arg == "--progress" && !progress) progress = true;
            else if (!have_limit) { limit = parse_n(arg); have_limit = true; }
            else throw std::invalid_argument("duplicate or invalid argument");
        }
        if (std::signal(SIGINT, signal_handler) == SIG_ERR ||
            std::signal(SIGTERM, signal_handler) == SIG_ERR)
            throw std::runtime_error("cannot install interruption handlers");
        for (unsigned n = 1; n <= limit; ++n) {
            Search search(n, progress);
            const std::size_t value = search.run();
            if (printed) std::cout << ", ";
            std::cout << value << std::flush;
            if (!std::cout) throw std::runtime_error("stdout write failed");
            printed = true;
        }
        std::cout << '\n' << std::flush;
        if (!std::cout) throw std::runtime_error("stdout write failed");
        return 0;
    } catch (const Interrupted&) {
        if (printed) std::cout << '\n' << std::flush;
        std::cerr << "interrupted: unfinished term not printed\n";
        return 128 + static_cast<int>(stop_signal);
    } catch (const std::exception& error) {
        if (printed) std::cout << '\n' << std::flush;
        std::cerr << "error: " << error.what() << '\n';
        return 1;
    }
}
