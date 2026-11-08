// A401861: maximum size of a family of distinct subsets of {1,...,n}
// whose pairwise intersections are nonempty arithmetic progressions.
// Singletons and two-element sets count as arithmetic progressions.
// Independent C++17 implementation; no third-party source code is used.
//
// Build: c++ -O3 -std=c++17 -pthread 401861_03.cpp -o 401861_03
// Usage: ./401861_03 [N] [--threads T] [--progress]
// N=1..14, T=1..32; default N=9, T=min(8, hardware concurrency), or 1
// if hardware concurrency is unknown. Prints completed a(1),...,a(N).
// No files or network operations. Diagnostics go only to stderr.
// All workers are joined before an answer is printed. Interruption or any
// worker failure stops the unfinished term without printing its bound.
//
// Exactness:
// * The graph has one vertex per nonempty subset; adjacency means a nonempty
//   AP intersection. Every AP lookup is checked by an independent predicate.
// * Szabo's construction is checked and used ONLY as a lower bound.
// * Each worker uses the 01 version's proper-coloring prefix upper bound.
// * A branch (R,P) splits by vertices v in reverse color order, with child
//   (R+v, P intersect N(v)); v is then removed from the parent's P. Every
//   completion belongs to exactly one branch. A queued branch replaces that
//   same local branch, without discarding or duplicating its completions.
// * A bounded dynamic queue shares the first four branching levels. A full
//   queue causes local search. Queue order is not a pruning assumption.
// * The global lower bound is atomic and increases only with a checked
//   witness, under its mutex. A stale lower bound can only weaken pruning.
//   Graph data is immutable during worker execution; stacks are private.
// * done is set under the queue mutex only when pending and active tasks
//   are both zero. Any error cancels every worker and prevents an answer.
//
// Bounds/resources at N<=14, T<=32:
// V<=16383, words<=256; graph storage <32 MiB. All subset shifts are <14;
// word shifts are <64. Vertex and color IDs fit uint16_t. Each path is a
// clique with at most V vertices; path length + candidate/color bound <=2V.
// Queue holds <=4*T pending tasks; every prefix has <=4 elements. A job
// contains at most 256 uint64_t words. Worker frame payload budgets sum to
// at most 128 MiB; these exclude graph, queue, stack objects and allocator
// overhead, so this is NOT a hard total-process memory limit. Each worker
// reserves <=V+1 frame objects and <=V path entries. Allocation failures
// abort the unfinished term. Node counters use saturation, not wraparound.
// The signal handler only stores to a compile-time lock-free atomic<int>.

#include <algorithm>
#include <atomic>
#include <condition_variable>
#include <deque>
#include <mutex>
#include <thread>
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
constexpr unsigned max_threads = 32;
std::atomic<int> stop_signal{0};
static_assert(std::atomic<int>::is_always_lock_free,
              "signal handler requires lock-free atomic<int>");

void signal_handler(int signum) { stop_signal.store(signum, std::memory_order_relaxed); }
struct Interrupted final : std::exception {};
struct Cancelled final : std::exception {};

unsigned checked_n(unsigned n) {
    if (n < 1 || n > max_n) throw std::invalid_argument("N must be in 1..14");
    return n;
}
std::uint32_t element_bit(unsigned x) {
    if (x < 1 || x > max_n) throw std::logic_error("element outside supported range");
    return std::uint32_t{1} << (x - 1U);
}

unsigned bit_index(Word value) {
    // All callers check value != 0 before using the trailing-zero builtin.
    return static_cast<unsigned>(__builtin_ctzll(value));
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
    for (std::size_t w = 0; w < bits.size(); ++w)
        if (bits[w] != 0) return w * 64U + bit_index(bits[w]);
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


struct Task {
    std::vector<std::size_t> prefix;
    Bits candidates;
};

struct Shared {
    const unsigned threads;
    const std::size_t queue_limit;
    std::atomic<std::size_t> best;
    std::vector<std::size_t> witness;
    std::mutex witness_mutex;
    std::atomic<bool> cancelled{false};
    std::atomic<std::size_t> queued{0};
    std::vector<std::atomic<std::uint64_t>> visits;
    std::mutex queue_mutex, report_mutex;
    std::condition_variable ready;
    std::deque<Task> tasks;
    std::size_t active=0;
    bool done=false;
    std::exception_ptr error;
    Clock::time_point last_report=Clock::now();

    Shared(unsigned t,std::size_t lower,const std::vector<std::size_t>& example)
        : threads(t),queue_limit(4U*t),best(lower),witness(example),visits(t) {
        for (auto& value:visits) value.store(0,std::memory_order_relaxed);
    }
    std::uint64_t total_visits() const {
        std::uint64_t total=0;
        const auto limit=std::numeric_limits<std::uint64_t>::max();
        for (const auto& value:visits) {
            const auto v=value.load(std::memory_order_relaxed);
            total=v>limit-total ? limit : total+v;
        }
        return total;
    }
    void fail(std::exception_ptr reason) {
        {
            std::lock_guard<std::mutex> lock(queue_mutex);
            if (!error) error=reason;
            cancelled.store(true,std::memory_order_relaxed);
        }
        ready.notify_all();
    }
    bool take(Task& task) {
        std::unique_lock<std::mutex> lock(queue_mutex);
        ready.wait(lock,[&] {return cancelled.load(std::memory_order_relaxed) || done || !tasks.empty();});
        if (cancelled.load(std::memory_order_relaxed) || done) return false;
        task=std::move(tasks.front());
        tasks.pop_front();
        queued.store(tasks.size(),std::memory_order_relaxed);
        ++active;
        return true;
    }
    void finish() {
        {
            std::lock_guard<std::mutex> lock(queue_mutex);
            if (active==0) throw std::logic_error("invalid active task count");
            --active;
            if (active==0 && tasks.empty()) done=true;
        }
        ready.notify_all();
    }
    bool offer(const std::vector<std::size_t>& prefix,std::size_t v,Bits& candidates) {
        // Split at most the first four levels. A full queue is only a hint
        // to search locally, never a reason to discard a branch.
        if (threads==1 || prefix.size()>=4 || queued.load(std::memory_order_relaxed)>=queue_limit)
            return false;
        {
            std::lock_guard<std::mutex> lock(queue_mutex);
            if (cancelled.load(std::memory_order_relaxed)) throw Cancelled{};
            if (tasks.size()>=queue_limit) return false;
            Task task;
            task.prefix=prefix;
            task.prefix.push_back(v);
            task.candidates=std::move(candidates);
            tasks.push_back(std::move(task));
            queued.store(tasks.size(),std::memory_order_relaxed);
        }
        ready.notify_one();
        return true;
    }
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
        if (stop_signal.load(std::memory_order_relaxed) != 0) throw Interrupted{};
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


    struct Worker {
        const Search& graph_;
        Shared& shared_;
        const unsigned id_;
        const std::size_t words_, budget_;
        std::uint64_t nodes_=0;
        Clock::time_point last_report_=Clock::now();
        std::vector<std::size_t> path_;
        std::vector<Frame> stack_;

        Worker(const Search& graph,Shared& shared,unsigned id)
            :graph_(graph),shared_(shared),id_(id),words_(graph.words_),
             budget_(frame_budget/shared.threads) {
            path_.reserve(graph.vertices_);
            stack_.reserve(graph.vertices_+1U);
        }
        ~Worker() {shared_.visits[id_].store(nodes_,std::memory_order_relaxed);}

        void poll(bool force=false) {
            if (stop_signal.load(std::memory_order_relaxed)!=0) throw Interrupted{};
            if (shared_.cancelled.load(std::memory_order_relaxed)) throw Cancelled{};
            if (!graph_.progress_ || (!force && nodes_%4096U!=0)) return;
            const auto now=Clock::now();
            if (now-last_report_<std::chrono::seconds(5)) return;
            last_report_=now;
            shared_.visits[id_].store(nodes_,std::memory_order_relaxed);
            std::lock_guard<std::mutex> lock(shared_.report_mutex);
            if (now-shared_.last_report<std::chrono::seconds(5)) return;
            shared_.last_report=now;
            std::cerr<<"n="<<graph_.n_<<", lower="<<shared_.best.load(std::memory_order_relaxed)
                     <<", nodes~="<<shared_.total_visits()<<", threads="<<shared_.threads
                     <<", seconds="<<std::chrono::duration<double>(now-graph_.started_).count()<<'\n';
        }

        void publish(std::size_t v) {
            if (path_.size()+1U<=shared_.best.load(std::memory_order_relaxed)) return;
            std::lock_guard<std::mutex> lock(shared_.witness_mutex);
            if (path_.size()+1U<=shared_.best.load(std::memory_order_relaxed)) return;
            auto example=path_;
            example.push_back(v);
            // Complete all throwing work before publishing a new bound.
            graph_.verify_witness(example);
            shared_.witness.swap(example);
            shared_.best.store(shared_.witness.size(),std::memory_order_relaxed);
        }
    Frame color(Bits candidates, std::size_t live_bytes) {
        const std::size_t count = population(candidates);
        const std::size_t bytes = words_*sizeof(Word) + count*2U*sizeof(std::uint16_t);
        if (bytes > budget_ - live_bytes)
            throw std::runtime_error("search memory limit reached; unfinished term not printed");
        Frame f;
        f.candidates = std::move(candidates);
        f.order.reserve(count);
        f.colors.reserve(count);
        f.bytes = f.candidates.capacity()*sizeof(Word)
                + (f.order.capacity()+f.colors.capacity())*sizeof(std::uint16_t);
        if (f.bytes > budget_ - live_bytes)
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
                const Word* adjacent = graph_.row(v);
                for (std::size_t w = 0; w < words_; ++w) available[w] &= ~adjacent[w];
            }
        }
        f.remaining = count;
        return f;
    }

        void search(Task& task) {
            poll(true);
            path_.assign(task.prefix.begin(),task.prefix.end());
            const auto lower=shared_.best.load(std::memory_order_relaxed);
            if (path_.size()+population(task.candidates)<=lower) return;
            stack_.push_back(color(std::move(task.candidates),0));
            std::size_t live_bytes=stack_.back().bytes;
            while (!stack_.empty()) {
                poll();
                Frame& f=stack_.back();
                if (f.remaining==0 || path_.size()+f.colors[f.remaining-1U]<=
                    shared_.best.load(std::memory_order_relaxed)) {
                    live_bytes-=f.bytes;
                    stack_.pop_back();
                    if (!stack_.empty()) path_.pop_back();
                    continue;
                }
                const std::size_t v=f.order[--f.remaining];
                Bits child(words_);
                const Word* adjacent=graph_.row(v);
                for (std::size_t w=0;w<words_;++w) child[w]=f.candidates[w]&adjacent[w];
                erase(f.candidates,v);
                if (nodes_!=std::numeric_limits<std::uint64_t>::max()) ++nodes_;
                if (nodes_%4096U==0) shared_.visits[id_].store(nodes_,std::memory_order_relaxed);
                publish(v);
                if (path_.size()+1U+population(child)<=shared_.best.load(std::memory_order_relaxed)) continue;
                if (shared_.offer(path_,v,child)) continue;
                Frame next=color(std::move(child),live_bytes);
                live_bytes+=next.bytes;
                path_.push_back(v);
                stack_.push_back(std::move(next));
            }
            shared_.visits[id_].store(nodes_,std::memory_order_relaxed);
        }
    };

public:
    explicit Search(unsigned n, bool progress)
        : n_(checked_n(n)), vertices_((std::size_t{1} << n_)-1U),
          words_((vertices_+63U)/64U), edges_(vertices_*words_, 0), progress_(progress) {
        // Also validate n inside the constructor before size arithmetic.
        build_graph();
        seed_construction();
    }


    std::size_t run(unsigned threads=1) {
        if (threads<1 || threads>max_threads) throw std::invalid_argument("threads must be in 1..32");
        Shared shared(threads,best_,witness_);
        Bits all(words_,std::numeric_limits<Word>::max());
        if (vertices_%64U!=0) all.back()=(Word{1}<<(vertices_%64U))-1U;
        shared.tasks.push_back(Task{{},std::move(all)});
        shared.queued.store(1,std::memory_order_relaxed);
        const auto work=[&](unsigned id) {
            try {
                Worker worker(*this,shared,id);
                Task task;
                while (shared.take(task)) {
                    worker.search(task);
                    shared.finish();
                }
            } catch (...) {
                shared.fail(std::current_exception());
            }
        };
        std::vector<std::thread> workers;
        workers.reserve(threads-1U);
        try {
            for (unsigned id=1;id<threads;++id) workers.emplace_back(work,id);
            work(0);
        } catch (...) {
            // In particular, join threads already started if creation fails.
            shared.fail(std::current_exception());
        }
        for (auto& thread:workers) thread.join();
        if (shared.error) std::rethrow_exception(shared.error);
        if (stop_signal.load(std::memory_order_relaxed)!=0) throw Interrupted{};
        best_=shared.best.load(std::memory_order_relaxed);
        witness_=std::move(shared.witness);
        nodes_=shared.total_visits();
        verify_witness(witness_);
        if (witness_.size()!=best_) throw std::logic_error("bound/witness mismatch");
        if (progress_)
            std::cerr<<"n="<<n_<<": "<<best_<<" (optimal), nodes="<<nodes_
                     <<", threads="<<threads<<", seconds="
                     <<std::chrono::duration<double>(Clock::now()-started_).count()<<'\n';
        return best_;
    }

};


unsigned parse_integer(const std::string& text,unsigned maximum,const char* message) {
    if (text.empty()) throw std::invalid_argument(message);
    unsigned value=0;
    for (char c:text) {
        if (c<'0' || c>'9') throw std::invalid_argument(message);
        const auto digit=static_cast<unsigned>(c-'0');
        if (value>maximum/10U || (value==maximum/10U && digit>maximum%10U))
            throw std::invalid_argument(message);
        value=value*10U+digit;
    }
    if (value==0) throw std::invalid_argument(message);
    return value;
}
} // namespace

int main(int argc, char** argv) {
    bool printed = false;
    try {

        const char* usage="usage: ./401861_03 [N] [--threads T] [--progress]; N=1..14, T=1..32";
        if (argc>6) throw std::invalid_argument(usage);
        unsigned limit=9U;
        const unsigned available=std::thread::hardware_concurrency();
        unsigned threads=std::min(8U,available==0 ? 1U : available);
        bool progress=false,have_limit=false,have_threads=false;
        for (int i=1;i<argc;++i) {
            const std::string arg(argv[i]);
            if (arg=="--progress" && !progress) progress=true;
            else if (arg=="--threads" && !have_threads && i+1<argc) {
                threads=parse_integer(argv[++i],max_threads,"threads must be an integer in 1..32");
                have_threads=true;
            } else if (!have_limit) {
                limit=parse_integer(arg,max_n,"N must be an integer in 1..14");
                have_limit=true;
            } else throw std::invalid_argument(usage);
        }
        if (std::signal(SIGINT, signal_handler) == SIG_ERR ||
            std::signal(SIGTERM, signal_handler) == SIG_ERR)
            throw std::runtime_error("cannot install interruption handlers");
        for (unsigned n = 1; n <= limit; ++n) {
            Search search(n, progress);
            const std::size_t value = search.run(threads);
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
        return 128 + stop_signal.load(std::memory_order_relaxed);
    } catch (const std::exception& error) {
        if (printed) std::cout << '\n' << std::flush;
        std::cerr << "error: " << error.what() << '\n';
        return 1;
    }
}
