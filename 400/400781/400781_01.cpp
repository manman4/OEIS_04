#include <algorithm>
#include <array>
#include <cerrno>
#include <charconv>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <limits>
#include <map>
#include <sstream>
#include <stdexcept>
#include <string>
#include <system_error>
#include <vector>
#include <fcntl.h>
#include <sys/file.h>
#include <unistd.h>

using U = std::uint64_t;
struct Small { U sum; std::array<int, 3> x{}; };

U parse_unsigned(const std::string& text) {
    U value = 0;
    const auto parsed = std::from_chars(text.data(), text.data() + text.size(), value);
    if (parsed.ec != std::errc{} || parsed.ptr != text.data() + text.size())
        throw std::runtime_error("invalid unsigned integer: " + text);
    return value;
}

struct FileDescriptor {
    int fd;
    explicit FileDescriptor(int value) : fd(value) {
        if (fd < 0) throw std::system_error(errno, std::generic_category());
    }
    ~FileDescriptor() { ::close(fd); }
    FileDescriptor(const FileDescriptor&) = delete;
    FileDescriptor& operator=(const FileDescriptor&) = delete;
};

// The lock covers read/merge/replace, so concurrent runs cannot lose updates.
// A complete, fsynced temporary file is renamed over the old file atomically.
void save_bfile(const std::string& filename, int n, U value, U total, U maximum) {
    if (filename.empty()) return;
    FileDescriptor lock(::open((filename + ".lock").c_str(), O_CREAT | O_RDWR, 0600));
    while (::flock(lock.fd, LOCK_EX) != 0) {
        if (errno != EINTR) throw std::system_error(errno, std::generic_category());
    }
    struct Entry { U value = 0, total = 0, maximum = 0; bool has_metadata = false; };
    std::map<U, Entry> entries;
    std::map<U, std::pair<U, U>> metadata;
    std::vector<std::string> comments;
    const std::string header = "# A400781: n a(n); max_pairs is the maximum number of disjoint representations.";
    if (std::filesystem::exists(filename)) {
        std::ifstream in(filename);
        if (!in) throw std::runtime_error("cannot read b-file: " + filename);
        std::string line;
        while (std::getline(in, line)) {
            const auto first = line.find_first_not_of(" \t\r");
            if (first == std::string::npos) continue;
            line.erase(0, first);
            if (line.rfind("# n=", 0) == 0) {
                std::istringstream row(line);
                std::string mark, index, count, packing, extra;
                if (!(row >> mark >> index >> count >> packing) || row >> extra ||
                    index.rfind("n=", 0) != 0 || count.rfind("representations=", 0) != 0 ||
                    packing.rfind("max_pairs=", 0) != 0)
                    throw std::runtime_error("invalid b-file metadata");
                const U key = parse_unsigned(index.substr(2));
                const U count_value = parse_unsigned(count.substr(16));
                const U packing_value = parse_unsigned(packing.substr(10));
                if (!key || packing_value < key || count_value < packing_value ||
                    !metadata.emplace(key, std::make_pair(count_value, packing_value)).second)
                    throw std::runtime_error("invalid or duplicate b-file metadata");
            } else if (line[0] == '#') {
                if (line != header) comments.push_back(line);
            } else {
                std::istringstream row(line);
                std::string index, number, extra;
                if (!(row >> index >> number) || row >> extra)
                    throw std::runtime_error("b-file data must have two columns");
                const U key = parse_unsigned(index), number_value = parse_unsigned(number);
                if (!key || !number_value || !entries.emplace(key, Entry{number_value}).second)
                    throw std::runtime_error("invalid or duplicate b-file index");
            }
        }
        if (!in.eof()) throw std::runtime_error("error reading b-file");
    }
    for (const auto& item : metadata) {
        auto it = entries.find(item.first);
        if (it == entries.end()) throw std::runtime_error("b-file metadata has no data row");
        it->second.total = item.second.first;
        it->second.maximum = item.second.second;
        it->second.has_metadata = true;
    }
    auto& entry = entries[static_cast<U>(n)];
    if (entry.value && entry.value != value) throw std::runtime_error("conflicting value already in b-file");
    if (entry.has_metadata && (entry.total != total || entry.maximum != maximum))
        throw std::runtime_error("conflicting representation counts already in b-file");
    entry = Entry{value, total, maximum, true};
    std::ostringstream data;
    data << header << '\n';
    for (const auto& comment : comments) data << comment << '\n';
    for (const auto& item : entries) {
        const auto& result = item.second;
        if (result.has_metadata)
            data << "# n=" << item.first << " representations=" << result.total
                 << " max_pairs=" << result.maximum << '\n';
        data << item.first << ' ' << result.value << '\n';
    }
    const std::string content = data.str();
    std::string temporary = filename + ".tmp.XXXXXX";
    std::vector<char> name(temporary.begin(), temporary.end());
    name.push_back('\0');
    FileDescriptor out(::mkstemp(name.data()));
    temporary = name.data();
    try {
        std::size_t written = 0;
        while (written < content.size()) {
            const auto amount = ::write(out.fd, content.data() + written, content.size() - written);
            if (amount < 0 && errno == EINTR) continue;
            if (amount <= 0) throw std::system_error(errno ? errno : EIO, std::generic_category());
            written += static_cast<std::size_t>(amount);
        }
        if (::fsync(out.fd) != 0 || ::rename(temporary.c_str(), filename.c_str()) != 0)
            throw std::system_error(errno, std::generic_category());
    } catch (...) {
        ::unlink(temporary.c_str());
        throw;
    }
}

class Search {
    int n, m;
    U limit;
    U low = 0;
    bool narrow = false;
    std::vector<U> p, prefix, sums;
    std::vector<std::uint32_t> offsets;
    std::vector<Small> left, right;
    std::vector<std::vector<int>> reps, chosen, best;
    std::vector<bool> used;
    std::string bfile;
    std::size_t pos = 0;

    U enumerate(int start, int k, U s, bool fill) {
        if (start + k - 1 > m) return 0;
        if (s + (prefix[m] - prefix[m-k]) < low) return 0;
        if (k == 1) {
            const auto end = std::upper_bound(p.begin() + start, p.end(), limit - s);
            const auto first = std::lower_bound(p.begin() + start, end, low > s ? low - s : 0);
            start = static_cast<int>(first - p.begin());
            const auto last = static_cast<int>(end - p.begin());
            if (fill) for (int x = start; x < last; ++x) {
                if (narrow) { offsets.push_back(static_cast<std::uint32_t>(s + p[x] - low)); ++pos; }
                else sums[pos++] = s + p[x];
            }
            return static_cast<U>(std::max(0, last - start));
        }
        U count = 0;
        const U tail = prefix[m] - prefix[m-k+1];
        const U need = low > s + tail ? low - s - tail : 0;
        start = static_cast<int>(std::lower_bound(p.begin() + start, p.end(), need) - p.begin());
        for (int x = start; x + k - 1 <= m; ++x) {
            // The next k increasing bases are at least x,...,x+k-1.
            if (prefix[x + k - 1] - prefix[x - 1] > limit - s) break;
            count += enumerate(x + 1, k - 1, s + p[x], fill);
        }
        return count;
    }

    void small(int start, int k, U s, std::array<int, 3> a, int idx,
               std::vector<Small>& out) {
        if (!k) { out.push_back({s, a}); return; }
        for (int x = start; x + k - 1 <= m; ++x) {
            a[idx] = x;
            small(x + 1, k - 1, s + p[x], a, idx + 1, out);
        }
    }

    void build_tables() {
        const int a = n / 2, b = n - a;
        small(1, a, 0, {}, 0, left);
        small(1, b, 0, {}, 0, right);
        auto cmp = [](const Small& x, const Small& y) { return x.sum < y.sum; };
        std::sort(left.begin(), left.end(), cmp);
        std::sort(right.begin(), right.end(), cmp);
    }

    bool select(std::size_t i) {
        if (chosen.size() == static_cast<std::size_t>(n)) return true;
        if (reps.size() - i < static_cast<std::size_t>(n) - chosen.size()) return false;
        for (std::size_t j = i; j < reps.size(); ++j) {
            bool ok = true;
            for (int x : reps[j]) if (used[x]) { ok = false; break; }
            if (!ok) continue;
            for (int x : reps[j]) used[x] = true;
            chosen.push_back(reps[j]);
            if (select(j + 1)) return true;
            chosen.pop_back();
            for (int x : reps[j]) used[x] = false;
        }
        return false;
    }

    void maximize(std::size_t i) {
        if (chosen.size() > best.size()) best = chosen;
        // At most one additional representation can be chosen per remaining row.
        if (chosen.size() + reps.size() - i <= best.size()) return;
        for (std::size_t j = i; j < reps.size(); ++j) {
            if (chosen.size() + reps.size() - j <= best.size()) break;
            bool ok = true;
            for (int x : reps[j]) if (used[x]) { ok = false; break; }
            if (!ok) continue;
            for (int x : reps[j]) used[x] = true;
            chosen.push_back(reps[j]);
            maximize(j + 1);
            chosen.pop_back();
            for (int x : reps[j]) used[x] = false;
        }
    }

    void emit_result(U value, bool minimum_proved) {
        best = chosen;
        chosen.clear();
        std::fill(used.begin(), used.end(), false);
        maximize(0);
        chosen = best;
        if (minimum_proved)
            save_bfile(bfile, n, value, static_cast<U>(reps.size()), static_cast<U>(chosen.size()));
        // Only machine-readable result columns go to stdout.
        std::cout << n << ' ' << value << ' ' << chosen.size() << '\n' << std::flush;
        std::ostringstream detail;
        detail << "result n=" << n << " N=" << value << " representations=" << reps.size()
               << " max_pairs=" << chosen.size() << " minimum_proved=" << minimum_proved << '\n';
        if (minimum_proved && !bfile.empty()) detail << "saved " << bfile << '\n';
        for (const auto& row : chosen) {
            detail << "representation:";
            for (int x : row) detail << ' ' << x;
            detail << '\n';
        }
        std::cerr << detail.str() << std::flush;
    }

    bool check(U target, U expected) {
        if (left.empty()) build_tables();
        reps.clear(); chosen.clear();
        std::fill(used.begin(), used.end(), false);
        const int a = n / 2, b = n - a;
        for (const auto& l : left) {
            if (l.sum >= target) break;
            const U need = target - l.sum;
            auto it = std::lower_bound(right.begin(), right.end(), need,
                [](const Small& x, U y) { return x.sum < y; });
            for (; it != right.end() && it->sum == need; ++it) {
                // A representation has one unique split after its a-th base.
                if (a && l.x[a - 1] >= it->x[0]) continue;
                std::vector<int> r(l.x.begin(), l.x.begin() + a);
                r.insert(r.end(), it->x.begin(), it->x.begin() + b);
                reps.push_back(r);
            }
        }
        if (expected && reps.size() != expected) throw std::runtime_error("representation count mismatch");
        return select(0);
    }

public:
    Search(int exponent, int maxbase, std::string output_file)
        : n(exponent), m(maxbase), p(m+1), prefix(m+1), used(m+1), bfile(std::move(output_file)) {
        if (n < 1 || n > 6 || m < n || m > 10000) throw std::runtime_error("require 1<=n<=6 and n<=M<=10000");
        for (int x = 1; x <= m; ++x) {
            U v = 1;
            for (int j = 0; j < n; ++j) {
                if (v > std::numeric_limits<U>::max() / static_cast<U>(x)) throw std::runtime_error("power overflow");
                v *= static_cast<U>(x);
            }
            p[x] = v;
            if (prefix[x-1] > std::numeric_limits<U>::max() - v) throw std::runtime_error("prefix overflow");
            prefix[x] = prefix[x-1] + v;
        }
        limit = p[m];
    }

    bool target(U value) {
        const bool found = check(value, 0);
        std::cerr << (found ? "upper_bound " : "rejected ") << n << ' ' << value << " representations=" << reps.size() << '\n';
        if (found) emit_result(value, false);
        return found;
    }

    void inspect(U value) {
        if (!value || value > limit) throw std::runtime_error("inspect requires 1<=value<=M^n");
        check(value, 0);
        emit_result(value, false);
    }

    static void radix_sort(std::vector<std::uint32_t>& values) {
        std::vector<std::uint32_t> buffer(values.size());
        std::vector<std::size_t> positions(65536);
        for (unsigned shift : {0U, 16U}) {
            std::fill(positions.begin(), positions.end(), 0);
            for (auto v : values) ++positions[(v >> shift) & 65535U];
            std::size_t offset = 0;
            for (auto& count : positions) {
                const auto next = offset + count;
                count = offset;
                offset = next;
            }
            for (auto v : values) buffer[positions[(v >> shift) & 65535U]++] = v;
            values.swap(buffer);
        }
    }

    void chunks(U maximum, U width, U first = 0) {
        if (maximum > limit || !width || width > (U{1} << 32)) throw std::runtime_error("require maximum<=M^n and 1<=width<=2^32");
        if (first > maximum) throw std::runtime_error("require first<=maximum");
        const auto begin = std::chrono::steady_clock::now();
        narrow = true;
        U total = 0, candidates = 0;
        std::vector<U> hist(1, 0);
        for (low = first; low <= maximum;) {
            limit = std::min(maximum, low + width - 1);
            offsets.clear();
            pos = 0;
            const U count = enumerate(1, n, 0, true);
            if (pos != offsets.size() || pos != count) throw std::runtime_error("chunk size mismatch");
            total += count;
            radix_sort(offsets);
            for (std::size_t i = 0; i < offsets.size();) {
                std::size_t j = i + 1;
                while (j < offsets.size() && offsets[j] == offsets[i]) ++j;
                const auto ways = j-i;
                if (hist.size() <= ways) hist.resize(ways+1);
                ++hist[ways];
                if (ways >= static_cast<std::size_t>(n)) {
                    ++candidates;
                    if (check(low + offsets[i], ways)) {
                        emit_result(low + offsets[i], first == 0);
                        std::cerr << (first == 0 ? "minimum proved" : "interval minimum")
                                  << "; first=" << first << " records=" << total << " candidates_checked=" << candidates << '\n';
                        report(begin, hist);
                        return;
                    }
                }
                i=j;
            }
            std::cerr << "completed [" << low << ',' << limit << "] records=" << count
                      << " total=" << total << " seconds="
                      << std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count() << '\n';
            if (limit == maximum) break;
            low = limit + 1;
        }
        if (first == 0) std::cerr << "lower_bound " << n << ' ' << maximum + 1 << '\n';
        else std::cerr << "excluded " << n << ' ' << first << ' ' << maximum << '\n';
        std::cerr << "complete; records=" << total << " candidates_checked=" << candidates << '\n';
        report(begin, hist);
    }

    void run() {
        auto begin = std::chrono::steady_clock::now();
        const U count = enumerate(1, n, 0, false);
        std::cerr << "n=" << n << " M=" << m << " limit=" << limit << " records=" << count
                  << " bytes=" << count * sizeof(U) << '\n';
        sums.resize(static_cast<std::size_t>(count));
        enumerate(1, n, 0, true);
        if (pos != sums.size()) throw std::runtime_error("enumeration size mismatch");
        std::cerr << "enumerated; sorting\n";
        std::sort(sums.begin(), sums.end());
        std::vector<U> hist(1, 0);
        U candidates = 0;
        for (std::size_t i = 0; i < sums.size();) {
            std::size_t j = i + 1;
            while (j < sums.size() && sums[j] == sums[i]) ++j;
            const auto ways = j - i;
            if (hist.size() <= ways) hist.resize(ways + 1);
            ++hist[ways];
            if (ways >= static_cast<std::size_t>(n)) {
                ++candidates;
                if (check(sums[i], ways)) {
                    emit_result(sums[i], true);
                    std::cerr << "minimum proved through candidate; candidates_checked=" << candidates << '\n';
                    report(begin, hist);
                    return;
                }
            }
            i = j;
        }
        std::cerr << "lower_bound " << n << ' ' << limit + 1 << '\n';
        std::cerr << "complete; candidates_checked=" << candidates << '\n';
        report(begin, hist);
    }

    static void report(std::chrono::steady_clock::time_point begin, const std::vector<U>& hist) {
        std::cerr << "histogram";
        for (std::size_t k = 1; k < hist.size(); ++k) std::cerr << ' ' << k << ':' << hist[k];
        std::cerr << "\nseconds=" << std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count() << '\n';
    }
};

int main(int argc, char** argv) {
    try {
        std::string bfile = "b400781_01.txt";
        std::vector<std::string> args;
        for (int i = 1; i < argc; ++i) {
            const std::string argument = argv[i];
            if (argument == "--no-bfile") bfile.clear();
            else if (argument == "--bfile") {
                if (++i == argc) throw std::runtime_error("--bfile requires a path");
                bfile = argv[i];
                if (bfile.empty()) throw std::runtime_error("empty b-file path");
            } else args.push_back(argument);
        }
        if (args.size() < 2) throw std::runtime_error("usage: 400781_01 n M [--chunks maximum [width] | --range first maximum [width] | --inspect value | --targets file] [--bfile path | --no-bfile]");
        Search search(std::stoi(args[0]), std::stoi(args[1]), bfile);
        if (args.size() == 4 && args[2] == "--targets") {
            std::ifstream in(args[3]);
            if (!in) throw std::runtime_error("cannot read targets");
            U index, value;
            while (in >> index >> value) if (search.target(value)) break;
        } else if ((args.size() == 4 || args.size() == 5) && args[2] == "--chunks")
            search.chunks(parse_unsigned(args[3]), args.size() == 5 ? parse_unsigned(args[4]) : (U{1}<<32));
        else if ((args.size() == 5 || args.size() == 6) && args[2] == "--range")
            search.chunks(parse_unsigned(args[4]), args.size() == 6 ? parse_unsigned(args[5]) : (U{1}<<32), parse_unsigned(args[3]));
        else if (args.size() == 4 && args[2] == "--inspect") search.inspect(parse_unsigned(args[3]));
        else if (args.size() == 2) search.run();
        else throw std::runtime_error("invalid search arguments");
    } catch (const std::exception& e) { std::cerr << e.what() << '\n'; return 1; }
}
