// A401619 / Erdos Problem 771. Exact integer search; no external libraries.
// Build: c++ -O3 -std=c++17 -DNDEBUG 401619_01.cpp -o 401619_01
// POSIX file locks and atomic checkpoint replacement (macOS/Linux).
#include <algorithm>
#include <cerrno>
#include <chrono>
#include <csignal>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
#include <fcntl.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>

namespace fs = std::filesystem;
using Clock = std::chrono::steady_clock;
using Bits = std::vector<std::uint64_t>;
constexpr int MAX_N = 1000; // Engineering limit, not a claim of practical runtime.
constexpr const char* MAGIC = "A401619_EXACT_LOW_HIGH_V1";
volatile std::sig_atomic_t interrupted = 0;
extern "C" void on_signal(int) { interrupted = 1; }
struct Stopped { int code; };

int integer(const std::string& s, int low, int high) {
    if (s.empty() || s.find_first_not_of("0123456789") != std::string::npos)
        throw std::runtime_error("Expected an unsigned decimal integer: " + s);
    std::uint64_t value = 0;
    for (char c : s) {
        value = value * 10 + static_cast<unsigned>(c - '0');
        if (value > static_cast<std::uint64_t>(high))
            throw std::runtime_error("Integer exceeds supported limit: " + s);
    }
    if (value < static_cast<std::uint64_t>(low))
        throw std::runtime_error("Integer below supported minimum: " + s);
    return static_cast<int>(value);
}
int triangle(int n) { return n * (n + 1) / 2; }
bool get(const Bits& b, int i) {
    return ((b[static_cast<std::size_t>(i / 64)] >> (i % 64)) & 1U) != 0;
}
void trim(Bits& b, int limit) {
    if (limit % 64 != 63)
        b.back() &= (std::uint64_t{1} << (limit % 64 + 1)) - 1;
}
// Exactly R union (R+x), truncated to sums <= limit. Source and result differ.
Bits shifted_union(const Bits& b, int x, int limit) {
    Bits result = b;
    if (x > limit) return result;
    const std::size_t words = static_cast<std::size_t>(x / 64);
    const unsigned shift = static_cast<unsigned>(x % 64);
    for (std::size_t j = b.size(); j-- > words;) {
        std::uint64_t value = b[j - words] << shift;
        if (shift != 0 && j > words)
            value |= b[j - words - 1] >> (64 - shift);
        result[j] |= value;
    }
    trim(result, limit);
    return result;
}
Bits subset_sums(const std::vector<int>& items, int limit) {
    Bits sums(static_cast<std::size_t>(limit / 64 + 1));
    sums[0] = 1;
    for (int x : items) sums = shifted_union(sums, x, limit);
    return sums;
}

struct Control {
    Clock::time_point start = Clock::now(), report = start;
    double seconds = 0, progress = 5;
    std::uint64_t nodes = 0, calls = 0;
    int n = 0, target = 0;
    bool quiet = false;
    double elapsed() const { return std::chrono::duration<double>(Clock::now()-start).count(); }
    void check(bool force = false) {
        if (!force && (nodes & 4095U) != 0) return;
        if (interrupted) throw Stopped{130};
        const auto now = Clock::now();
        if (seconds > 0 && std::chrono::duration<double>(now-start).count() >= seconds)
            throw Stopped{124};
        if (!quiet && progress > 0 && std::chrono::duration<double>(now-report).count() >= progress) {
            std::cerr << "n=" << n << ", m=" << target << ", nodes=" << nodes
                      << ", target_checks=" << calls << '\n';
            report = now;
        }
    }
};

// Decide whether a k-element subset of [1,n] avoids the target sum m.
// Split at m/2. At most one element > m/2 can occur in a sum equal to m.
class Avoider {
    int n_, m_, k_, free_, top_;
    Control& ctl_;
    std::vector<int> chosen_, answer_;
    bool dfs(int first, const Bits& reachable) {
        ++ctl_.nodes;
        ctl_.check();
        std::vector<int> high;
        for (int y = m_/2+1; y <= std::min(n_,m_-1); ++y)
            if (!get(reachable,m_-y)) high.push_back(y);
        const int base = static_cast<int>(chosen_.size()) + free_;
        // All currently eligible high elements may be included together.
        if (base + static_cast<int>(high.size()) >= k_) {
            answer_ = chosen_;
            answer_.insert(answer_.end(),high.begin(),high.end());
            for (int y=m_+1; y<=n_; ++y) answer_.push_back(y);
            answer_.resize(static_cast<std::size_t>(k_));
            return true;
        }
        if (first > top_) return false;
        std::vector<int> pending = high;
        for (int y=first; y<=top_; ++y)
            if (!get(reachable,m_-y)) pending.push_back(y);
        const int upper = base + static_cast<int>(pending.size());
        if (upper < k_) return false;
        // Disjoint incompatible pairs cost at least one omission per pair.
        // A reachable s with s+x+y=m forbids choosing both x and y.
        std::vector<unsigned char> used(pending.size());
        int pairs = 0;
        for (std::size_t i=0; i<pending.size(); ++i) {
            if (used[i]) continue;
            for (std::size_t j=i+1; j<pending.size(); ++j) {
                if (!used[j] && pending[i]+pending[j] <= m_ &&
                    get(reachable,m_-pending[i]-pending[j])) {
                    used[i]=used[j]=1;
                    ++pairs;
                    break;
                }
            }
        }
        if (upper-pairs < k_) return false;
        // Exclude individually forbidden low elements without branching.
        while (first <= top_ && get(reachable,m_-first)) ++first;
        if (first > top_) return false;
        chosen_.push_back(first);
        Bits next = shifted_union(reachable,first,m_);
        if (dfs(first+1,next)) return true;
        chosen_.pop_back();
        return dfs(first+1,reachable);
    }
public:
    Avoider(int n,int m,int k,Control& ctl)
        : n_(n),m_(m),k_(k),free_(std::max(0,n-m)),top_(std::min(n,m/2)),ctl_(ctl) {}
    bool run() {
        ++ctl_.calls;
        ctl_.target=m_;
        ctl_.check(true);
        Bits reachable(static_cast<std::size_t>(m_/64+1));
        reachable[0]=1;
        const bool found = dfs(1,reachable);
        if (found) {
            std::sort(answer_.begin(),answer_.end());
            if (static_cast<int>(answer_.size())!=k_ ||
                std::adjacent_find(answer_.begin(),answer_.end())!=answer_.end() ||
                (!answer_.empty() && (answer_.front()<1 || answer_.back()>n_)) ||
                get(subset_sums(answer_,m_),m_))
                throw std::runtime_error("Internal error: invalid avoiding witness");
        }
        return found;
    }
    const std::vector<int>& answer() const { return answer_; }
};
struct Row { int n, value, upper_witness; };

class Engine {
    int cached_k_ = -1, last_n_ = -1;
    Bits candidates_;
public:
    // Previous exact value r implies a(n) is r or r+1. A witness m certifies
    // that every (r+1)-element subset represents m, hence the upper bound r.
    Row next(int n, int previous, int previous_witness, Control& ctl) {
        const int k=previous+1, H=triangle(k);
        if (cached_k_!=k || last_n_!=n-1) {
            candidates_.assign(static_cast<std::size_t>(H/64+1),~std::uint64_t{0});
            candidates_[0]&=~std::uint64_t{1};
            trim(candidates_,H);
            cached_k_=k;
        }
        ctl.n=n;
        for (int m=1; m<=H; ++m) {
            ctl.check(true);
            if (!get(candidates_,m)) continue;
            Avoider search(n,m,k,ctl);
            if (!search.run()) {
                last_n_=n;
                return Row{n,previous,m};
            }
            // One k-set can eliminate many possible universal sums at once.
            Bits sums=subset_sums(search.answer(),H);
            for (std::size_t j=0; j<candidates_.size(); ++j) candidates_[j]&=sums[j];
        }
        last_n_=n;
        // The previous upper witness remains universal for sets one larger:
        // remove n, if present. Thus an increase cannot exceed one.
        return Row{n,k,previous_witness};
    }
};

std::string btext(const std::vector<Row>& rows) {
    std::ostringstream out;
    for (const Row& r : rows) out<<r.n<<' '<<r.value<<'\n';
    return out.str();
}
std::uint64_t digest(const std::string& s) {
    std::uint64_t h=14695981039346656037ULL;
    for (unsigned char c : s) { h^=c; h*=1099511628211ULL; }
    return h; // Accidental-corruption check; not an authentication mechanism.
}
std::string state_text(const std::vector<Row>& rows) {
    std::ostringstream out;
    out<<MAGIC<<'\n';
    for (const Row& r : rows) out<<r.n<<' '<<r.value<<' '<<r.upper_witness<<'\n';
    const std::string payload=out.str();
    out<<"CHECKSUM "<<std::hex<<std::setw(16)<<std::setfill('0')<<digest(payload)<<'\n';
    return out.str();
}
void regular_or_missing(const fs::path& p) {
    struct stat st{};
    if (lstat(p.c_str(),&st)==0) {
        if (!S_ISREG(st.st_mode) || st.st_nlink!=1)
            throw std::runtime_error("Refusing non-regular, symlink or hard-linked file: "+p.string());
    } else if (errno!=ENOENT) throw std::runtime_error("Cannot inspect file: "+p.string());
}
bool exists_regular(const fs::path& p) {
    regular_or_missing(p);
    struct stat st{};
    return lstat(p.c_str(),&st)==0;
}
std::string read_file(const fs::path& p) {
    regular_or_missing(p);
    std::ifstream in(p,std::ios::binary);
    if (!in) throw std::runtime_error("Cannot read "+p.string());
    in.seekg(0,std::ios::end);
    const auto size=in.tellg();
    if (size<0 || size>4*1024*1024) throw std::runtime_error("Unexpected file size: "+p.string());
    in.seekg(0);
    std::string value(static_cast<std::size_t>(size),'\0');
    if (!value.empty() && !in.read(&value[0],static_cast<std::streamsize>(value.size())))
        throw std::runtime_error("Read failed: "+p.string());
    return value;
}
std::vector<Row> parse_state(const std::string& text) {
    const auto pos=text.rfind("CHECKSUM ");
    if (pos==std::string::npos) throw std::runtime_error("Checkpoint lacks checksum");
    const std::string payload=text.substr(0,pos), footer=text.substr(pos);
    std::ostringstream expected;
    expected<<"CHECKSUM "<<std::hex<<std::setw(16)<<std::setfill('0')<<digest(payload)<<'\n';
    if (footer!=expected.str()) throw std::runtime_error("Checkpoint checksum mismatch");
    std::istringstream input(payload);
    std::string line;
    if (!std::getline(input,line) || line!=MAGIC)
        throw std::runtime_error("Unsupported checkpoint version");
    std::vector<Row> rows;
    int previous=0;
    while (std::getline(input,line)) {
        std::istringstream fields(line);
        std::string ns,vs,ms,extra;
        if (!(fields>>ns>>vs>>ms) || fields>>extra) throw std::runtime_error("Invalid checkpoint row");
        Row r{integer(ns,1,MAX_N),integer(vs,0,MAX_N),integer(ms,1,triangle(MAX_N))};
        if (r.n!=static_cast<int>(rows.size())+1 || r.value>=r.n ||
            r.value<previous || r.value>previous+1 ||
            r.upper_witness>triangle(r.value+1) || r.upper_witness>triangle(r.n) ||
            (r.n==1 && (r.value!=0 || r.upper_witness!=1)))
            throw std::runtime_error("Inconsistent checkpoint row");
        rows.push_back(r);
        previous=r.value;
    }
    if (state_text(rows)!=text) throw std::runtime_error("Non-canonical checkpoint");
    return rows;
}
class Lock {
    int fd_=-1;
public:
    explicit Lock(const fs::path& p) {
        regular_or_missing(p);
        fd_=open(p.c_str(),O_CREAT|O_RDWR|O_NOFOLLOW,0600);
        if (fd_<0) throw std::runtime_error("Cannot open lock "+p.string());
        if (flock(fd_,LOCK_EX|LOCK_NB)!=0) {
            close(fd_); fd_=-1;
            throw std::runtime_error("Another process is using "+p.string());
        }
    }
    ~Lock() { if(fd_>=0) close(fd_); }
    Lock(const Lock&)=delete;
    Lock& operator=(const Lock&)=delete;
};
void atomic_write(const fs::path& destination,const std::string& text) {
    regular_or_missing(destination);
    std::string name=destination.string()+".tmp.XXXXXX";
    std::vector<char> tmp(name.begin(),name.end()); tmp.push_back('\0');
    int fd=mkstemp(tmp.data());
    if(fd<0) throw std::runtime_error("Cannot create temporary output");
    bool renamed=false;
    try {
        std::size_t offset=0;
        while(offset<text.size()) {
            const auto count=write(fd,text.data()+offset,text.size()-offset);
            if(count<0 && errno==EINTR) continue;
            if(count<=0) throw std::runtime_error("Output write failed");
            offset+=static_cast<std::size_t>(count);
        }
        if(fsync(fd)!=0) throw std::runtime_error("Output fsync failed");
        const int close_result=close(fd); fd=-1;
        if(close_result!=0) throw std::runtime_error("Output close failed");
        regular_or_missing(destination);
        if(rename(tmp.data(),destination.c_str())!=0) throw std::runtime_error("Output rename failed");
        renamed=true;
        const fs::path parent=destination.parent_path().empty()?fs::path("."):destination.parent_path();
        const int dirfd=open(parent.c_str(),O_RDONLY|O_DIRECTORY);
        if(dirfd<0) throw std::runtime_error("Cannot open output directory for fsync");
        const int result=fsync(dirfd); close(dirfd);
        if(result!=0) throw std::runtime_error("Directory fsync failed");
    } catch (...) {
        if(fd>=0) close(fd);
        if(!renamed) unlink(tmp.data());
        throw;
    }
}
struct Options {
    int limit=0;
    bool no_files=false,verify=false,self_test=false,quiet=false,query=false;
    int qn=0,qm=0,qk=0;
    double seconds=0,progress=5;
    fs::path directory=".";
};
void help() {
    std::cout<<"Usage: 401619_01 N [--output-dir DIR] [--no-files] [--verify]\n"
             <<"                  [--seconds S] [--progress-seconds S] [--quiet]\n"
             <<"       401619_01 --self-test\n"
             <<"       401619_01 --query N M K [--seconds S]\n"
             <<"N: 1.."<<MAX_N<<" (engineering limit; exponential search may stop much earlier).\n"
             <<"Default files: b401619.txt and 401619_01.state in the output directory.\n"
             <<"Only exact completed terms are saved. Existing state is structurally checked\n"
             <<"with a checksum; --verify additionally recomputes all saved terms.\n"
             <<"--seconds bounds this run; 0 means unlimited. Incomplete term is not saved.\n"
             <<"Stable .lock files remain after exit and must not be removed while in use.\n";
}
double duration_argument(const std::string& s) {
    if(s.empty() || s.find_first_not_of("0123456789.")!=std::string::npos)
        throw std::runtime_error("Invalid time argument");
    std::size_t used=0;
    const double result=std::stod(s,&used);
    if(used!=s.size() || !(result>=0 && result<=31536000))
        throw std::runtime_error("Time must be between 0 and 31536000 seconds");
    return result;
}
Options options(int argc,char** argv) {
    Options o;
    for(int i=1;i<argc;++i) {
        const std::string arg=argv[i];
        auto value=[&]() { if(i+1>=argc) throw std::runtime_error("Missing option argument");return std::string(argv[++i]); };
        if(arg=="--help" || arg=="-h") { help(); std::exit(0); }
        if(arg=="--self-test") o.self_test=true;
        else if(arg=="--query") {
            o.query=true; o.qn=integer(value(),1,MAX_N);
            o.qm=integer(value(),1,triangle(o.qn)); o.qk=integer(value(),0,o.qn);
        } else if(arg=="--no-files") o.no_files=true;
        else if(arg=="--verify") o.verify=true;
        else if(arg=="--quiet") o.quiet=true;
        else if(arg=="--output-dir") o.directory=value();
        else if(arg=="--seconds") o.seconds=duration_argument(value());
        else if(arg=="--progress-seconds") o.progress=duration_argument(value());
        else if(o.limit==0 && arg.size()>0 && arg[0]!='-') o.limit=integer(arg,1,MAX_N);
        else throw std::runtime_error("Unknown or duplicate argument: "+arg);
    }
    if(o.self_test) {
        if(argc!=2) throw std::runtime_error("--self-test must be used alone");
    } else if(o.query) {
        if(o.limit || o.verify || o.no_files || o.directory!=fs::path("."))
            throw std::runtime_error("--query is a separate, file-free mode");
    } else if(o.limit==0) throw std::runtime_error("Specify N or --help");
    if(o.no_files && o.verify) throw std::runtime_error("--verify requires saved files");
    return o;
}

// Independent oracle: enumerate every subset and its subset sums with Boolean
// arrays (no low/high split, pair bound, previous term, or candidate cache).
std::vector<int> direct_best(int n) {
    const int H=triangle(n);
    std::vector<int> best(static_cast<std::size_t>(H+1),0);
    const unsigned end=1U<<static_cast<unsigned>(n);
    for(unsigned mask=0;mask<end;++mask) {
        std::vector<unsigned char> possible(static_cast<std::size_t>(H+1)); possible[0]=1;
        int count=0;
        for(int x=1;x<=n;++x) if(mask&(1U<<static_cast<unsigned>(x-1))) {
            ++count;
            for(int s=H;s>=x;--s) if(possible[static_cast<std::size_t>(s-x)]) possible[static_cast<std::size_t>(s)]=1;
        }
        for(int m=1;m<=H;++m) if(!possible[static_cast<std::size_t>(m)])
            best[static_cast<std::size_t>(m)]=std::max(best[static_cast<std::size_t>(m)],count);
    }
    return best;
}
void self_test() {
    Control ctl; ctl.quiet=true;
    Engine engine; int previous=0,witness=1;
    for(int n=1;n<=12;++n) {
        const auto best=direct_best(n);
        const int expected=*std::min_element(best.begin()+1,best.end());
        const Row row=engine.next(n,previous,witness,ctl);
        if(row.value!=expected || best[static_cast<std::size_t>(row.upper_witness)]!=row.value)
            throw std::runtime_error("Self-test: sequence or upper witness mismatch");
        if(n<=8) for(int m=1;m<=triangle(n);++m) for(int k=0;k<=n;++k) {
            Avoider solver(n,m,k,ctl);
            if(solver.run()!=(best[static_cast<std::size_t>(m)]>=k))
                throw std::runtime_error("Self-test: avoiding-set feasibility mismatch");
        }
        previous=row.value; witness=row.upper_witness;
    }
    // Word boundaries, including shifts 0 mod 64 and limits 63 mod 64.
    for(int H : {63,64,65,127,128,129}) {
        const std::vector<int> selected={1,2,31,32,63,64,65};
        Bits fast=subset_sums(selected,H);
        std::vector<unsigned char> plain(static_cast<std::size_t>(H+1));plain[0]=1;
        for(int x:selected) for(int s=H;s>=x;--s)
            if(plain[static_cast<std::size_t>(s-x)]) plain[static_cast<std::size_t>(s)]=1;
        for(int s=0;s<=H;++s) if(get(fast,s)!=(plain[static_cast<std::size_t>(s)]!=0))
            throw std::runtime_error("Self-test: bitset word-boundary mismatch");
    }
    const std::vector<Row> sample={{1,0,1},{2,1,1},{3,1,3}};
    if(state_text(parse_state(state_text(sample)))!=state_text(sample))
        throw std::runtime_error("Self-test: state roundtrip mismatch");
    std::cout<<"Self-test passed: sequence n=1..12; all (m,k) at n<=8; bitset boundaries; checkpoint roundtrip.\n";
}
int main(int argc,char** argv) {
    try {
        const Options opt=options(argc,argv);
        std::signal(SIGINT,on_signal); std::signal(SIGTERM,on_signal);
        if(opt.self_test) { self_test();return 0; }
        Control ctl;ctl.seconds=opt.seconds;ctl.progress=opt.progress;ctl.quiet=opt.quiet;
        if(opt.query) {
            Avoider solver(opt.qn,opt.qm,opt.qk,ctl);
            if(solver.run()) {
                std::cout<<"AVOID";for(int x:solver.answer())std::cout<<' '<<x;std::cout<<'\n';
            } else std::cout<<"UNAVOIDABLE\n";
            return 0;
        }
        std::vector<Row> rows;
        Engine engine;
        auto compute = [&](bool files,const fs::path& state,const fs::path& bfile) {
            if(opt.verify && !rows.empty()) {
                Engine verifier; int prior=0,w=1;
                std::cerr<<"Recomputing saved n=1.."<<rows.size()<<"...\n";
                for(const Row& saved:rows) {
                    const Row actual=verifier.next(saved.n,prior,w,ctl);
                    if(actual.value!=saved.value) throw std::runtime_error("Saved value fails recomputation");
                    // The saved upper witness is not assumed correct merely
                    // because another witness proves the same value.
                    Avoider upper(saved.n,saved.upper_witness,saved.value+1,ctl);
                    if(upper.run()) throw std::runtime_error("Saved upper witness is false");
                    prior=actual.value;w=actual.upper_witness;
                }
                std::cerr<<"Saved values and upper witnesses verified.\n";
            }
            if(files) {
                // Recover only an absent or exact, whole-row prefix of b-file.
                const std::string expected=btext(rows);
                if(exists_regular(bfile)) {
                    const std::string old=read_file(bfile);
                    if((!old.empty() && old.back()!='\n') || expected.compare(0,old.size(),old)!=0)
                        throw std::runtime_error("b-file disagrees with checkpoint; leaving it untouched");
                    if(old!=expected) atomic_write(bfile,expected);
                } else if(!rows.empty()) atomic_write(bfile,expected);
            }
            for(const Row& r:rows) if(r.n<=opt.limit) std::cout<<r.n<<' '<<r.value<<'\n';
            std::cout.flush();
            for(int n=static_cast<int>(rows.size())+1;n<=opt.limit;++n) {
                ctl.check(true);
                const auto begun=Clock::now();const auto nodes=ctl.nodes,calls=ctl.calls;
                const int prior=rows.empty()?0:rows.back().value;
                const int w=rows.empty()?1:rows.back().upper_witness;
                const Row row=engine.next(n,prior,w,ctl);
                std::vector<Row> next=rows;next.push_back(row);
                // Checkpoint is authoritative; b-file is its recoverable view.
                if(files) { atomic_write(state,state_text(next));atomic_write(bfile,btext(next)); }
                rows.swap(next);
                std::cout<<row.n<<' '<<row.value<<'\n'<<std::flush;
                if(!opt.quiet) std::cerr<<"n="<<n<<": "<<row.value<<" (exact), upper_m="<<row.upper_witness
                    <<", nodes="<<ctl.nodes-nodes<<", target_checks="<<ctl.calls-calls
                    <<", seconds="<<std::fixed<<std::setprecision(6)
                    <<std::chrono::duration<double>(Clock::now()-begun).count()<<'\n';
            }
        };
        if(opt.no_files) compute(false,{},{});
        else {
            const fs::path dir=fs::canonical(opt.directory);
            if(!fs::is_directory(dir)) throw std::runtime_error("Output directory does not exist");
            const fs::path state=dir/"401619_01.state",bfile=dir/"b401619.txt";
            // Lock both shared resources before reading either of them.
            Lock state_lock(state.string()+".lock"),output_lock(bfile.string()+".lock");
            if(exists_regular(state)) rows=parse_state(read_file(state));
            else if(exists_regular(bfile) && !read_file(bfile).empty())
                throw std::runtime_error("Nonempty b-file without checkpoint; refusing to overwrite/import it");
            compute(true,state,bfile);
        }
        return 0;
    } catch(const Stopped& stop) {
        std::cerr<<"Stopped; incomplete term was not saved. Resume with the same output directory.\n";
        return stop.code;
    } catch(const std::exception& error) {
        std::cerr<<"Error: "<<error.what()<<'\n';return 1;
    }
}
