// Verify fixed dyadic prime windows with outward-rounded integer arithmetic.
// Build and run via run.py, which constructs the small certified log table.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>
#include <gmpxx.h>

using I = __int128_t;
using U = __uint128_t;
using Word = uint64_t;
using Pos = uint32_t;
constexpr Word scale_log = Word(1) << 57;
constexpr I ratio_lift = I(1) << 23; // All final values are in units of 2^-80.
constexpr I scale = I(1) << 80;
constexpr Word log_width = 256;
constexpr Word decimal_scale = 10000000;
constexpr Pos xmax = 459165024;

struct Bounds { I lo, hi; };

void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(message);
}
std::string integer_text(I x) {
    if (x < 0) return "-" + integer_text(-x);
    std::string result;
    do { result.push_back('0' + int(x % 10)); x /= 10; } while (x);
    std::reverse(result.begin(),result.end());
    return result;
}
mpz_class big(I x) { return mpz_class(integer_text(x)); }

struct Anchors {
    Word log2;
    std::array<Word,4096> entries{};
    explicit Anchors(const char* path) {
        std::ifstream file(path);
        require(bool(file >> log2), "missing log(2) anchor");
        for (Word& n : entries) require(bool(file >> n), "missing log anchor");
    }
    Word lower_log(Pos p) const {
        int e = 31 - __builtin_clz(p);
        Word power_two = Word(1) << e;
        Word scaled_p = Word(p) * 4096;
        Word h = scaled_p / power_two;
        Word d = h * power_two;
        Word n = scaled_p - d;
        // log(p) = e*log(2) + log(h/4096) + log(1+n/d).
        // n/d < 1/4096. Alternating partial sums of orders 3 and 4
        // enclose the residual; every power and every division is enclosed.
        Word lo = scale_log, hi = scale_log;
        I lower = I(e)*log2 + entries[h-4096];
        I upper = lower + e + 1;
        for (Word j=1; j<=4; ++j) {
            lo = Word(U(lo)*n/d);
            hi = Word((U(hi)*n+d-1)/d);
            if (j%2) {
                lower += lo/j;
                upper += (hi+j-1)/j;
            } else {
                lower -= (hi+j-1)/j;
                if (j<4) upper -= lo/j;
            }
        }
        require(lower>0 && upper>=lower && upper-lower<=log_width, "log enclosure failed");
        return Word(lower);
    }
};

std::vector<Pos> sieve(Pos limit) {
    // Segmented integer sieve, independent of the exploratory odd-only sieve.
    Pos root = Pos(std::sqrt(limit));
    while ((Word(root)+1)*(root+1)<=limit) ++root;
    std::vector<bool> base(root+1, true);
    std::vector<Pos> small;
    for (Pos i=2; i<=root; ++i) {
        if (!base[i]) continue;
        small.push_back(i);
        for (Word j=Word(i)*i; j<=root; j+=i) base[j]=false;
    }
    constexpr Pos block = 1<<19;
    std::vector<Pos> result;
    for (Word left=2; left<=limit; left+=block) {
        Word right = std::min<Word>(limit+1ULL,left+block);
        std::vector<uint8_t> prime(right-left,1);
        for (Word p:small) {
            if (p*p>=right) break;
            Word first=std::max(p*p, ((left+p-1)/p)*p);
            for (Word j=first;j<right;j+=p) prime[j-left]=0;
        }
        for (Word j=left;j<right;++j) if(prime[j-left]) result.push_back(Pos(j));
    }
    return result;
}

struct Prefix {
    size_t count=0;
    I logs=0, ratios=0, ratio_error=0;
    void add(Pos p, Word log_floor) {
        I lo=I(log_floor)*ratio_lift;
        I t=lo/p;
        logs+=log_floor;
        ratios+=t;
        ratio_error+=(lo+log_width*ratio_lift+p-1)/p-t;
        ++count;
    }
};

struct Line { Bounds slope, intercept; };

Line interval_line(const std::array<Prefix,3>& prefix, Word log2) {
    // A=(x/4,x/2], B=(x/2,x]. The line is 2F(x)=m*x+b, F(x)=D(x/4).
    auto& all=prefix[0]; auto& half=prefix[1]; auto& quarter=prefix[2];
    I na=half.count-quarter.count, nb=all.count-half.count;
    I la=half.logs-quarter.logs, lb=all.logs-half.logs;
    I ta=half.ratios-quarter.ratios, tb=all.ratios-half.ratios;
    I ea=half.ratio_error-quarter.ratio_error, eb=all.ratio_error-half.ratio_error;
    I m=I(log2)*ratio_lift+ta-2*tb;
    I b=(-4*la+2*lb)*ratio_lift;
    return {{m-2*eb,m+ratio_lift+ea},
            {b-4*na*log_width*ratio_lift,b+2*nb*log_width*ratio_lift}};
}
Bounds value(const Line& line, Pos x) {
    return {line.slope.lo*x+line.intercept.lo,line.slope.hi*x+line.intercept.hi};
}
Bounds direct_sum(Pos x, Word log2, const std::vector<Pos>& primes, const std::vector<Word>& logs) {
    Bounds result{I(x)*log2*ratio_lift,I(x)*(log2+1)*ratio_lift};
    size_t i=std::upper_bound(primes.begin(),primes.end(),x/4)-primes.begin();
    for (; i<primes.size() && primes[i]<=x; ++i) {
        Pos q=primes[i];
        Word numerator=2ULL*q<=x ? 4ULL*q-x : 2ULL*x-2ULL*q;
        I lower=I(numerator)*logs[i]*ratio_lift;
        I upper=I(numerator)*(logs[i]+log_width)*ratio_lift;
        result.lo-=(upper+q-1)/q;
        result.hi-=lower/q;
    }
    return result;
}

Word sqrt_ceiling(Pos x) {
    // Integer certification of ceil(2^20*sqrt(x)); hardware sqrt only seeds the search.
    Word seed=Word(std::sqrt(double(x))*1048576);
    U target=U(x)<<40;
    while(U(seed)*seed<target) ++seed;
    while(seed && U(seed-1)*(seed-1)>=target) --seed;
    return seed;
}

struct Window {
    Pos left, right, witness;
    Word threshold; // floor of the exploratory normalized minimum * 10^7
    size_t count=0, pieces=0, exact_comparisons=0;
    Bounds normalized_value{}, raw_best{};
    Pos raw_x=0;
    I runner_lower=I(1)<<124;
    mpz_class witness_upper_sq;

    Window(Pos l,Pos r,Pos w,Word h):left(l),right(r),witness(w),threshold(h) {}
    void initialize(Word log2,const std::vector<Pos>& primes,const std::vector<Word>& logs) {
        require(left<witness && witness<right, "witness must be internal in this study");
        normalized_value=direct_sum(witness,log2,primes,logs);
        mpz_class d=decimal_scale, s=big(scale), hi=big(normalized_value.hi);
        mpz_class lo=big(normalized_value.lo), h=threshold;
        witness_upper_sq=hi*hi;
        require(lo>0 && d*d*lo*lo>h*h*s*s*witness &&
                d*d*hi*hi<(h+1)*(h+1)*s*s*witness, "witness outside claimed decimal bin");
    }
    void raw_candidate(Pos x, Bounds v) {
        ++count;
        if(!raw_x || v.lo<raw_best.lo) {
            if(raw_x) runner_lower=raw_best.lo;
            raw_x=x; raw_best=v;
        } else runner_lower=std::min(runner_lower,v.lo);
    }
    void normalized_piece(Pos u,Pos v,const Line& line,Bounds start,Bounds end,Word root_ceil) {
        ++pieces;
        require(start.lo>0 && end.lo>0, "positivity failed");
        if(v==witness || u==witness) {
            // Derivative of (m*x+b)/sqrt(x) has the sign of m*x-b.
            if(v==witness)
                require(std::max(line.slope.hi*u,line.slope.hi*v)<line.intercept.lo,
                        "left witness segment not strictly decreasing");
            else
                require(std::min(line.slope.lo*u,line.slope.lo*v)>line.intercept.hi,
                        "right witness segment not strictly increasing");
            return;
        }
        I small=std::min(start.lo,end.lo) >> 48; // downward to 2^-32 units
        if(small*decimal_scale>I(threshold+1)*root_ceil*(I(1)<<12)) return;
        ++exact_comparisons;
        // Compare the lower affine bound with the direct upper bound at the witness.
        // Test the ends, and any interior minimum at b/m. Big integers avoid overflow.
        auto endpoint_above=[&](Pos x,I value_lo){
            mpz_class a=big(value_lo);
            return a*a*witness>witness_upper_sq*x;
        };
        require(endpoint_above(u,start.lo) && endpoint_above(v,end.lo),
                "another endpoint overlaps the normalized witness");
        I m=line.slope.lo, b=line.intercept.lo;
        if(m>0 && m*u<b && b<m*v)
            require(4*big(m)*big(b)*witness>witness_upper_sq,
                    "interior stationary point overlaps the witness");
    }
};

// Visit every affine piece after cutting at the supplied study endpoints.
template<class Visitor>
void visit_pieces(std::vector<Pos> edges, Word log2, const std::vector<Pos>& primes,
                  const std::vector<Word>& logs, Visitor visit) {
    std::sort(edges.begin(),edges.end());
    edges.erase(std::unique(edges.begin(),edges.end()),edges.end());
    edges.push_back(xmax+1);
    std::array<Prefix,3> prefix{};
    Pos prev=0;
    size_t edge=0;
    while(prev<xmax) {
        std::array<Pos,3> next;
        Pos x=edges[edge];
        for(int j=0;j<3;++j) {
            size_t i=prefix[j].count;
            next[j]=i<primes.size()?primes[i]*(1U<<j):xmax+1;
            x=std::min(x,next[j]);
        }
        visit(prev,x,next[1]==x,interval_line(prefix,log2));
        for(int j=0;j<3;++j) {
            if(next[j]!=x) continue;
            size_t i=prefix[j].count;
            prefix[j].add(primes[i],logs[i]);
        }
        if(edges[edge]==x) ++edge;
        prev=x;
    }
}

#include "checkpoint_loss.hpp"

int main(int argc,char** argv) try {
    bool loss_only = argc==3 && std::string(argv[2])=="--loss";
    require(argc==2 || loss_only,"usage: verify anchors.txt [--loss]");
    Anchors anchors(argv[1]);
    auto primes=sieve(xmax);
    std::vector<Word> logs;
    logs.reserve(primes.size());
    for(Pos p:primes) logs.push_back(anchors.lower_log(p));
    if (loss_only) {
        certify_checkpoint_losses(anchors.log2,primes,logs);
        return 0;
    }
    std::vector<Window> runs={{400,800,482,5695770},{256,1024,866,5487440},
        {20736,248832,44134,4330185},{331776,7962624,638774,3746873},
        {8503056,xmax,135711766,3890582},{256,xmax,638774,3746873}};
    std::vector<Pos> edges;
    for(auto& w:runs) {
        w.initialize(anchors.log2,primes,logs);
        edges.push_back(w.left); edges.push_back(w.right);
    }
    visit_pieces(edges,anchors.log2,primes,logs,[&](Pos prev,Pos x,bool center,const Line& line) {
        auto start=value(line,prev),end=value(line,x);
        const Word root=sqrt_ceiling(x);
        for(auto& w:runs) {
            if(x<w.left || x>w.right) continue;
            if(x==w.left || x==w.right || center) w.raw_candidate(x,end);
            if(prev>=w.left) w.normalized_piece(prev,x,line,start,end,root);
        }
    });
    std::cout<<"left,right,centers_and_endpoints,affine_pieces,raw_x,raw_lo,raw_hi,norm_x,norm_vlo,norm_vhi,exact_fallbacks\n";
    for(auto& w:runs) {
        require(w.raw_best.hi<w.runner_lower && w.pieces>0, "raw minimizer unresolved");
        auto raw=direct_sum(w.raw_x,anchors.log2,primes,logs);
        raw.lo=std::max(raw.lo,w.raw_best.lo);
        raw.hi=std::min(raw.hi,w.raw_best.hi);
        require(raw.lo>0 && raw.lo<=raw.hi, "raw witness disagrees with sweep");
        std::cout<<w.left<<','<<w.right<<','<<w.count<<','<<w.pieces<<','<<w.raw_x<<','
                 <<integer_text(raw.lo)<<','<<integer_text(raw.hi)<<','<<w.witness<<','
                 <<integer_text(w.normalized_value.lo)<<','<<integer_text(w.normalized_value.hi)
                 <<','<<w.exact_comparisons<<'\n';
    }
    return 0;
} catch(const std::exception& e) {
    std::cerr<<e.what()<<'\n'; return 1;
}
