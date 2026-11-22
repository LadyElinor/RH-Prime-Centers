// Independent, floating-point discovery pass. The integer verifier certifies its candidates.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <vector>

struct WindowScan {
    int64_t left, right;
    long double minimum=1e90L, scaled_minimum=1e90L;
    long double raw_x=0, normalized_x=0;
    int64_t points=0;

    void examine(long double x, long double twice_deficit) {
        long double ratio=twice_deficit/std::sqrt(x);
        if (ratio<scaled_minimum) {
            scaled_minimum=ratio;
            normalized_x=x;
        }
        if (twice_deficit/2<minimum) {
            minimum=twice_deficit/2;
            raw_x=x;
        }
    }
};

int main() {
    std::array<WindowScan,6> windows={{{400,800},{256,1024},{20736,248832},
        {331776,7962624},{8503056,459165024},{256,459165024}}};
    int limit=int(windows.back().right);
    std::vector<bool> composite(limit/2+1);
    for(int64_t p=3;p*p<=limit;p+=2) {
        if(composite[p/2]) continue;
        for(int64_t j=p*p;j<=limit;j+=2*p) composite[j/2]=true;
    }
    std::vector<int> primes={2};
    for(int n=3;n<=limit;n+=2) if(!composite[n/2]) primes.push_back(n);
    std::vector<long double> ratios;
    ratios.reserve(primes.size());
    for(int p:primes) ratios.push_back(std::log(static_cast<long double>(p))/p);

    std::vector<int64_t> edges;
    for(auto& w:windows) { edges.push_back(w.left); edges.push_back(w.right); }
    std::sort(edges.begin(),edges.end());
    edges.erase(std::unique(edges.begin(),edges.end()),edges.end());
    edges.push_back(limit+1LL);
    long double value=0, slope=std::log(2.0L);
    int64_t previous=0;
    std::array<size_t,3> indices{};
    size_t edge=0;
    while(previous<limit) {
        std::array<int64_t,3> next;
        int64_t x=edges[edge];
        for(int j=0;j<3;++j) {
            next[j]=indices[j]<primes.size() ? (int64_t(1)<<j)*primes[indices[j]] : limit+1LL;
            x=std::min(x,next[j]);
        }
        long double end_value=value+(x-previous)*slope;
        for(auto& w:windows) {
            if(x<w.left || x>w.right) continue;
            w.examine(x,end_value);
            if(previous>=w.left && slope>0) {
                long double stationary=value/slope-previous;
                if(previous<stationary && stationary<x)
                    w.examine(stationary,value+(stationary-previous)*slope);
            }
            if(x==w.left || x==w.right || x==next[1]) ++w.points;
        }
        if(edges[edge]==x) ++edge;
        constexpr int jump[3]={-2,3,-1};
        for(int j=0;j<3;++j) {
            if(x!=next[j]) continue;
            slope+=jump[j]*ratios[indices[j]++];
        }
        previous=x;
        value=end_value;
    }
    for(auto& w:windows)
        std::printf("%lld %lld %lld raw %.12Lf x %.12Lf scaled %.12Lf x %.12Lf\n",
                    (long long)w.left,(long long)w.right,(long long)w.points,
                    w.minimum,w.raw_x,w.scaled_minimum,w.normalized_x);
}
