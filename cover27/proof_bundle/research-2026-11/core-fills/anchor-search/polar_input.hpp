#ifndef COVER27_POLAR_INPUT_HPP
#define COVER27_POLAR_INPUT_HPP

#include <array>
#include <cstdint>
#include <fstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace polar27 {
using Int=std::int64_t;
#ifndef COVER27_DISKS
#define COVER27_DISKS 27
#endif
#ifndef COVER27_BOUNDARY
#define COVER27_BOUNDARY 14
#endif
constexpr int N=COVER27_DISKS, B=COVER27_BOUNDARY;
struct Bin { Int rlo,rhi; std::vector<Int> arcs; };
struct Ring { Int radius; int samples; };
struct Spec { int family,fixed,ring; Int anchor; };
struct Cut { std::vector<std::pair<int,int>> terms; Int required=0; };
struct RadialCount { int first,last,needed; Int max_norm; };

struct Input {
    Int turn=0,scale=0,radius=0;
    int angular=0;
    std::vector<Ring> rings;
    std::vector<std::vector<Bin>> families;
    std::array<Spec,N> roles{};
    std::vector<Cut> cuts;
    std::vector<RadialCount> counts;
    Int expanded_radius=0;
    int core_ring=-1,min_core=-1,exact_core=0;
    Int core_angle_lo=0,core_angle_hi=0;
    std::vector<int> core_order;

    explicit Input(const char *path) {
        std::ifstream in(path);
        std::string tag;
        int ns=0,nf=0,nc=0;
        in>>tag>>turn>>scale>>radius>>angular>>ns>>nf>>nc;
        if(!in||tag!="COVER27-POLAR-1"||turn<2||turn%2||scale<1||radius<1||
           angular<2||ns<1||nf<1||nc<1) throw std::runtime_error("bad input header");
        rings.resize(ns);
        for(auto &s:rings){
            in>>s.radius>>s.samples;
            if(!in||s.radius<1||s.radius>scale||s.samples<0||(s.samples&&turn%s.samples))
                throw std::runtime_error("bad ring");
        }
        if(rings.back().radius!=scale)throw std::runtime_error("missing unit boundary");
        families.resize(nf);
        for(auto &bins:families){
            int m=0; in>>m;
            if(!in||m<1)throw std::runtime_error("bad bin count");
            bins.resize(m);
            for(auto &bin:bins){
                in>>bin.rlo>>bin.rhi;
                if(!in||bin.rlo<0||bin.rlo>bin.rhi||bin.rhi>scale)
                    throw std::runtime_error("bad radial bin");
                bin.arcs.resize(ns);
                for(Int &a:bin.arcs){
                    in>>a;
                    if(!in||a>turn/2||a< -2*turn)throw std::runtime_error("bad angle bound");
                }
            }
        }
        for(auto &role:roles){
            in>>role.family>>role.fixed>>role.ring>>role.anchor;
            if(!in||role.family<0||role.family>=nf||role.fixed<0||role.fixed>1||
               role.ring< -1||role.ring>=ns||role.anchor<0||role.anchor>=turn)
                throw std::runtime_error("bad role");
        }
        cuts.resize(nc);
        for(auto &cut:cuts){
            int m=0;in>>m;
            if(!in||m<1)throw std::runtime_error("bad cut");
            cut.terms.resize(m);
            Int total=0;
            for(auto &[ring,weight]:cut.terms){
                in>>ring>>weight;
                if(!in||ring<0||ring>=ns||weight<=0)throw std::runtime_error("bad cut term");
                total+=weight;
            }
            if(total>10'000'000)throw std::runtime_error("oversized cut");
            cut.required=total*(turn/2);
        }
        int count=0;
        in>>count>>expanded_radius;
        if(!in||count<1||expanded_radius<1||expanded_radius>=scale)
            throw std::runtime_error("bad radial count header");
        counts.resize(count);
        for(auto &c:counts){
            in>>c.first>>c.last>>c.needed>>c.max_norm;
            if(!in||c.first<0||c.first>=c.last||c.last>N||!c.needed||
               c.needed>c.last-c.first||c.needed<c.first-c.last||c.max_norm<1||c.max_norm>scale)
                throw std::runtime_error("bad radial count");
        }
        int order_size=0;
        in>>core_ring>>min_core>>core_angle_lo>>core_angle_hi>>order_size>>exact_core;
        if(!in||core_ring< -1||core_ring>=ns-1||(N!=27&&core_ring>=0)||
           exact_core<0||exact_core>N-B||((core_ring<0)!=(exact_core==0))||
           (min_core!= -1&&min_core!=23)||min_core>=N||
           (order_size!=0&&order_size!=10)||(min_core<0)!=(order_size==0)||
           (min_core>=0&&(core_ring<0||exact_core!=10||core_angle_lo<0||core_angle_hi<core_angle_lo||
                          core_angle_hi>=3*turn/2)))
            throw std::runtime_error("bad core data");
        core_order.resize(order_size);
        std::array<bool,10> used{};
        for(int &k:core_order){
            in>>k;
            if(!in||k<14||k>=24||used[k-14])throw std::runtime_error("bad core order");
            used[k-14]=true;
        }
    }
};
}
#endif
