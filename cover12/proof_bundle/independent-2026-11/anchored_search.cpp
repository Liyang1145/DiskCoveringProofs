#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <numeric>
#include <string>
#include <utility>
#include <vector>
#include "refine_geometry.hpp"

namespace circle {

using I = std::int64_t;
using Word = std::uint64_t;
using Mask = std::vector<Word>;
constexpr I turn = 1008000000;
constexpr I scale = 1000000000;
constexpr I r_units = 361102964;
constexpr int n_disks = 12;
constexpr I radial_start = scale - r_units;
constexpr I radial_end = 933000000;
constexpr I dead = -2*turn;
constexpr int n_caps = 11;
using Clock = std::chrono::steady_clock;

struct Ring {
    I radius;
    int samples;
    I phase;
};

struct ProblemData {
    int m, n_angles, n_radials, slot, redundant;
    int start_bin=0, stop_bin=0;
    std::vector<Ring> rings;
    std::vector<int> cap_rings;
    std::map<std::array<I, 3>, I> exact;
    std::map<std::pair<I,I>,refine::Box> directions;
    std::map<int,std::array<I,4>> good;
    ProblemData(int m_, int a, int r, int sl, int red)
        : m(m_), n_angles(a), n_radials(r), slot(sl), redundant(red) {
        for (I s : {278, 295, 313, 326, 340, 354, 365, 380, 394, 408, 421, 437,
                   453, 470, 488, 506, 525, 545, 565, 586, 607, 627, 642, 665,
                   690, 720, 760, 810, 880, 1000}) {
            const int n = s == 1000 ? n_angles : n_angles/2;
            if (n <= 0 || turn % n) std::abort();
            rings.push_back({s*1000000, n, 0});
        }
        for (I s : {295, 340, 365, 394, 408, 437, 488, 545, 607, 642, 1000}) {
            auto it = std::find_if(rings.begin(), rings.end(), [&](Ring row) {
                return row.radius == s*1000000;
            });
            cap_rings.push_back(int(it-rings.begin()));
        }
    }
    I arc(I s, I lo, I hi) const {
        return exact.at({s,lo,hi});
    }
    std::vector<std::pair<I,I>> radial_bins(int kind) const {
        I low = 0, high = radial_start;
        int n = 2*n_radials;
        if (kind == 0) {
            low = radial_start;
            high = m == 9 ? 778070000 : 2*r_units;
            n = std::max(5,n_radials/2);
        } else if (kind == 1) {
            low = radial_start;
            high = radial_end;
            n = n_radials;
        }
        std::vector<std::pair<I,I>> b;
        for (int j=0; j<n; ++j) {
            b.push_back({low+(high-low)*j/n, low+(high-low)*(j+1)/n});
        }
        return b;
    }
};

struct Cell {
    I lo, hi, left, right;
    int rad;
    refine::Box box;
};

I distance_to_arc(I a, I lo, I hi) {
    I result = turn;
    for (I k : {-turn, I(0), turn}) {
        const I x = a+k;
        result = std::min(result, std::max({I(0), lo-x, x-hi}));
    }
    return result;
}

struct Group {
    std::vector<Cell> cells;
    std::vector<std::pair<I,I>> radials;
    std::vector<std::vector<I>> widths;
    int words;
    Group(const ProblemData &p, int kind, I anchor = -1, I a = 0, I b = turn)
        : radials(p.radial_bins(kind)) {
        for (Ring ring : p.rings) {
            widths.emplace_back();
            for (auto [lo,hi] : radials) widths.back().push_back(p.arc(ring.radius,lo,hi));
        }
        for (int k=0; k<(kind==0 ? 1 : p.n_angles); ++k) {
            const I lo = kind == 0 ? 0 : turn*k/p.n_angles;
            const I hi = kind == 0 ? 0 : turn*(k+1)/p.n_angles;
            if (hi<a || lo>b) continue;
            for (int rad=0; rad<int(radials.size()); ++rad) {
                const I beta = widths.back()[rad];
                if (anchor>=0 && distance_to_arc(anchor,lo,hi)>beta) continue;
                refine::Box box{};
                if (!p.directions.empty()) {
                    const auto direction=p.directions.at({lo,hi});
                    const auto [t,u]=radials[rad];
                    box=direction*refine::Iv{t,u};
                }
                cells.push_back({lo,hi,lo-beta,hi+beta,rad,box});
            }
        }
        words = (int(cells.size())+63)/64;
    }
};

struct Support {
    int word;
    Word bits;
};

struct Domain {
    std::vector<Support> words;
    I lo = turn, hi = 0, left = 2*turn, right = -turn;
    I radial_low = scale, radial_high = 0;
    std::array<I,n_caps> cap{};
    int count=0;
    refine::Box box{{scale,-scale},{scale,-scale}};
};

using D = std::shared_ptr<Domain>;
using State = std::array<D,n_disks>;

struct Literal {
    int group;
    std::shared_ptr<Mask> covered;
};

struct Row {
    std::vector<Literal> terms;
};

struct Branch {
    const Literal *literal;
    double fraction;
    std::vector<const Literal*> symmetric;
};

struct Stats {
    I nodes=0, conflict=0, unit=0, arc=0, alpha=0, removed=0;
};

struct Solver {
    ProblemData &p;
    std::array<std::shared_ptr<Group>,n_disks> groups;
    std::vector<int> order;
    std::vector<Row> rows;
    Stats stats;
    I node_limit;
    int max_depth=0;
    I leaves=0, direct_pattern=0;
    I per_leaf=0;
    refine::Refiner refiner;
    Clock::time_point start = Clock::now();

    Solver(ProblemData &p_, I limit) : p(p_), node_limit(limit) {
        groups[0] = std::make_shared<Group>(p,0);
        const I a0=turn*6/100, a8=turn-a0;
        std::array<I,8> anchors;
        for (int k=0; k<8; ++k) {
            anchors[k] = a0+(a8-a0)*k/7;
            groups[k+1]=std::make_shared<Group>(p,1,anchors[k]);
        }
        for (int k=0; k<9; ++k) order.push_back(k);
        if (p.m==10) {
            const I cap=turn*59/1000;
            const I lo = p.slot==0 ? 0 : anchors[p.slot-1]-cap;
            const I hi = p.slot==8 ? turn : anchors[p.slot]+cap;
            groups[9]=std::make_shared<Group>(p,1,-1,lo,hi);
            order.insert(order.begin()+p.slot+1,9);
        }
        auto inside = std::make_shared<Group>(p,2);
        for (int k=p.m; k<n_disks; ++k) groups[k]=inside;
        if (p.redundant) groups[11]=std::make_shared<Group>(p,1);
        prepare_rows();
    }

    void prepare_rows() {
        for (int s=0; s<int(p.rings.size()); ++s) {
            const Ring ring = p.rings[s];
            for (int j=0; j<ring.samples; ++j) {
                const I theta=turn*j/ring.samples+ring.phase;
                Row row;
                for (int k=0; k<n_disks; ++k) {
                    if (s==int(p.rings.size())-1 && k>=p.m) continue;
                    const Group &g=*groups[k];
                    bool shared=false;
                    for (const auto &term:row.terms) {
                        if (groups[term.group] == groups[k]) {
                            row.terms.push_back({k,term.covered});
                            shared=true;
                            break;
                        }
                    }
                    if (shared) continue;
                    auto mask=std::make_shared<Mask>(g.words);
                    bool hit=false;
                    for (int c=0; c<int(g.cells.size()); ++c) {
                        const auto &cell=g.cells[c];
                        const I beta=g.widths[s][cell.rad];
                        if (beta>=0 && distance_to_arc(theta,cell.lo,cell.hi)<=beta) {
                            (*mask)[c/64] |= Word(1)<<(c%64);
                            hit=true;
                        }
                    }
                    if (hit) row.terms.push_back({k,std::move(mask)});
                }
                rows.push_back(std::move(row));
            }
        }
        std::cerr<<"Built "<<rows.size()<<" witness rows in "<<elapsed()<<" s\n";
        std::cerr<<"Initial cells:";
        for (int k=0;k<n_disks;++k) std::cerr<<" "<<groups[k]->cells.size();
        std::cerr<<"\n";
    }

    double elapsed() const {
        return std::chrono::duration<double>(Clock::now()-start).count();
    }

    void summarize(int k,Domain &d) const {
        const Group &g=*groups[k];
        std::vector<bool> bins(g.radials.size(),false);
        for (auto support : d.words) {
            const int base=64*support.word;
            Word bits=support.bits;
            d.count+=std::popcount(bits);
            while (bits) {
                const int j=std::countr_zero(bits);
                bits &= bits-1;
                const Cell &c=g.cells[base+j];
                d.lo=std::min(d.lo,c.lo);
                d.hi=std::max(d.hi,c.hi);
                d.left=std::min(d.left,c.left);
                d.right=std::max(d.right,c.right);
                d.box=refine::unite(d.box,c.box);
                bins[c.rad]=true;
            }
        }
        for (int j=0;j<int(bins.size());++j) if (bins[j]) {
            d.radial_low=std::min(d.radial_low,g.radials[j].first);
            d.radial_high=std::max(d.radial_high,g.radials[j].second);
            for (int q=0;q<n_caps;++q) {
                d.cap[q]=std::max(d.cap[q],g.widths[p.cap_rings[q]][j]);
            }
        }
    }

    template <class F> D trim(D d,int k,const F &keep) {
        auto out=std::make_shared<Domain>();
        out->words.reserve(d->words.size());
        bool change=false;
        for (auto supp:d->words) {
            const Word b=keep(supp);
            change |= b!=supp.bits;
            if (b) out->words.push_back({supp.word,b});
        }
        if (!change) return d;
        if (out->words.empty()) return nullptr;
        summarize(k,*out);
        stats.removed+=d->count-out->count;
        return out;
    }

    template <class F> D filter(D d,int k,const F &allow) {
        return trim(d,k,[&](Support s) {
            Word bits=s.bits, good=0;
            while (bits) {
                const int j=std::countr_zero(bits);
                if (allow(groups[k]->cells[64*s.word+j])) good|=Word(1)<<j;
                bits&=bits-1;
            }
            return good;
        });
    }

    static int status(const Domain &d,const Mask &covered) {
        bool some=false,miss=false;
        for (const auto s:d.words) {
            const Word c=covered[s.word];
            some |= (s.bits&c)!=0;
            miss |= (s.bits&~c)!=0;
            if (some&&miss) return 1;
        }
        return some ? 2 : 0;
    }

    static int n_hits(const Domain &d,const Mask &covered) {
        int hits=0;
        for (auto s:d.words) hits+=std::popcount(s.bits&covered[s.word]);
        return hits;
    }

    State initial() const {
        State D0;
        for (int k=0;k<n_disks;++k) {
            for (int i=0;i<k;++i) {
                if (groups[i]==groups[k]) { D0[k]=D0[i]; break; }
            }
            if (D0[k]) continue;
            auto d=std::make_shared<Domain>();
            const Group &g=*groups[k];
            for (int w=0;w<g.words;++w) {
                const int n=std::min(64,int(g.cells.size())-64*w);
                d->words.push_back({w,n==64 ? ~Word(0) : (Word(1)<<n)-1});
            }
            summarize(k,*d);
            D0[k]=d;
        }
        return D0;
    }

    bool preprop(State &D0,bool &changed) {
        if (std::any_of(D0.begin(),D0.end(),[](const D &x) {return !x || !x->count;})) return false;
        auto update=[&](int k,D d) {
            changed |= d!=D0[k];
            D0[k]=d;
            return bool(d);
        };
        if (p.m==9 && !p.redundant) {
            const I max8=D0[8]->radial_high,min1=D0[1]->radial_low;
            if (min1>max8) return false;
            if (!update(1,filter(D0[1],1,[&](const Cell &c){return groups[1]->radials[c.rad].first<=max8;}))
                || !update(8,filter(D0[8],8,[&](const Cell &c){return groups[8]->radials[c.rad].second>=min1;}))) return false;
            for (int k=9;k<11;++k) {
                const I lo=D0[k]->lo,hi=D0[k+1]->hi;
                if (lo>hi) return false;
                if (!update(k,filter(D0[k],k,[&](const Cell &c){return c.lo<=hi;}))
                    || !update(k+1,filter(D0[k+1],k+1,[&](const Cell &c){return c.hi>=lo;}))) return false;
            }
        }
        I shallow=scale;
        for (int k:order) shallow=std::min(shallow,D0[k]->radial_high);
        if (D0[0]->radial_low>shallow) return false;
        if (groups[0]->radials.back().first>shallow &&
            !update(0,filter(D0[0],0,[&](const Cell &c) { return groups[0]->radials[c.rad].first<=shallow; }))) return false;
        const I deep=D0[0]->radial_low;
        for (int k:order) {
            if (D0[k]->radial_low<deep && !update(k,filter(D0[k],k,[&](const Cell &c) {
                return groups[k]->radials[c.rad].second>=deep;
            }))) return false;
        }
        I alpha_sum=0;
        for (int k:order) alpha_sum+=D0[k]->cap[n_caps-1];
        if (alpha_sum<turn/2) { ++stats.alpha; return false; }
        for (int index=0;index<int(order.size());++index) {
            const int i=order[index],j=order[(index+1)%order.size()];
            const I wrap=j==0 ? turn : 0;
            const I min_gap=std::max(I(0),turn-2*alpha_sum+D0[i]->cap[n_caps-1]+D0[j]->cap[n_caps-1]);
            const I a=D0[i]->right, b=D0[j]->left+wrap;
            const I c=D0[i]->lo, d=D0[j]->hi+wrap;
            if (a<b || d<c+min_gap) { ++stats.arc; return false; }
            if (!update(i,filter(D0[i],i,[&](const Cell &cell) {return cell.right>=b && cell.lo<=d-min_gap;}))) return false;
            if (!update(j,filter(D0[j],j,[&](const Cell &cell) {return cell.left+wrap<=a && cell.hi+wrap>=c+min_gap;}))) return false;
        }
        for (int q=0;q<n_caps;++q) {
            I sum=0;
            for (int k=0;k<n_disks;++k) if (q<n_caps-1 || k<p.m) sum+=D0[k]->cap[q];
            if (sum<turn/2) { ++stats.alpha; return false; }
            for (int k=0;k<n_disks;++k) if (q<n_caps-1 || k<p.m) {
                const I threshold=turn/2-sum+D0[k]->cap[q];
                if (threshold<=0) continue;
                const auto &values=groups[k]->widths[p.cap_rings[q]];
                if (!update(k,filter(D0[k],k,[&](const Cell &c) {return values[c.rad]>=threshold;}))) return false;
            }
        }
        return true;
    }

    bool propagate(State &d,std::vector<int> &pending) {
        while (true) {
            bool changed=false;
            if (!preprop(d,changed)) return false;
            std::vector<int> next;
            next.reserve(pending.size());
            for (int ix:pending) {
                int n=0;
                bool guaranteed=false;
                const Literal *only=nullptr;
                for (const auto &lit:rows[ix].terms) {
                    const int s=status(*d[lit.group],*lit.covered);
                    if (s==2) { guaranteed=true; break; }
                    if (s==1) { ++n; only=&lit; }
                }
                if (guaranteed) continue;
                if (n==0) return false;
                if (n==1) {
                    const int k=only->group;
                    d[k]=trim(d[k],k,[&](Support s) {return s.bits&(*only->covered)[s.word];});
                    changed=true;
                    ++stats.unit;
                } else {
                    next.push_back(ix);
                }
            }
            pending.swap(next);
            if (!changed) return true;
        }
    }

    std::vector<Branch> branches(const State &d,const std::vector<int> &pending) const {
        std::vector<Branch> best;
        double score=100;
        for (int ix:pending) {
            std::vector<Branch> candidate;
            double total=0;
            for (const auto &lit:rows[ix].terms) {
                const int k=lit.group;
                const int n=n_hits(*d[k],*lit.covered);
                if (!n) continue;
                bool symmetric=false;
                for (auto &x:candidate) {
                    const int g=x.literal->group;
                    if ((p.m!=9 || p.redundant) && k>=p.m && g>=p.m && groups[k]==groups[g] &&
                        d[k]->count==d[g]->count && d[k]->words.size()==d[g]->words.size() &&
                        std::equal(d[k]->words.begin(),d[k]->words.end(),d[g]->words.begin(),
                                   [](Support a,Support b){ return a.word==b.word && a.bits==b.bits; })) {
                        x.symmetric.push_back(&lit);
                        symmetric=true;
                        break;
                    }
                }
                if (!symmetric) {
                    const double f=double(n)/d[k]->count;
                    total+=f;
                    candidate.push_back({&lit,f,{}});
                    if (total>=score) break;
                }
            }
            if (total<score) {
                score=total;
                best=std::move(candidate);
            }
        }
        std::sort(best.begin(),best.end(),[](const Branch &a,const Branch &b){return a.fraction<b.fraction;});
        return best;
    }

    void display(const State &d) const {
        for (int k=0;k<n_disks;++k) {
            const auto b=d[k]->words.front();
            const auto &c=groups[k]->cells[64*b.word+std::countr_zero(b.bits)];
            const auto [rl,rh]=groups[k]->radials[c.rad];
            std::cout << k << ' ' << d[k]->count << ' '
                      << (rl+rh)/2.0/scale << ' '
                      << (c.lo+c.hi)/2.0/turn << '\n';
        }
    }

    bool recognize(const State &d,refine::Boxes &boxes,refine::Hints &polar) const {
        for (int k=0;k<n_disks;++k) boxes[k]=d[k]->box;
        for (int k=0;k<3;++k) {
            const Domain &g=*d[9+k];
            polar[k]={g.lo,g.hi,g.radial_low,g.radial_high};
        }
        return refine::in_balanced_pattern(boxes,polar);
    }

    bool search(State d,std::vector<int> pending,int depth) {
        ++stats.nodes;
        max_depth=std::max(max_depth,depth);
        if (node_limit && stats.nodes>node_limit) throw std::string("node limit");
        if (stats.nodes%1000000==0 || stats.nodes==1000) {
            std::cerr << "node " << stats.nodes << " time " << elapsed() << " maxdepth " << max_depth
                      << " left " << pending.size() << " units " << stats.unit << " sizes";
            for (auto x:d) std::cerr<<" "<<(x ? x->count : 0);
            std::cerr<<"\n";
            if (!p.directions.empty()) std::cerr<<"leaf "<<leaves<<" refinements "<<refiner.nodes
                <<" patterns "<<direct_pattern<<"+"<<refiner.balanced<<"\n";
        }
        if (!p.directions.empty()) {
            refine::Boxes boxes;
            refine::Hints polar;
            if (recognize(d,boxes,polar)) { ++direct_pattern; return false; }
        }
        if (!propagate(d,pending)) {
            ++stats.conflict;
            return false;
        }
        if (!p.directions.empty()) {
            refine::Boxes boxes;
            refine::Hints polar;
            if (recognize(d,boxes,polar)) {
                ++direct_pattern;
                return false;
            }
            if (pending.empty()) {
                ++leaves;
                refiner.limit=per_leaf ? refiner.nodes+per_leaf : 0;
                if (refiner.prove(boxes,polar)) return false;
                std::cerr<<"Unresolved input boxes:\n";
                for (const auto &b:boxes) std::cerr<<b.x.lo<<" "<<b.x.hi<<" "<<b.y.lo<<" "<<b.y.hi<<"\n";
                for (const auto &g:polar) std::cerr<<g.alo<<" "<<g.ahi<<" "<<g.rlo<<" "<<g.rhi<<"\n";
            }
        }
        if (pending.empty()) {
            display(d);
            return true;
        }
        const auto next=branches(d,pending);
        for (const auto &choice:next) {
            const auto &lit=*choice.literal;
            const int k=lit.group;
            D original=d[k];
            d[k]=trim(original,k,[&](Support s) {return s.bits&(*lit.covered)[s.word];});
            if (d[k] && search(d,pending,depth+1)) return true;
            d[k]=trim(original,k,[&](Support s) {return s.bits&~(*lit.covered)[s.word];});
            if (!d[k]) break;
            for (const auto *eq:choice.symmetric) {
                const int g=eq->group;
                d[g]=trim(d[g],g,[&](Support s){return s.bits&~(*eq->covered)[s.word];});
                if (!d[g]) return false;
            }
        }
        return false;
    }

    bool solve() {
        std::vector<int> pending(rows.size());
        std::iota(pending.begin(),pending.end(),0);
        auto root=initial();
        if (p.stop_bin>p.start_bin) {
            root[0]=filter(root[0],0,[&](const Cell &c) {
                return p.start_bin<=c.rad && c.rad<p.stop_bin;
            });
            if (!root[0]) return false;
        }
        if (p.good.empty()) return search(std::move(root),std::move(pending),0);
        for (int k:{9,10,11,0,3,6,1,2,4,5,7,8}) {
            const auto [al,ah,rl,rh]=p.good.at(k);
            auto contained=[&](const Cell &c) {
                const auto [l,h]=groups[k]->radials[c.rad];
                return al<=c.lo && c.hi<=ah && rl<=l && h<=rh;
            };
            State bad=root;
            bad[k]=filter(root[k],k,[&](const Cell &c){return !contained(c);});
            if (bad[k]) {
                std::cerr<<"Complement of good ranges, first outside group "<<k<<"\n";
                if (search(std::move(bad),pending,0)) return true;
            }
            root[k]=filter(root[k],k,contained);
            if (!root[k]) break;
        }
        return false;
    }
};

} // namespace circle

int main(int argc,char **argv) {
    using namespace circle;
    if (argc<8) {
        std::cerr<<"Exact angular bounds are required. Run verify_global.py.\n";
        return 2;
    }
    int m=argc>1 ? std::atoi(argv[1]) : 10;
    int a=argc>2 ? std::atoi(argv[2]) : 360;
    int nr=argc>3 ? std::atoi(argv[3]) : 48;
    int slot=argc>4 ? std::atoi(argv[4]) : 4;
    I lim=argc>5 ? std::atoll(argv[5]) : 200000;
    int red=argc>6 ? std::atoi(argv[6]) : 0;
    ProblemData p(m,a,nr,slot,red);
    if (argc>11) {
        p.start_bin=std::atoi(argv[10]);
        p.stop_bin=std::atoi(argv[11]);
    }
    if (argc>7) {
        std::ifstream file(argv[7]);
        I s,t,u,h;
        while (file>>s>>t>>u>>h) p.exact[{s,t,u}]=h;
        if (p.exact.empty()) return 2;
    }
    if (argc>8) {
        std::ifstream file(argv[8]);
        I a,b,x,y,z,w;
        while (file>>a>>b>>x>>y>>z>>w) {
            if (a==-1) p.good[int(b)]={x,y,z,w};
            else p.directions[{a,b}]={{x,y},{z,w}};
        }
        if (p.directions.empty() || m!=9 || red) return 2;
    }
    if (m==9 && !red && (p.directions.empty() || p.good.size()!=12)) return 2;
    std::cout<<std::setprecision(14);
    Solver solver(p,lim);
    if (argc>9) solver.per_leaf=std::atoll(argv[9]);
    int status=1;
    try {
        bool ok=solver.solve();
        std::cout<<(ok ? "unresolved" : "excluded")<<'\n';
        if (!ok) status=0;
    } catch (const std::string &what) {
        std::cout<<what<<'\n';
    }
    const auto &s=solver.stats;
    std::cout << "nodes "<<s.nodes<<" conflicts "<<s.conflict<<" units "<<s.unit
              <<" arcs "<<s.arc<<" alpha "<<s.alpha<<" elapsed "<<solver.elapsed()<<'\n';
    if (!p.directions.empty()) std::cout << "leaves " << solver.leaves
        << " refinement nodes " << solver.refiner.nodes << " refinement conflicts "
        << solver.refiner.dead << " pattern " << solver.direct_pattern << "+" << solver.refiner.balanced
        << " refinement depth " << solver.refiner.max_depth << '\n';
    return status;
}
