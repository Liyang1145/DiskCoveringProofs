#ifndef CIRCLE_REFINE_GEOMETRY_HPP
#define CIRCLE_REFINE_GEOMETRY_HPP

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <utility>
#include <vector>

namespace refine {

using I = std::int64_t;
using W = __int128_t;
constexpr I scale=1000000000;
constexpr I r_units=361102964;
constexpr I turn=1008000000;
constexpr int n_disks=12;

I floor_div(W a,W b) {
    if (b<=0) throw std::logic_error("bad divisor");
    W q=a/b;
    if (a%b<0) --q;
    if (q<std::numeric_limits<I>::min() || q>std::numeric_limits<I>::max())
        throw std::overflow_error("interval bound overflow");
    return I(q);
}

I ceil_div(W a,W b) { return -floor_div(-a,b); }

I floor_root(W v) {
    if (v<0) throw std::logic_error("negative square root");
    I x=I(std::sqrt((long double)v));
    while (W(x)*x>v) --x;
    while (W(x+1)*(x+1)<=v) ++x;
    return x;
}

I ceil_root(W v) {
    I a=floor_root(v);
    return W(a)*a==v ? a : a+1;
}

struct Iv {
    I lo,hi;
    Iv operator-() const { return {-hi,-lo}; }
    Iv operator+(Iv b) const { return {lo+b.lo,hi+b.hi}; }
    Iv operator-(Iv b) const { return *this+(-b); }
    Iv operator*(Iv b) const {
        const auto [l,h]=std::minmax({W(lo)*b.lo,W(lo)*b.hi,W(hi)*b.lo,W(hi)*b.hi});
        return {floor_div(l,scale),ceil_div(h,scale)};
    }
    Iv div(I n) const { return {floor_div(lo,n),ceil_div(hi,n)}; }
    Iv div(Iv b) const {
        if (b.lo<=0) throw std::logic_error("nonpositive interval divisor");
        return *this*Iv{floor_div(W(scale)*scale,b.hi),ceil_div(W(scale)*scale,b.lo)};
    }
    Iv square() const {
        W a=W(lo)*lo,b=W(hi)*hi;
        return {lo<=0 && hi>=0 ? 0 : floor_div(std::min(a,b),scale),
                ceil_div(std::max(a,b),scale)};
    }
    Iv sqrt() const {
        return {floor_root(W(lo)*scale),ceil_root(W(hi)*scale)};
    }
};

struct Box {
    Iv x,y;
    bool empty() const { return x.lo>x.hi || y.lo>y.hi; }
    Iv norm2() const { return x.square()+y.square(); }
    I width() const { return x.hi-x.lo+y.hi-y.lo; }
    Box operator+(const Box &b) const { return {x+b.x,y+b.y}; }
    Box operator-(const Box &b) const { return {x-b.x,y-b.y}; }
    Box operator*(Iv a) const { return {x*a,y*a}; }
    Box div(I n) const { return {x.div(n),y.div(n)}; }
};

Box unite(Box a,Box b) {
    return {{std::min(a.x.lo,b.x.lo),std::max(a.x.hi,b.x.hi)},
            {std::min(a.y.lo,b.y.lo),std::max(a.y.hi,b.y.hi)}};
}

struct Point {
    I x,y;
    bool operator==(const Point &) const = default;
};

W sq(I n) { return W(n)*n; }
W gap(Iv a,Iv b) { return std::max({I(0),a.lo-b.hi,b.lo-a.hi}); }
W dist2_min(const Box &a,const Box &b) {
    W dx=gap(a.x,b.x),dy=gap(a.y,b.y);
    return dx*dx+dy*dy;
}
W dist2_min(const Box &b,Point p) {
    return dist2_min(b,Box{{p.x,p.x},{p.y,p.y}});
}
W dist2_max(const Box &b,Point p) {
    return std::max(sq(p.x-b.x.lo),sq(p.x-b.x.hi))
          +std::max(sq(p.y-b.y.lo),sq(p.y-b.y.hi));
}

using Boxes = std::array<Box,n_disks>;
constexpr W r2=W(r_units)*r_units;
struct Polar {
    I alo,ahi,rlo,rhi;
};
using Hints=std::array<Polar,3>;

bool disjoint_from_pair(const Boxes &b,int i,int j,int k) {
    return dist2_min(b[i],b[k])>4*r2 || dist2_min(b[j],b[k])>4*r2;
}

bool outside(Box p,const Boxes &b,int i,int j,int k,int first) {
    for (int q=first;q<n_disks;++q)
        if (q!=i && q!=j && q!=k && !disjoint_from_pair(b,i,j,q)
            && dist2_min(p,b[q])<=r2) return false;
    return true;
}

bool crossing(Box a,Box b,bool inward,Box &p) {
    const Iv r{361102963,361102964};
    const Box e=b-a;
    const Iv t=e.norm2();
    if (t.lo<=0) return false;
    const Iv h=r.square()-t.div(4);
    if (h.lo<=0) return false;
    Iv ratio=h.sqrt().div(t.sqrt());
    const Box normal{-e.y,e.x};
    const Box m=(a+b).div(2);
    p=inward ? m+normal*ratio : m-normal*ratio;
    return true;
}

bool in_balanced_pattern(const Boxes &b,const Hints &polar) {
    std::array<Iv,3> u;
    for (int k=0;k<3;++k) {
        u[k]=b[9+k].norm2().sqrt();
        u[k].lo=std::max(u[k].lo,polar[k].rlo);
        u[k].hi=std::min(u[k].hi,polar[k].rhi);
        if (u[k].lo>u[k].hi || u[k].lo<100000000) return false;
    }
    std::array<int,3> seq={9,10,11};
    bool acute_inner=true;
    for (int k=9;k<12;++k) {
        const Box x=b[9+(k-9+1)%3]-b[k];
        const Box y=b[9+(k-9+2)%3]-b[k];
        if ((x.x*y.x+x.y*y.y).lo<=0 || u[k-9].hi>=361102963) acute_inner=false;
    }
    do {
        bool valid=true;
        for (int k=0;k<3 && valid;++k) {
            int i=seq[k],j=seq[(k+1)%3];
            const auto &p=b[i],&q=b[j];
            const bool large=u[i-9].lo>=140000000 && u[j-9].lo>=140000000;
            const I max_gap=large ? turn/2-1 : 425134683;
            const auto a=polar[i-9],e=polar[j-9];
            I wrap=e.ahi<=a.alo ? turn : 0;
            const I dlo=e.alo-a.ahi+wrap,dhi=e.ahi-a.alo+wrap;
            if (dlo<=0 || dhi>max_gap) {
                const Iv cross=p.x*q.y-p.y*q.x;
                if (cross.lo<=0) { valid=false; break; }
                if (!large) {
                    const Iv cosine=(p.x*q.x+p.y*q.y).div(u[i-9]*u[j-9]);
                    if (cosine.lo<-881582193) valid=false;
                }
            }
        }
        for (int k=0;k<3 && valid;++k) {
            Box p;
            const int left=3*k+1,right=3*k+2;
            const int i=seq[k],j=seq[(k+1)%3],low=(3*k+3)%9;
            // In a nine-arc cover the other six outer disks are disjoint
            // from at least one of the two disks. Their nearer intersection
            // is inside the unit disk by the radial normalization.
            bool high_isolated=true;
            for (int q=9;q<n_disks;++q)
                if (q!=i && !disjoint_from_pair(b,left,right,q)) high_isolated=false;
            if (!high_isolated &&
                (!crossing(b[left],b[right],true,p) || !outside(p,b,left,right,i,9))) {
                valid=false;
                break;
            }
            bool low_isolated=acute_inner;
            if (low_isolated) for (int q=0;q<9;++q)
                if (q!=low && !disjoint_from_pair(b,i,j,q)) low_isolated=false;
            if (!low_isolated &&
                (!crossing(b[i],b[j],false,p) || !outside(p,b,i,j,low,0))) {
                valid=false;
                break;
            }
        }
        if (valid) return true;
    } while (std::next_permutation(seq.begin(),seq.end()));
    return false;
}

struct Vec {
    double x,y;
    Vec operator+(Vec q) const { return {x+q.x,y+q.y}; }
    Vec operator-(Vec q) const { return {x-q.x,y-q.y}; }
    Vec operator*(double a) const { return {x*a,y*a}; }
    double dot(Vec q) const { return x*q.x+y*q.y; }
    double norm2() const { return dot(*this); }
    Vec perpendicular() const { return {-y,x}; }
};

Vec midpoint(Box b) {return {(b.x.lo+b.x.hi)/2.0/scale,(b.y.lo+b.y.hi)/2.0/scale};}

std::vector<Point> generate_witnesses(const Boxes &b) {
    std::array<Vec,n_disks> centers;
    for (int k=0;k<n_disks;++k) centers[k]=midpoint(b[k]);
    std::vector<std::pair<double,Point>> candidates;
    auto offer=[&](Vec p) {
        const double n=p.norm2();
        if (!std::isfinite(n) || n>1.000000000001) return;
        if (n>1) p=p*(1/std::sqrt(n));
        Point q{I(p.x*scale),I(p.y*scale)};
        if (sq(q.x)+sq(q.y)>W(scale)*scale) return;
        double minimum=9;
        for (auto c:centers) minimum=std::min(minimum,(c-p).norm2());
        if (minimum>.120) candidates.push_back({minimum,q});
    };
    for (int i=0;i<n_disks;++i) {
        const Vec c=centers[i];
        if (c.norm2()>1e-16) offer(c*(-1/std::sqrt(c.norm2())));
        for (int j=i+1;j<n_disks;++j) {
            const Vec u=centers[j]-c;
            const double nu=u.norm2();
            if (nu<1e-20) continue;
            const Vec normal=u*(1/std::sqrt(nu));
            const double offset=normal.dot((centers[j]+c)*.5);
            if (std::abs(offset)<=1) {
                const Vec projection=normal*offset;
                const Vec diff=normal.perpendicular()*std::sqrt(1-offset*offset);
                offer(projection+diff);
                offer(projection-diff);
            }
            for (int k=j+1;k<n_disks;++k) {
                const Vec v=centers[k]-c;
                const double det=2*(u.x*v.y-u.y*v.x);
                if (std::abs(det)<1e-14) continue;
                const double nv=v.norm2();
                offer(c+Vec{(nu*v.y-nv*u.y)/det,(nv*u.x-nu*v.x)/det});
            }
        }
    }
    std::sort(candidates.begin(),candidates.end(),[](const auto &a,const auto &b) {
        return a.first>b.first;
    });
    std::vector<Point> out;
    for (auto [d,p]:candidates) {
        bool distinct=true;
        for (auto q:out) if (sq(p.x-q.x)+sq(p.y-q.y)<W(10000)*10000) {
            distinct=false;
            break;
        }
        if (distinct) out.push_back(p);
        if (out.size()==22) break;
    }
    return out;
}

Box trim_circle(Box b,Point p) {
    W dy=gap(b.y,Iv{p.y,p.y});
    if (dy*dy>r2) return {{1,0},{1,0}};
    I dx=ceil_root(r2-dy*dy);
    b.x={std::max(b.x.lo,p.x-dx),std::min(b.x.hi,p.x+dx)};
    if (b.empty()) return b;
    W dd=gap(b.x,Iv{p.x,p.x});
    if (dd*dd>r2) return {{1,0},{1,0}};
    I yy=ceil_root(r2-dd*dd);
    b.y={std::max(b.y.lo,p.y-yy),std::min(b.y.hi,p.y+yy)};
    return b;
}

struct Refiner {
    I nodes=0,dead=0,balanced=0,unit=0;
    I limit=0;
    int max_depth=0;

    bool prove(Boxes boxes,const Hints &polar,std::vector<Point> inherited={},int depth=0) {
        ++nodes;
        max_depth=std::max(max_depth,depth);
        if (limit && nodes>limit) return false;
        if (in_balanced_pattern(boxes,polar)) { ++balanced; return true; }
        auto w=generate_witnesses(boxes);
        for (auto p:inherited) if (std::find(w.begin(),w.end(),p)==w.end()) w.push_back(p);
        if (w.size()>72) w.resize(72);
        for (int pass=0;pass<4;++pass) {
            bool changed=false;
            for (auto p:w) {
                int count=0,last=-1;
                bool full=false;
                for (int k=0;k<n_disks;++k) {
                    if (dist2_max(boxes[k],p)<=r2) { full=true; break; }
                    if (dist2_min(boxes[k],p)<=r2) {++count;last=k;}
                }
                if (full) continue;
                if (!count) { ++dead; return true; }
                if (count==1) {
                    const auto next=trim_circle(boxes[last],p);
                    if (next.empty()) { ++dead; return true; }
                    if (next.width()<boxes[last].width()) {
                        changed=true;
                        ++unit;
                        boxes[last]=next;
                    }
                }
            }
            if (!changed) break;
        }
        if (in_balanced_pattern(boxes,polar)) { ++balanced; return true; }

        int best_count=n_disks+1;
        Point chosen{};
        std::array<bool,n_disks> able{};
        W best_margin=0;
        for (auto p:w) {
            W d=std::numeric_limits<I>::max();
            std::array<bool,n_disks> possible{};
            int count=0;
            bool full=false;
            bool variable=false;
            for (int k=0;k<n_disks;++k) {
                if (dist2_max(boxes[k],p)<=r2) { full=true; break; }
                const W d0=dist2_min(boxes[k],p);
                if (d0<=r2) {
                    possible[k]=true;
                    ++count;
                    variable |= boxes[k].x.hi-boxes[k].x.lo>1 || boxes[k].y.hi-boxes[k].y.lo>1;
                }
                d=std::min(d,d0);
            }
            if (full) continue;
            if (!count) { ++dead; return true; }
            if (!variable) continue;
            if (count<best_count || (count==best_count && d>best_margin)) {
                best_count=count;
                best_margin=d;
                chosen=p;
                able=possible;
            }
        }

        if (best_count>1 && best_count<=3) {
            bool shrinks=true;
            Boxes narrowed=boxes;
            for (int k=0;k<n_disks;++k) if (able[k]) {
                narrowed[k]=trim_circle(boxes[k],chosen);
                if (narrowed[k].empty()) continue;
                if (narrowed[k].width()*5>4*boxes[k].width()) shrinks=false;
            }
            if (shrinks) {
                for (int k=0;k<n_disks;++k) if (able[k]&&!narrowed[k].empty()) {
                    auto sub=boxes;
                    sub[k]=narrowed[k];
                    if (!prove(sub,polar,w,depth+1)) return false;
                }
                return true;
            }
        }

        int kbest=-1,axis=0;
        W score=-1;
        for (int k=0;k<n_disks;++k) if (able[k] || best_count==n_disks+1) {
            for (int a=0;a<2;++a) {
                const Iv range=a ? boxes[k].y : boxes[k].x;
                const I len=range.hi-range.lo;
                if (len<=1) continue;
                const I wp=a ? chosen.y : chosen.x;
                const I offset=best_count==n_disks+1 ? scale : std::abs(wp-(range.hi+range.lo)/2)+1000;
                const W s=W(len)*offset;
                if (s>score) {score=s;kbest=k;axis=a;}
            }
        }
        if (kbest<0 || depth>=200) {
            std::cerr<<"Refinement unresolved at depth "<<depth<<" with "<<best_count<<" supports.\n";
            for (const auto &box:boxes) std::cerr<<box.x.lo<<" "<<box.x.hi<<" "<<box.y.lo<<" "<<box.y.hi<<"\n";
            return false;
        }
        Iv &x=axis ? boxes[kbest].y : boxes[kbest].x;
        const Iv hold=x;
        const I cut=x.lo+(x.hi-x.lo)/2;
        x.hi=cut;
        if (!prove(boxes,polar,w,depth+1)) return false;
        x={cut,hold.hi};
        return prove(boxes,polar,w,depth+1);
    }
};

} // namespace refine

#endif
