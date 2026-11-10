#include <algorithm>
#include <array>
#include <atomic>
#include <cfenv>
#include <cfloat>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <future>
#include <iomanip>
#include <iostream>
#include <limits>
#include <memory>
#include <mutex>
#include <stdexcept>
#include <string>
#include <thread>
#include <type_traits>
#include <unordered_map>
#include <utility>
#include <vector>

using real = double;
static_assert(std::numeric_limits<real>::is_iec559 && std::numeric_limits<real>::digits==53);
static_assert(sizeof(real)==sizeof(std::uint64_t) && FLT_EVAL_METHOD==0);
constexpr real inf = std::numeric_limits<real>::infinity();
constexpr std::uint64_t sign_bit = std::uint64_t{1}<<63;
template<bool Up> real adjacent(real x) {
    std::uint64_t bits;
    std::memcpy(&bits,&x,sizeof(bits));
    if((bits&~sign_bit)==0)bits=Up?1:sign_bit|1;
    else if(x!=(Up?inf:-inf))bits+=((bits&sign_bit)==0)==Up?1:-std::uint64_t{1};
    std::memcpy(&x,&bits,sizeof(x));
    return x;
}
real down(real x) { return adjacent<false>(x); }
real up(real x) { return adjacent<true>(x); }

struct I {
    real lo, hi;
    I(real x = 0) : lo(x), hi(x) {}
    I(real a, real b) : lo(a), hi(b) {}
};
I operator+(I a, I b) { return {down(a.lo+b.lo),up(a.hi+b.hi)}; }
I operator-(I a) { return {-a.hi,-a.lo}; }
I operator-(I a, I b) { return a+(-b); }
I operator*(I a, I b) {
    real p=a.lo*b.lo,q=a.lo*b.hi,r=a.hi*b.lo,s=a.hi*b.hi;
    return {down(std::min({p,q,r,s})),up(std::max({p,q,r,s}))};
}
I operator/(I a,I b) {
    if(b.lo<=0 && b.hi>=0) throw std::domain_error("division by an interval containing zero");
    return a*I(down(1/b.hi),up(1/b.lo));
}
I rat(int p,int q=1) {return I(p)/I(q);}
I sq(I a) {
    if(a.lo>=0) return {std::max(0.,down(a.lo*a.lo)),up(a.hi*a.hi)};
    if(a.hi<=0) return {std::max(0.,down(a.hi*a.hi)),up(a.lo*a.lo)};
    return {0,up(std::max(a.lo*a.lo,a.hi*a.hi))};
}
I nonneg(I a) { return {std::max(0.,a.lo),std::max(0.,a.hi)}; }
I abs_i(I a) {
    if(a.lo>=0)return a;
    if(a.hi<=0)return -a;
    return {0,std::max(-a.lo,a.hi)};
}
I rt(I a) {
    if(a.hi<0)throw std::domain_error("negative radical");
    real l=a.lo<1e-290?0:std::sqrt(a.lo);
    real h=(0<a.hi && a.hi<1e-290)?1e-144:std::sqrt(a.hi);
    if(l>0)while(up(l*l)>a.lo)l=down(l);
    if(h>0)while(down(h*h)<a.hi)h=up(h);
    return {l,h};
}

I atan_small(I x) {
    real a=std::max(std::abs(x.lo),std::abs(x.hi));
    if(a>0.501)throw std::domain_error("unreduced arctangent");
    I power=x,sum(0),mult=-sq(x);
    for(int k=0;k<26;k++) {sum=sum+power/I(2*k+1);power=power*mult;}
    real e=(abs_i(power)/53).hi;
    return sum+I(-e,e);
}
const I pi=16*atan_small(rat(1,5))-4*atan_small(rat(1,239));
I atan_point(real x) {
    if(x<0)return -atan_point(-x);
    if(x<=0.5)return atan_small(I(x));
    if(x>=2)return pi/2-atan_small(1/I(x));
    return pi/4+atan_small((I(x)-1)/(I(x)+1));
}
I atan_i(I x) {return {atan_point(x.lo).lo,atan_point(x.hi).hi};}
I asin_point(real x) {
    if(x<=0)return 0;
    if(x>=1)return pi/2;
    I root=rt(1-sq(I(x)));
    return x<=.5?atan_i(I(x)/root):pi/2-atan_i(root/I(x));
}
I asin_i(I x) {return {asin_point(x.lo).lo,asin_point(x.hi).hi};}

struct Trig {I s,c;};
Trig trig_point(real a) {
    I x(a),s(0),c(0),st=x,ct=1,m=-sq(x);
    for(int j=0;j<15;j++){
        s=s+st;c=c+ct;
        st=st*m/((2*j+2)*(2*j+3));
        ct=ct*m/((2*j+1)*(2*j+2));
    }
    real se=abs_i(st).hi,ce=abs_i(ct).hi;
    return {s+I(-se,se),c+I(-ce,ce)};
}
Trig trig(I a) {
    a=nonneg(a);
    if(a.hi>2)throw std::domain_error("angle outside [0,2]");
    static std::unordered_map<real,Trig> cache;
    auto get=[&](real x){
        auto it=cache.find(x);
        if(it!=cache.end())return it->second;
        auto val=trig_point(x);cache.emplace(x,val);return val;
    };
    Trig l=get(a.lo),h=get(a.hi);
    real s_hi=(a.lo<=(pi/2).hi && a.hi>=(pi/2).lo)?1:std::max(l.s.hi,h.s.hi);
    return {{std::min(l.s.lo,h.s.lo),s_hi},{h.c.lo,l.c.hi}};
}
struct V {I x,y;};
V operator+(V a,V b){return {a.x+b.x,a.y+b.y};}
V operator-(V a,V b){return {a.x-b.x,a.y-b.y};}
V operator*(I t,V a){return {t*a.x,t*a.y};}
V operator/(V a,I t){return {a.x/t,a.y/t};}
V left(V a){return {-a.y,a.x};}
I dot(V a,V b){return a.x*b.x+a.y*b.y;}
I det(V a,V b){return a.x*b.y-a.y*b.x;}
I norm2(V a){return sq(a.x)+sq(a.y);}
I norm(V a){return rt(norm2(a));}
V unit(Trig a){return {a.c,a.s};}

const I root2=rt(I(2)), R=rt(I(6))+rt(I(3)), S=R-2, R2=sq(R), T2=R2-1, T=rt(T2);
const I M=asin_i(1/R), tc=2+root2, delta_cos=rt(2+root2)/2, td=4*delta_cos;
const I lambda=root2/4, fan_price=R2-1-2*lambda, eta=rat(203,200);
const I d_price=root2+10*rat(23,50)+rat(31,10), tilt_price=1/delta_cos+10*rat(59,200);
const I p_rad=rat(-863,250),p_x=rat(1281,1000),p_y=rat(-223,1000);
const V p_vec{p_x,p_y};
const I cap_normal=rat(546,100),cap_block=rat(3215,100);
const I unit_peak=rt(I(3))/2, area_peak=3*rt(I(3))/4;
const I Fc=fan_price*asin_i(root2/(2*R))-tc*root2/2+lambda*pi/2;
const I Fd=fan_price*asin_i(delta_cos/R)-td*delta_cos+3*lambda*pi/4;
const I min_outer=R-1;
const I fan_ceiling=rat(823,250);
const I outer_angle_area=rat(8224,10000);

struct StarPrices {
    I azimuth, tilt, angle;
    bool cap_fan=false;
    I outer_angle=0;
    I core_radius=1;
    bool away=false;
    I core_chord=1;
};
const StarPrices standard_prices{d_price,tilt_price,eta};
const StarPrices ten_ring_prices{4,tilt_price,1,true};
const StarPrices priced_ring{4,tilt_price,1,true,rat(1,2)};
const StarPrices twin_ring{rat(24,5),rat(33,10),rat(7,10),true,rat(1,2)};
const StarPrices chord_ring{rat(17,3),rat(-4,5),0,true,rat(1,2),1,false,rat(29,10)};
const StarPrices seven_chord_ring{5,rat(9,5),0,true,rat(1,2),1,false,rat(17,10)};
const StarPrices wide_ring{4,tilt_price,1,true,0,rat(1069,1000),true};
const StarPrices wide_three_ring{4,tilt_price,1,true,0,rat(1455,1000),true};

I cap_fan_score(I value,const StarPrices& prices){
    return prices.cap_fan?I(std::min(value.hi,fan_ceiling.hi)):value;
}

I radial_q(I t) {
    I h=(T2-sq(t))/(2*t);
    return rt(nonneg(1-sq(h)));
}
I score_at(real high) {
    // F is capped at t_D, and p is capped at sqrt(R^2-1); both are nondecreasing below their caps.
    real t=std::max(high,min_outer.hi);
    I f;
    if(t>=td.lo) f=Fd;
    else { I q=radial_q(t); f=fan_price*asin_i(q/R)-I(t)*q+2*lambda*asin_i(q); }
    I half=t>=T.lo?M:asin_i(radial_q(t)/R);
    return f+10*half;
}

constexpr int mesh = 16384;
I score_upper(real high) {
    // Upper bounds at the dyadic mesh points, looked up to the right.
    static const auto table=[] {
        std::array<real,mesh+1> values{};
        for(int i=0;i<=mesh;i++)values[i]=score_at(3.+real(i)/mesh).hi;
        return values;
    }();
    int i=static_cast<int>(std::ceil(high*mesh))-3*mesh;
    return i>mesh?I((Fd+10*M).hi):I(table[std::max(0,i)]);
}

struct FanDerivative { I rim,area; };

bool fan_derivative(real t,FanDerivative& result){
    if(t>=T.lo)return false;
    I r(t),h=(T2-sq(r))/(2*r),width=rt(nonneg(1-sq(h)));
    if(width.lo<=0)return false;
    result={h/(r*width), t<td.lo?(2*sq(h)-1+2*lambda)/width:I(0)};
    return true;
}

const std::array<I,mesh+1>& asin_table() {
    static const auto table=[] {
        std::array<I,mesh+1> values{};
        for(int i=0;i<=mesh;i++)values[i]=asin_point(real(i)/mesh);
        return values;
    }();
    return table;
}
I asin_lower(real low) {
    return I(asin_table()[std::clamp(static_cast<int>(std::floor(low*mesh)),0,mesh)].lo);
}
I asin_mesh(I a) {
    const auto& table=asin_table();
    auto low=[&](real x){
        int k=std::clamp(static_cast<int>(std::floor(x*mesh)),-mesh,mesh);
        return k<0?-table[-k].hi:table[k].lo;
    };
    auto high=[&](real x){
        int k=std::clamp(static_cast<int>(std::ceil(x*mesh)),-mesh,mesh);
        return k<0?-table[-k].lo:table[k].hi;
    };
    return {low(a.lo),high(a.hi)};
}

struct Edge {
    I x, h, radius, inside_area, outer_area;
    V midpoint;
    V inward_scaled;
};
I triangle_area_upper(I x){
    if(x.hi<unit_peak.lo){I z=x.hi;return z*(1+rt(nonneg(1-sq(z))));}
    if(x.lo>unit_peak.hi){I z=x.lo;return z*(1+rt(nonneg(1-sq(z))));}
    return area_peak;
}
bool edge(I ta,I tb,Trig angle,V A,V B,Edge& out,bool backward=false) {
    I prod=ta*tb;
    I x2= (sq(ta-tb)+2*prod*(1-angle.c))/4;
    if(x2.lo>1)return false;
    x2={std::max(0.,x2.lo),std::min(1.,x2.hi)};
    I x=rt(x2),h=rt(nonneg(1-x2));
    // P^2 = 1+t_a t_b cos(d) + h t_a t_b sin(d)/x.
    real limit=(2*rt(prod)).hi;
    I factor=backward?I(-limit,0):I(0,limit);
    if(x.lo>0){
        I tmp=prod*angle.s/x;
        factor={std::max(factor.lo,tmp.lo),std::min(factor.hi,tmp.hi)};
    }
    if(factor.lo>factor.hi)return false;
    I rad=rt(nonneg(1+prod*angle.c+h*factor));
    rad.hi=std::min({rad.hi,up(ta.hi+1),up(tb.hi+1)});
    if(rad.lo>rad.hi || rad.hi<S.lo)return false;
    out={x,h,rad,prod*angle.s/2,triangle_area_upper(x),I(.5)*(A+B),I(.5)*left(B-A)};
    return true;
}

I outer_tangent_upper(const Edge& e){
    I q(std::max(e.radius.lo,S.lo),e.radius.hi),t=q+1;
    I score=score_upper(t.hi);
    I loose=e.outer_area+cap_fan_score(score,priced_ring);
    FanDerivative derivative;
    if(e.x.lo<=0 || !fan_derivative(t.hi,derivative))return loose;
    I weight(((10*derivative.rim+derivative.area)*q/t).lo);
    if(weight.lo<=0)return loose;
    I projection=(e.x*e.h+e.inside_area)/q;
    I length=rt(nonneg(sq(e.x)+sq(weight)+2*weight*projection));
    I deficit=2*weight*nonneg(e.x-projection)/(e.x+weight+length);
    I coupled=e.outer_area+score-deficit;
    return I(std::min(loose.hi,coupled.hi));
}

I coupled_outer_upper(const Edge& edge){
    // Here both the area and the fan score depend on the same outer center.
    // Split q+1-|K| into slabs. The far-radius slab is a circular segment
    // in the unit disk centered at the outward intersection P.
    constexpr std::array<int,20> steps{0,25,50,100,150,200,280,360,450,550,680,830,
                                       1000,1200,1500,1850,2300,2900,3700,5000};
    constexpr int grid=512;
    using LossRow=std::array<real,steps.size()>;
    static const auto slab=[=]{
        std::array<I,steps.size()> values{};
        for(std::size_t k=0;k<steps.size();k++)values[k]=rat(steps[k],10000);
        return values;
    }();
    static const auto losses=[=]{
        std::vector<LossRow> table((2*grid+1)*(grid+1),LossRow{});
        for(int i=0;i<=2*grid;i++){
            I q(2.+real(i)/grid);
            for(std::size_t k=0;k+1<steps.size();k++){
                I delta=rat(steps[k+1],10000);
                I lower( (1-delta*(1+1/q)+sq(delta)/(2*q)).lo );
                I transverse=rt(nonneg(1-sq(lower)));
                for(int j=0;j<=grid;j++){
                    I cosine(real(j)/grid);
                    if(cosine.lo>=lower.lo)continue;
                    I support=lower*cosine+transverse*rt(nonneg(1-sq(cosine)));
                    table[i*(grid+1)+j][k]=std::max(0.,down(1-support.hi));
                }
            }
        }
        return table;
    }();
    real q_lower=std::max(edge.radius.lo,S.lo);
    real direction=1;
    if(edge.x.lo>0){
        I projected=(edge.h+edge.inside_area/edge.x)/I(q_lower);
        direction=std::clamp(projected.hi,0.,1.);
    }
    int i=std::clamp(static_cast<int>(std::floor(q_lower*grid))-2*grid,0,2*grid);
    int j=std::clamp(static_cast<int>(std::ceil(direction*grid)),0,grid);
    const LossRow& loss=losses[i*(grid+1)+j];
    real best=-inf;
    for(std::size_t k=0;k<steps.size();k++){
        real t=(I(edge.radius.hi)+1-slab[k]).hi;
        if(t<min_outer.lo)break;
        I score=cap_fan_score(score_upper(t),priced_ring);
        best=std::max(best,up(score.hi-down(edge.x.lo*loss[k])));
    }
    return edge.outer_area+(best==-inf?fan_ceiling:I(best));
}

bool lens_support(V v,V q,I& support){
    I q2=norm2(q);
    if(q2.lo>4)return false;
    q2.hi=std::min(4.,q2.hi);
    I nv=norm(v),nq=rt(q2),vq=dot(v,q),cross=det(q,v);
    support=I(std::min(nv.hi,(nv+vq).hi));

    // This expression equals |v| + v.q and avoids cancellation when v and q
    // are nearly antiparallel. The original bound remains available.
    I denominator=nv*nq-vq;
    if(denominator.lo>0){
        I stable=nv*(1-nq)+sq(cross)/denominator;
        support=I(std::min(support.hi,stable.hi));
    }
    if(nv.lo>0 && q2.lo>0){
        I projection=vq/nv;
        if((q2-2*projection).lo>0 && (q2+2*projection).lo>0){
            I cap=vq/2+rt(nonneg(1-q2/4))*abs_i(cross)/nq;
            support=I(std::min(support.hi,cap.hi));
        }
    }
    return true;
}

bool annular_core_support(V v,V q,I radius,I& support){
    I q2=norm2(q),limit=sq(1+radius);
    if(q2.lo>limit.hi)return false;
    q2.hi=std::min(q2.hi,limit.hi);
    I nq=rt(q2),nv=norm(v),vq=dot(v,q);
    support=I(std::min((radius*nv).hi,(nv+vq).hi));
    if(nv.lo<=0 || nq.lo<=0)return true;
    I projection=vq/nq,side=abs_i(det(q,v))/nq;
    I unit=projection/nv;
    I cut(std::max(-1.,(-nq/2).lo));
    if(unit.hi<cut.lo){
        I capped=vq+cut*projection+rt(nonneg(1-sq(cut)))*side;
        support=I(std::min(support.hi,capped.hi));
    }
    if((q2+sq(radius)-2*radius*nq*unit-1).lo>0 && (q2+1+2*nq*unit-sq(radius)).lo>0){
        I base=(q2+sq(radius)-1)/(2*nq);
        I cap=base*projection+rt(nonneg(sq(radius)-sq(base)))*side;
        support=I(std::min(support.hi,cap.hi));
    }
    return true;
}

bool central(I x,I h,V midpoint,V inward_scaled,V linear,I angle_price,I& result,
             I radius=1,bool away=false,I core_chord=1){
    V v=core_chord.lo==1&&core_chord.hi==1?inward_scaled+linear:core_chord*inward_scaled+linear;
    I sup=away?radius*norm(v):norm(v);
    if(x.lo>0){
        V q=midpoint+(h/x)*inward_scaled;
        if(away?!annular_core_support(v,q,radius,sup):!lens_support(v,q,sup))return false;
    }
    result=I(sup.hi)-angle_price*asin_lower(x.lo);
    return true;
}

bool intersect(I& a,I b){
    a.lo=std::max(a.lo,b.lo);
    a.hi=std::min(a.hi,b.hi);
    return a.lo<=a.hi;
}

struct Mixed {bool active; bool symmetric=false; bool both=false; bool shallow=false;};
const I phase_price=rat(43,10);

I radius_price(I t) {
    return rat(13,2)*(I(std::min(3.5,t.lo),std::min(3.5,t.hi))-rat(82,25))
           +4*nonneg(t-3.5);
}

constexpr int arc_mesh=2048;
const I join_price=6;
const I shallow_price=rat(5,2);
constexpr int arc_kinds=6;
using ArcBounds=std::array<real,2*arc_kinds>;

I arc_coefficient(int kind){
    return kind==4?join_price:kind==5?shallow_price:phase_price;
}

I rim_width_upper(real t){
    static const auto table=[] {
        std::array<real,mesh+1> values{};
        for(int i=0;i<=mesh;i++){
            real t=std::max(3.+real(i)/mesh,min_outer.hi);
            values[i]=t>=T.lo?M.hi:asin_i(radial_q(I(t))/R).hi;
        }
        return values;
    }();
    if(t>=T.lo)return I(M.hi);
    int i=static_cast<int>(std::ceil(t*mesh))-3*mesh;
    return i>mesh?I(M.hi):I(table[std::max(0,i)]);
}

template<class Row>
void extend_range_max(std::vector<std::vector<Row>>& values){
    std::size_t size=values.front().size();
    for(std::size_t width=2;width<=size;width*=2){
        const auto& previous=values.back();
        std::vector<Row> level(size-width+1);
        for(std::size_t i=0;i<level.size();i++){
            level[i]=previous[i];
            if constexpr(std::is_same_v<Row,real>){
                level[i]=std::max(level[i],previous[i+width/2]);
            }else{
                for(std::size_t k=0;k<level[i].size();k++)level[i][k]=std::max(level[i][k],previous[i+width/2][k]);
            }
        }
        values.push_back(std::move(level));
    }
}

const std::vector<std::vector<ArcBounds>>& shared_radius_table(){
    static const auto table=[] {
        struct RadiusCell {I t; std::array<real,arc_kinds> costs; I half_width;};
        std::vector<RadiusCell> radii;
        const real limit=rat(104,25).hi;
        for(int j=static_cast<int>(std::floor(min_outer.lo*arc_mesh));j<static_cast<int>(std::ceil(limit*arc_mesh));j++){
            I t(std::max(min_outer.lo,real(j)/arc_mesh),std::min(limit,real(j+1)/arc_mesh));
            I price=radius_price(t);
            I score=score_upper(t.hi);
            I rim=rim_width_upper(t.hi);
            radii.push_back({t,{price.hi,(score-price).hi,0,(score/2).hi,(score+join_price*rim).hi,(score/2).hi},
                             asin_mesh(2/t)});
        }
        std::vector<std::vector<ArcBounds>> values(1,std::vector<ArcBounds>(2*arc_mesh));
        for(int i=0;i<2*arc_mesh;i++){
            I q(2.+real(i)/arc_mesh,2.+real(i+1)/arc_mesh);
            auto& row=values[0][i];
            row.fill(-inf);
            for(const auto& radius:radii){
                I t=radius.t;
                I power=1-sq(t-q);
                if(power.hi<0)continue;
                I drop((nonneg(power)/(2*t*q)).hi);
                I sine=rt(nonneg(drop*(2-drop)));
                I arc=asin_mesh(sine);
                for(int k=0;k<arc_kinds;k++){
                    I coefficient=arc_coefficient(k);
                    real psi=(coefficient*arc).hi;
                    real phase=(coefficient*radius.half_width).hi;
                    row[k]=std::max(row[k],up(radius.costs[k]+psi));
                    row[k+arc_kinds]=std::max(row[k+arc_kinds],up(radius.costs[k]+phase));
                }
            }
        }
        extend_range_max(values);
        return values;
    }();
    return table;
}

// Bound the azimuth price together with the matching radial score.
bool arc_reward(const Edge& e,bool upper,int k,I& value){
    I q=e.radius;
    if(!intersect(q,I(S.lo,4)))return false;
    I py(-1,1);
    if(e.x.lo>0 && !intersect(py,e.midpoint.y-(e.h/e.x)*e.inward_scaled.y))return false;
    I phase=arc_coefficient(k)*asin_mesh((upper?py:-py)/q);
    auto index=[](real x){return std::clamp(static_cast<int>(std::floor(x*arc_mesh))-2*arc_mesh,0,2*arc_mesh-1);};
    int lo=index(q.lo),hi=index(q.hi),level=0,width=1;
    while(2*width<=hi-lo+1){width*=2;++level;}
    const auto& rows=shared_radius_table()[level];
    const auto& a=rows[lo];
    const auto& b=rows[hi-width+1];
    real arc=std::max(a[k],b[k]);
    if(arc==-inf)return false;
    real absolute=std::max(a[k+arc_kinds],b[k+arc_kinds]);
    value=I(std::min(up(phase.hi+arc),absolute));
    return true;
}

bool mixed_side(const Edge& e,bool upper,const Mixed& mixed,I& value){
    int k=mixed.active?(mixed.symmetric?(mixed.shallow?5:3):(upper?0:1)):2;
    I reward;
    if(!arc_reward(e,upper,k,reward))return false;
    value=e.inside_area+e.outer_area+reward;
    return true;
}

enum class PricedSeam {full, half, omit, inactive, inactive_no_area, inactive_phase};

I coupled_end_cost(const Edge& e,I a,I b,bool at_end,real t_lower,int rim_charge,I fallback);

bool priced_seam_upper(const Edge& e,I a,I b,PricedSeam mode,bool at_end,I& value){
    value=e.outer_area;
    if(mode==PricedSeam::inactive_no_area){value=0;return true;}
    if(mode==PricedSeam::inactive)return true;
    if(mode==PricedSeam::inactive_phase){
        if(!arc_reward(e,at_end,2,value))return false;
        value=value*(shallow_price/phase_price);
        return true;
    }
    if(mode==PricedSeam::full)value=outer_tangent_upper(e);
    if(mode==PricedSeam::half){
        I reward;
        if(!arc_reward(e,at_end,5,reward))return false;
        value=coupled_end_cost(e,a,b,at_end,min_outer.lo,0,value+reward+fan_ceiling/2)-fan_ceiling/2;
    }
    value=value-priced_ring.outer_angle*asin_lower(e.x.lo);
    return true;
}

bool join_reward(const Edge& e,I d,int flags,I& value){
    real radius=up(1+e.radius.hi);
    if(flags==0){value=score_upper(radius);return true;}
    if(flags==3){value=score_upper(radius)+2*join_price*rim_width_upper(radius)-join_price*d;return true;}
    return arc_reward(e,flags==2,4,value);
}

I normal_upper(const std::array<I,5>& x,bool& valid,int prices=1,const Mixed* mixed=nullptr,
               bool inactive=false,bool omit_outer_area=false,int joins=0,const StarPrices& star=standard_prices,
               int radial_ends=0,PricedSeam seam_mode=PricedSeam::full,I endpoint_price=rat(4,5)){
    I ta=x[0],tl=x[1],d=x[2];Trig tr=trig(d),half=trig(d/2);
    V a{ta,0},l{tl*tr.c,-tl*tr.s};
    Edge e;
    if(!edge(tl,ta,tr,l,a,e)){valid=false;return 0;}
    V linear=(-star.tilt*half.s)*V{half.c,-half.s};
    I radial=0;
    if(prices>=1){linear=linear+p_vec;radial=p_rad*ta;}
    if(prices==2){
        V el{tr.c,-tr.s};
        linear=linear+p_x*el+(-p_y)*left(el);
        radial=radial+p_rad*tl;
    }
    if(radial_ends>0)radial=radial-endpoint_price*(ta-rat(7,4));
    if(radial_ends==2)radial=radial-endpoint_price*(tl-rat(7,4));
    I local;
    if(!central(e.x,e.h,e.midpoint,e.inward_scaled,linear,star.angle,local,star.core_radius,star.away,star.core_chord)){
        valid=false;return 0;
    }
    if(star.outer_angle.lo>0){
        I seam;
        if(!priced_seam_upper(e,tl,ta,seam_mode,true,seam)){valid=false;return 0;}
        if(seam_mode==PricedSeam::full){
            I refined=coupled_outer_upper(e)-star.outer_angle*asin_lower(e.x.lo);
            seam=I(std::min(seam.hi,refined.hi));
        }
        return e.inside_area+seam+star.azimuth*d+radial+local;
    }
    if(mixed){
        I side;
        if(!mixed_side(e,true,*mixed,side)){valid=false;return 0;}
        return side+star.azimuth*d+radial+local;
    }
    I score=0;
    if(!inactive && !join_reward(e,d,joins,score)){valid=false;return 0;}
    if(joins==0)score=cap_fan_score(score,star);
    return e.inside_area+(omit_outer_area?I(0):e.outer_area)+score+star.azimuth*d+radial+local;
}

Trig signed_trig(I a){
    Trig value=trig(abs_i(a));
    if(a.lo>=0)return value;
    if(a.hi<=0)return {-value.s,value.c};
    return {{-trig(I(0,-a.lo)).s.hi,trig(I(0,a.hi)).s.hi},value.c};
}

I midpoint_block_upper(const std::array<I,5>& box,bool& valid,int prices,const Mixed* mixed=nullptr,
                       int omitted=0,int backward=0,int joins=0,const StarPrices& star=standard_prices,
                       int radial_ends=0,real cutoff=-inf,PricedSeam left_mode=PricedSeam::full,
                       PricedSeam right_mode=PricedSeam::full,I inactive_span=0,I endpoint_price=rat(4,5)){
    I m=box[0],tj=box[1],z=box[2],d=box[3],e=box[4];
    I end_rad(rat(118,100).lo,star.away?std::min((2+star.core_radius).hi,rat(3271,1000).hi):3.);
    real z_hi=std::min(up(m.hi-end_rad.lo),up(end_rad.hi-m.lo));
    if(!intersect(z,I(-z_hi,z_hi))){valid=false;return 0;}
    I ta=m-z,tb=m+z;
    if(!intersect(ta,end_rad)||!intersect(tb,end_rad)){valid=false;return 0;}
    I gaps(0,rat(953,1000).hi),d1=d+e,d2=d-e;
    if(!backward){
        real e_hi=std::min(d.hi,up(gaps.hi-d.lo));
        if(!intersect(e,I(-e_hi,e_hi))){valid=false;return 0;}
        d1=d+e;
        d2=d-e;
    }
    if(!intersect(d1,backward==1?-gaps:gaps)||!intersect(d2,backward==2?-gaps:gaps)){valid=false;return 0;}
    Trig tr=backward?signed_trig(d):trig(d),tr1=backward==1?signed_trig(d1):trig(d1);
    Trig tr2=backward==2?signed_trig(d2):trig(d2),shift=signed_trig(e);
    I s=tr.s,c=tr.c;
    I ms=m*s,zc=z*c;
    I x2=sq(ms)+sq(zc);
    if(!intersect(x2,I(0,1))){valid=false;return 0;}
    I x=rt(x2),h=rt(nonneg(1-x2));
    V v{-(m+star.tilt)*s,zc};
    if(star.core_chord.lo!=1||star.core_chord.hi!=1)v={-(star.core_chord*m+star.tilt)*s,star.core_chord*zc};
    I radial=0;
    if(prices==2){
        v.x=v.x-2*p_x*c-2*p_y*s;
        radial=-2*p_rad*m;
    }else if(prices==1){
        v.x=v.x-p_x*c-p_y*s;
        v.y=v.y+p_x*s-p_y*c;
        radial=-p_rad*ta;
    }
    if(radial_ends>0)radial=radial+endpoint_price*(ta-rat(7,4));
    if(radial_ends==2)radial=radial+endpoint_price*(tb-rat(7,4));
    I support=star.away?star.core_radius*norm(v):norm(v);
    if(x.lo>0){
        I ratio=h/x;
        V q{m*(c-ratio*s),z*(s+ratio*c)};
        if(star.away?!annular_core_support(v,q,star.core_radius,support):!lens_support(v,q,support)){
            valid=false;return 0;
        }
        V outer{m*(c+ratio*s),z*(s-ratio*c)};
        V ej=unit(shift);
        I proj=dot(outer,ej),trans=det(ej,outer);
        I r2=1-sq(trans);
        if(r2.hi<0){valid=false;return 0;}
        I r=rt(nonneg(r2));
        if(!intersect(tj,I((proj-r).lo,(proj+r).hi))){valid=false;return 0;}
    }
    if(mixed && mixed->both){
        // The core is also within two of each endpoint. This bound remains
        // informative when the base chord tends to zero.
        I diameter=2*norm(v);
        V A{ta*c,-ta*s},B{tb*c,tb*s};
        support=I(std::min({support.hi,(dot(v,A)+diameter).hi,(dot(v,B)+diameter).hi}));
    }

    Edge first,second;
    V a{},j{},j2{},b{};
    int first_joins=joins&3,second_joins=(joins>>1)&3;
    if(mixed || first_joins==1 || left_mode==PricedSeam::half || left_mode==PricedSeam::inactive_phase){
        a={ta,0};j=tj*unit(tr1);
    }
    else if(first_joins==2){a=ta*V{tr1.c,-tr1.s};j={tj,0};}
    if(second_joins==1){j2={tj,0};b=tb*unit(tr2);}
    else if(second_joins==2 || (mixed && mixed->both) || right_mode==PricedSeam::half || right_mode==PricedSeam::inactive_phase){
        j2=tj*V{tr2.c,-tr2.s};b={tb,0};
    }
    if(!edge(ta,tj,tr1,a,j,first,backward==1)||!edge(tj,tb,tr2,j2,b,second,backward==2)){valid=false;return 0;}
    I wedge=tj*(m*s*shift.c-z*c*shift.s);
    I cap_cross=2*(wedge-ta*tb*s*c);
    if(cap_cross.hi<0 || (4*sq(nonneg(cap_cross))-64*sq(first.x)*sq(second.x)*x2).hi<0){
        valid=false;return 0;
    }
    if(star.outer_angle.lo>0){
        I fixed=wedge+2*star.azimuth*d+radial+support-star.angle*asin_lower(x.lo),left,right;
        if(inactive_span.lo>0){
            if(left_mode==PricedSeam::inactive_no_area)fixed=fixed-inactive_span*d1;
            if(right_mode==PricedSeam::inactive_no_area)fixed=fixed-inactive_span*d2;
        }
        if(!priced_seam_upper(first,ta,tj,left_mode,false,left)||!priced_seam_upper(second,tj,tb,right_mode,true,right)){
            valid=false;return 0;
        }
        I loose=fixed+left+right;
        if(loose.hi<cutoff)return loose;
        if(left_mode==PricedSeam::full){
            I refined=coupled_outer_upper(first)-star.outer_angle*asin_lower(first.x.lo);
            left=I(std::min(left.hi,refined.hi));
        }
        if((fixed+left+right).hi<cutoff)return fixed+left+right;
        if(right_mode==PricedSeam::full){
            I refined=coupled_outer_upper(second)-star.outer_angle*asin_lower(second.x.lo);
            right=I(std::min(right.hi,refined.hi));
        }
        return fixed+left+right;
    }
    if(mixed){
        I side;
        if(!mixed_side(first,false,*mixed,side)){valid=false;return 0;}
        if(mixed->both){
            I right_side;
            // The second seam has the opposite azimuth sign but the same
            // share of the radial score as the first seam.
            I reward;
            if(!arc_reward(second,true,mixed->symmetric?(mixed->shallow?5:3):1,reward)){valid=false;return 0;}
            right_side=second.inside_area+second.outer_area+reward;
            return side+right_side+2*star.azimuth*d+radial+support-star.angle*asin_lower(x.lo);
        }
        I score=(omitted&2)?I(0):cap_fan_score(score_upper(up(second.radius.hi+1)),star);
        return side+second.inside_area+second.outer_area+score
               +2*star.azimuth*d+radial+support-star.angle*asin_lower(x.lo);
    }
    I first_score=0,second_score=0;
    if((!(omitted&1) && !join_reward(first,d1,first_joins,first_score)) ||
       (!(omitted&2) && !join_reward(second,d2,second_joins,second_score))){valid=false;return 0;}
    if(first_joins==0)first_score=cap_fan_score(first_score,star);
    if(second_joins==0)second_score=cap_fan_score(second_score,star);
    return wedge+first.outer_area+second.outer_area+first_score+second_score
           +2*star.azimuth*d+radial+support-star.angle*asin_lower(x.lo);
}

template<bool Crossing = false> real join_anchor_upper(I a){
    static const auto table=[] {
        struct RadiusCell {I t; real reward;};
        std::vector<RadiusCell> radii;
        real limit=rat(104,25).hi;
        for(int j=static_cast<int>(std::floor(min_outer.lo*arc_mesh));j<static_cast<int>(std::ceil(limit*arc_mesh));j++){
            I t(std::max(min_outer.lo,real(j)/arc_mesh),std::min(limit,real(j+1)/arc_mesh));
            I score=Crossing?score_upper(t.hi)/2+fan_ceiling/2:score_upper(t.hi)+join_price*rim_width_upper(t.hi);
            radii.push_back({t,score.hi});
        }
        std::vector<std::vector<real>> values(1,std::vector<real>(2*arc_mesh,-inf));
        for(int i=0;i<2*arc_mesh;i++){
            I a(1.+real(i)/arc_mesh,1.+real(i+1)/arc_mesh);
            for(const auto& radius:radii){
                I t=radius.t,power=4-sq(t-a);
                if(power.hi<0)continue;
                I drop((nonneg(power)/(2*t*a)).hi);
                I phi=drop.hi>=1?pi/2:asin_mesh(rt(nonneg(drop*(2-drop))));
                I coefficient=Crossing?shallow_price:join_price;
                values[0][i]=std::max(values[0][i],(I(radius.reward)+coefficient*phi).hi);
            }
        }
        extend_range_max(values);
        return values;
    }();
    auto index=[](real x){return std::clamp(static_cast<int>(std::floor(x*arc_mesh))-arc_mesh,0,2*arc_mesh-1);};
    int lo=index(a.lo),hi=index(a.hi),level=0,width=1;
    while(2*width<=hi-lo+1){width*=2;++level;}
    return std::max(table[level][lo],table[level][hi-width+1]);
}

template<int RimPrice=-1,bool OuterAngle=false,bool Wide=false> real crossed_side_upper(I a,int kind){
    constexpr int cells=1024;
    constexpr int anchor_cells=2*cells+(Wide?280:0);
    constexpr int side_cells=512;
    static const auto tables=[=] {
        struct OuterCell {I radius, half_score, full_score, rim_price;};
        std::vector<OuterCell> outer;
        real limit=rat(104,25).hi;
        I face_cap=OuterAngle?outer_angle_area:area_peak;
        for(int j=static_cast<int>(std::floor(min_outer.lo*cells));j<static_cast<int>(std::ceil(limit*cells));j++){
            I t(std::max(min_outer.lo,real(j)/cells),std::min(limit,real(j+1)/cells));
            I score=score_upper(t.hi),rim=0;
            if constexpr(RimPrice>=0){
                score=cap_fan_score(score,ten_ring_prices);
                if constexpr(RimPrice>0)rim=RimPrice*(M-rim_width_upper(t.hi));
            }
            outer.push_back({t,(score+fan_ceiling)/2-face_cap,score-face_cap,rim});
        }
        std::array<std::vector<std::vector<real>>,(RimPrice>=0?3:2)> result;
        for(auto& table:result)table.emplace_back(anchor_cells,-inf);
        auto face_bound=[](I side){
            I area=triangle_area_upper(side);
            if constexpr(OuterAngle){
                // One side incident to the outer site has half-length at most
                // side.hi, and the other has length at most 2.
                I upper(area.hi);
                I value=upper-priced_ring.outer_angle*asin_lower((upper/(2*I(side.hi))).lo);
                real bound=std::min(value.hi,outer_angle_area.hi);
                if(side.lo>rat(1,4).hi){
                    I turn=asin_mesh(side),stationary=asin_mesh(1/(4*side));
                    I exact=side*rt(nonneg(1-sq(side)))+rt(nonneg(sq(side)-rat(1,16)))
                        -(pi-turn-stationary)/4;
                    bound=std::min(bound,std::max(0.,exact.hi));
                }
                return I(bound);
            }
            return area;
        };
        for(int j=0;j<anchor_cells;j++){
            I a(1.+real(j)/cells,1.+real(j+1)/cells);
            for(const auto& entry:outer){
                I t=entry.radius,dist=(t-a)/2;
                if(dist.lo>1)break;
                real lowest=std::max(0.,dist.lo);
                I face=face_bound(I(lowest,1));
                real neutral=(entry.half_score+face-entry.rim_price/2).hi;
                result[0][0][j]=std::max(result[0][0][j],neutral);
                if constexpr(RimPrice>=0){
                    real full=(entry.full_score+face-entry.rim_price).hi;
                    result[2][0][j]=std::max(result[2][0][j],full);
                }
                I product=a*t,dsq=sq(dist);
                for(int k=443;k<side_cells;k++){
                    I u(k==443?lowest:std::max(lowest,real(k)/side_cells),real(k+1)/side_cells);
                    if(u.lo>u.hi)continue;
                    I phi=2*asin_mesh(rt(nonneg((sq(u)-dsq)/product)));
                    real cap=(entry.half_score+face_bound(u)+shallow_price*phi-entry.rim_price).hi;
                    result[1][0][j]=std::max(result[1][0][j],cap);
                }
            }
        }
        for(auto& table:result)extend_range_max(table);
        return result;
    }();
    auto index=[](real x){return std::clamp(static_cast<int>(std::floor(x*cells))-cells,0,anchor_cells-1);};
    int lo=index(a.lo),hi=index(a.hi),level=0,width=1;
    while(2*width<=hi-lo+1){width*=2;++level;}
    return std::max(tables[kind][level][lo],tables[kind][level][hi-width+1]);
}

enum class RootShared {none, inside, endpoint, symmetric, joined, free_middle, cross_one, cross_both, one_active_end};

I root_cap_upper(const std::array<I,3>& box,bool& valid,bool quadrilateral,int inactive,bool extra,
                 RootShared shared=RootShared::none,I t=I(0),bool shared_active=false,
                 const StarPrices& star=standard_prices,int left_charge=0,int right_charge=0){
    I m=box[0],z=box[1],d=box[2],a=m-z,b=m+z;
    I end_rad(rat(118,100).lo,star.away?std::min((2+star.core_radius).hi,rat(3271,1000).hi):3.);
    if(!intersect(a,end_rad)||!intersect(b,end_rad)){valid=false;return 0;}
    Trig half=trig(d/2);
    I ms=m*half.s,zc=z*half.c;
    I x2=sq(ms)+sq(zc);
    if(!intersect(x2,I(0,1))){valid=false;return 0;}
    I x=rt(x2),h=rt(nonneg(1-x2));
    if(!quadrilateral&&(star.core_chord.lo!=1||star.core_chord.hi!=1)){
        I local;
        if(!central(x,h,V{m*half.c,z*half.s},V{-ms,zc},V{-star.tilt*half.s,0},star.angle,local,
                    star.core_radius,star.away,star.core_chord)){
            valid=false;return 0;
        }
        return triangle_area_upper(x)+a*b*half.s*half.c+star.azimuth*d+local;
    }
    I toward(0,1);
    if(x.lo>0 && !intersect(toward,ms/x)){valid=false;return 0;}
    I qx=m*half.c-h*toward;
    I qy=z*half.s;
    if(x.lo>0)qy=qy+(h/x)*zc;
    else qy=I(-(1+star.core_radius).hi,(1+star.core_radius).hi);
    I adjustment;
    if(star.away){
        if(!annular_core_support(V{-star.tilt*half.s,0},V{qx,qy},star.core_radius,adjustment)){
            valid=false;return 0;
        }
    }else{
        if(norm2(V{qx,qy}).lo>4){valid=false;return 0;}
        adjustment=star.tilt*half.s*I(std::min(1.,up(1-qx.lo)));
    }
    bool endpoint=shared==RootShared::endpoint||shared==RootShared::symmetric;
    if(endpoint){
        if(!intersect(t,I(down(a.lo-2),up(a.hi+2)))){valid=false;return 0;}
        I power=4-sq(t-a);
        if(power.hi<0){valid=false;return 0;}
        I drop((nonneg(power)/(2*t*a)).hi);
        I phase=phase_price*asin_mesh(rt(nonneg(drop*(2-drop))));
        // Since t>2, this angular distance is acute. The coarse bound also
        // keeps the formula valid when the interval for the cosine is wide.
        I coarse=phase_price*asin_mesh(2/t);
        if(drop.hi>=1)phase=coarse;
        adjustment=adjustment+I(std::min(phase.hi,coarse.hi));
        if(shared==RootShared::endpoint){
            V v{-star.tilt*half.s-p_x*half.c-p_y*half.s,p_x*half.s-p_y*half.c};
            I support=norm(v);
            if(x.lo>0 && !lens_support(v,V{qx,qy},support)){valid=false;return 0;}
            adjustment=I(support.hi)-p_rad*a+I(std::min(phase.hi,coarse.hi));
        }
        if(shared_active){
            I score=score_upper(t.hi);
            adjustment=adjustment+(shared==RootShared::symmetric?score/2:score-radius_price(t));
        }
    }
    I angle=star.azimuth*d+adjustment-star.angle*asin_lower(x.lo);
    I base_area=triangle_area_upper(x);
    I root=2*base_area+angle;
    if(!quadrilateral)return root;

    if(shared==RootShared::one_active_end){
        return root+4*area_peak+cap_fan_score(score_upper(up(2+b.hi)),star);
    }

    if(left_charge||right_charge){
        auto end_score=[&](I radius,int charge){
            if(!charge)return cap_fan_score(score_upper(up(2+radius.hi)),star).hi;
            return star.away?crossed_side_upper<-1,false,true>(radius,charge==1)
                            :crossed_side_upper(radius,charge==1);
        };
        real l=end_score(a,left_charge),r=end_score(b,right_charge);
        if(l==-inf || r==-inf){valid=false;return 0;}
        return root+4*area_peak+I(l)+I(r)+fan_ceiling;
    }

    if(shared==RootShared::cross_one||shared==RootShared::cross_both){
        real l=join_anchor_upper<true>(a);
        real r=shared==RootShared::cross_both?join_anchor_upper<true>(b)
                                           :cap_fan_score(score_upper(up(2+b.hi)),star).hi;
        if(l==-inf || r==-inf){valid=false;return 0;}
        return root+4*area_peak+I(l)+I(r)+fan_ceiling;
    }

    if(shared==RootShared::joined && extra){
        real left=join_anchor_upper(a),right=join_anchor_upper(b);
        if(left==-inf || right==-inf){valid=false;return 0;}
        return 4+area_peak+base_area+angle-join_price*d+left+right+rat(823,250)+2*join_price*M;
    }

    I middle=fan_ceiling;
    if(!extra && shared!=RootShared::inside && shared!=RootShared::free_middle){
        I prod=a*b;
        I sine=2*half.s*half.c,cosine=1-2*sq(half.s);
        I factor(0,(2*rt(prod)).hi);
        if(x.lo>0 && !intersect(factor,prod*sine/x)){valid=false;return 0;}
        I q=rt(nonneg(1+prod*cosine+h*factor));
        q.hi=std::min({q.hi,up(a.hi+1),up(b.hi+1)});
        real limit=up(3+q.hi);
        middle=score_upper(limit);
        if(shared==RootShared::joined){
            real left=join_anchor_upper(a),right=join_anchor_upper(b);
            if(left==-inf || right==-inf){valid=false;return 0;}
            return root+4*area_peak-join_price*d+left+right+middle+2*join_price*rim_width_upper(limit);
        }
    }
    real left_score=endpoint?0:score_upper(up(2+a.hi)).hi;
    if(shared==RootShared::inside)middle=0;
    std::array<real,3> scores{left_score,score_upper(up(2+b.hi)).hi,middle.hi};
    if(star.cap_fan)for(real& score:scores)score=std::min(score,fan_ceiling.hi);
    std::sort(scores.begin(),scores.end());
    I budget=0;
    for(int i=inactive+(shared==RootShared::inside || endpoint);i<3;i++)budget=budget+scores[i];
    I area_angle=extra?4+area_peak+base_area+angle:root+4*area_peak;
    return area_angle+budget;
}

enum class Case { normal, normal_double, cap_one, cap_two };

template<std::size_t N,class Eval>
bool verify_boxes(const char* name,std::array<I,N> initial,std::array<real,N> weights,I cap,Eval eval,
                  std::uint64_t box_limit=1000000000){
    std::vector<std::array<I,N>> pending{initial};
    std::uint64_t count=0;
    while(!pending.empty()){
        auto box=pending.back();pending.pop_back();
        bool valid=true;
        I result=eval(box,valid);
        ++count;
        if(count%25000000==0)std::cout<<name<<' '<<count<<" boxes\n"<<std::flush;
        if(!valid||result.hi<cap.lo)continue;
        std::size_t axis=0;
        real width=0;
        for(std::size_t i=0;i<N;i++){
            real w=(box[i].hi-box[i].lo)*weights[i];
            if(w>width){width=w;axis=i;}
        }
        if(width<1e-7 || count>=box_limit){
            std::cerr<<"unresolved "<<name<<' '<<count<<" upper "<<std::setprecision(14)<<result.hi<<"\n";
            for(std::size_t i=0;i<N;i++)if(weights[i]>0)std::cerr<<"["<<box[i].lo<<","<<box[i].hi<<"] ";
            std::cerr<<"\n";
            return false;
        }
        real mid=box[axis].lo+(box[axis].hi-box[axis].lo)/2;
        auto other=box;
        box[axis].hi=mid;other[axis].lo=mid;
        pending.push_back(box);pending.push_back(other);
    }
    std::cout<<name<<" certified on "<<count<<" boxes\n"<<std::flush;
    return true;
}

I exact_rim_upper(real radius){
    if(radius>=T.lo)return I(M.hi);
    I t(std::max(radius,min_outer.hi));
    return I(asin_i(radial_q(t)/R).hi);
}

I span_angle(I a,I b,int reach){
    I half=rt(nonneg((reach*reach-sq(a-b))/(4*a*b)));
    return 2*asin_i(half);
}

I short_flank_span(I t,I u,I q,I pa,I pu){
    I reach=span_angle(t,q,3),via_rim=pa+pu+2*M+span_angle(u,q,1);
    return I(std::min(reach.hi,via_rim.hi))+asin_i(1/q);
}

bool verify_octagon_shared_span(bool flank){
    const I w=rat(47,40),single_cap=rat(77064,100000),paired_cap=rat(1173,1000),joined_cap=rat(712,1000);
    const I t(min_outer.lo,T.hi),radii(min_outer.lo,rat(213,50).hi),q(S.lo,rat(213,50).hi);
    const I allowance=w*(15*M-pi),gap=rat(953,1000);
    if(!verify_boxes("octagon-single-span",std::array<I,1>{t},std::array<real,1>{1},single_cap,
        [&](const auto& box,bool&){
            I a=box[0];
            I span=2*asin_i(1/(a-1));
            return I(std::min(gap.hi,span.hi))-w*(M-exact_rim_upper(a.hi));
        }))return false;
    if(!flank){
        if((2*pi-4*single_cap-paired_cap-2*joined_cap-allowance).lo<=0)return false;
        if(!verify_boxes("octagon-paired-span",std::array<I,1>{t},std::array<real,1>{1},paired_cap,
            [&](const auto& box,bool&){return 2*asin_i(2/box[0])-w*(M-exact_rim_upper(box[0].hi));}))return false;
        const I mix=rat(9,16);
        return verify_boxes("octagon-joined-single-span",std::array<I,2>{radii,q},std::array<real,2>{1,1},joined_cap,
            [&](const auto& box,bool& valid){
                I u=box[0],b=box[1];
                if(abs_i(u-b).lo>1){valid=false;return I(0);}
                I p=exact_rim_upper(u.hi),beta=asin_i(1/b),psi=span_angle(u,b,1);
                I single(std::min(gap.hi,(2*beta).hi));
                return mix*single+(1-mix)*(beta+psi+p)-w*(M-p);
            });
    }

    const I shift=rat(341,100),slope=rat(59,200),curve=rat(2,25),intercept=rat(137635,100000);
    auto envelope=[&](I a){I x=a-shift;return intercept-slope*x+curve*sq(x);};
    auto unjoined=[&](I a,I b){return span_angle(a,b,3)+asin_i(1/b)-w*(M-exact_rim_upper((b+1).hi))-envelope(a);};
    if(!verify_boxes("octagon-unjoined-flank",std::array<I,2>{t,q},std::array<real,2>{1,1},I(0),
        [&](const auto& box,bool&){
            I a=box[0],b=box[1],raw=unjoined(a,b);
            if(raw.hi<0)return raw;
            I cosine=(sq(a)+sq(b)-9)/(2*a*b),sn=rt(nonneg(1-sq(cosine))),u=b+1;
            if(sn.lo<=0||u.lo<=min_outer.hi||u.hi>=T.lo)return raw;
            I h=(T2-sq(u))/(2*u),z=rt(nonneg(1-sq(h)));
            if(z.lo<=0)return raw;
            I da=-(sq(a)-sq(b)+9)/(2*sq(a)*b*sn)+slope-2*curve*(a-shift);
            I db=-(sq(b)-sq(a)+9)/(2*sq(b)*a*sn)-1/(b*rt(sq(b)-1))+w*h/(u*z);
            I ac(a.lo+(a.hi-a.lo)/2),bc(b.lo+(b.hi-b.lo)/2);
            I mv=unjoined(ac,bc)+da*(a-ac)+db*(b-bc);
            return I(std::min(raw.hi,mv.hi));
        }))return false;
    return verify_boxes("octagon-short-rim-flank",std::array<I,3>{t,radii,q},std::array<real,3>{1,1,1},2*pi,
        [&](const auto& box,bool& valid){
            I a=box[0],u=box[1],b=box[2];
            if(abs_i(u-b).lo>1){valid=false;return I(0);}
            I pa=exact_rim_upper(a.hi),pu=exact_rim_upper(u.hi);
            return short_flank_span(a,u,b,pa,pu)-w*(2*M-pa-pu)+envelope(a)+4*single_cap+allowance;
        },1000000000);
}

bool verify_nine_two_pairs(int variant){
    const I t(min_outer.lo,T.hi),radii(min_outer.lo,rat(213,50).hi),q(S.lo,rat(213,50).hi);
    const I gap=rat(953,1000);
    auto one_dimensional=[&](const char* label,I bound,I w,int kind){
        return verify_boxes(label,std::array<I,1>{t},std::array<real,1>{1},bound,[&](const auto& box,bool&){
            I r=box[0],p=exact_rim_upper(r.hi);
            if(kind==0)return I(std::min(gap.hi,(2*asin_i(1/(r-1))).hi))-w*(M-p);
            if(kind==1)return 2*asin_i(2/r)-w*(M-p);
            return asin_i(2/r)+p-w*(M-p);
        });
    };
    if(variant==0){
        I w=rat(19,10),single=rat(73055,100000),pair=rat(112205,100000),joined=rat(69385,100000),extreme=rat(772,1000);
        I allowance=w*(14*M-pi);
        for(I cost:{3*single+2*pair+2*joined,4*single+pair+2*extreme,5*single+2*extreme})
            if((2*pi-cost-allowance).lo<=0)return false;
        if(!one_dimensional("nine-pairs-single-span",single,w,0)
           ||!one_dimensional("nine-pairs-pair-span",pair,w,1)
           ||!one_dimensional("nine-pairs-pair-extreme",extreme,w,2))return false;
        for(bool blend:{false,true}){
            I mix=blend?rat(19,30):I(0);
            if(!verify_boxes(blend?"nine-pairs-joined-singles":"nine-pairs-single-extreme",
                std::array<I,2>{radii,q},std::array<real,2>{1,1},blend?joined:extreme,
                [&](const auto& box,bool& valid){
                    I u=box[0],b=box[1];
                    if(abs_i(u-b).lo>1){valid=false;return I(0);}
                    I p=exact_rim_upper(u.hi),beta=asin_i(1/b),psi=span_angle(u,b,1);
                    return mix*I(std::min(gap.hi,(2*beta).hi))+(1-mix)*(beta+psi+p)-w*(M-p);
                }))return false;
        }
        return true;
    }
    if(variant==1){
        I w=rat(7,4),single=rat(737,1000),half=rat(1278,1000),extreme=rat(773,1000);
        I allowance=w*(14*M-pi);
        if((2*pi-4*half-single-allowance).lo<=0||(2*pi-5*single-2*extreme-2*M-allowance).lo<=0)return false;
        return one_dimensional("nine-pairs-adjacent-extreme",extreme,w,2)
            &&verify_boxes("nine-pairs-two-short-flanks",std::array<I,3>{t,radii,q},std::array<real,3>{1,1,1},half,
                [&](const auto& box,bool& valid){
                    I a=box[0],u=box[1],b=box[2];
                    if(abs_i(u-b).lo>1){valid=false;return I(0);}
                    I pa=exact_rim_upper(a.hi),pu=exact_rim_upper(u.hi);
                    return short_flank_span(a,u,b,pa,pu)-w*(M-pu)-w*(M-pa)/2;
                });
    }
    I w=rat(3,2),single=rat(749,1000),half=rat(2197,1000),mix=rat(9,20);
    if((2*pi-2*half-2*single-w*(14*M-pi)).lo<=0)return false;
    return one_dimensional("nine-pairs-middle-single-span",single,w,0)
        &&verify_boxes("nine-pairs-middle-single",std::array<I,4>{t,radii,q,q},std::array<real,4>{1,1,1,1},half,
            [&](const auto& box,bool& valid){
                I a=box[0],u=box[1],b=box[2],middle=box[3];
                if(abs_i(u-b).lo>1){valid=false;return I(0);}
                I pa=exact_rim_upper(a.hi),pu=exact_rim_upper(u.hi),pm=exact_rim_upper((middle+1).hi);
                I inner=mix*span_angle(a,middle,3)+(1-mix)*(pa+pm+2*M)-w*(M-pm)/2;
                return short_flank_span(a,u,b,pa,pu)-w*(2*M-pa-pu)+inner;
            });
}

bool verify_cap_span_prices(){
    const I w=rat(7,4),gap=rat(953,1000),single=rat(737,1000);
    const I allowance14=w*(14*M-pi),allowance15=w*(15*M-pi);
    const I double_active=rat(576,1000),mixed_active=rat(582,1000),mixed_inactive=rat(824,1000);
    const I long_active=rat(681,1000),long_inactive=rat(101,100);
    const std::array<I,8> spans{
        2*double_active+5*single+gap+allowance14,
        mixed_active+mixed_inactive+6*single+allowance14,
        2*long_active+4*single+gap+allowance14,
        long_active+long_inactive+5*single+allowance14,
        2*long_active+5*single+allowance15,
        4*double_active+4*single+allowance15,
        2*long_active+6*single+allowance14,
        6*double_active+3*single+allowance14,
    };
    for(I span:spans)if(span.hi>=(2*pi).lo)return false;
    I a((R-3).lo,rat(326,100).hi),q(S.lo,rat(213,50).hi);
    if(asin_i(1/I(a.lo)).hi>=long_inactive.lo)return false;
    if(!verify_boxes("cap-long-end-span",std::array<I,1>{a},std::array<real,1>{1},long_active,
        [&](const auto& box,bool&){
            I r=box[0];
            return asin_i(1/r)-w*(M-exact_rim_upper((r+2).hi));
        }))return false;
    auto endpoint=[&](const char* label,I mix,bool active,I bound){
        return verify_boxes(label,std::array<I,2>{a,q},std::array<real,2>{1,1},bound,
            [&](const auto& box,bool& valid){
                I r=box[0],b=box[1];
                if(abs_i(r-b).lo>1){valid=false;return I(0);}
                I local=span_angle(r,b,1)+asin_i(1/b);
                I cost=mix*I(std::min(gap.hi,local.hi))+(1-mix)*asin_i(1/r);
                if(active)cost=cost-w*(M-exact_rim_upper((b+1).hi));
                return cost;
            });
    };
    return endpoint("cap-two-active-end-span",rat(3,8),true,double_active)
        &&endpoint("cap-mixed-active-end-span",rat(19,40),true,mixed_active)
        &&endpoint("cap-mixed-inactive-end-span",rat(19,40),false,mixed_inactive);
}

bool verify_nine_cap_with_pair(){
    I w=rat(7,4),gap=rat(953,1000),single=rat(737,1000),pair=rat(1131,1000),allowance=w*(14*M-pi);
    I end=rat(681,1000),cross=rat(1311,1000),triangle=rat(1152,1000);
    I opposite=rat(60525,100000),middle=rat(12884,10000);
    for(I total:{2*end+pair+4*single,2*end+6*single,end+cross+5*single,
                 2*triangle+pair+3*single,3*triangle+pair+single,2*triangle+end+cross+2*single,
                 triangle+2*opposite+middle+3*single})
        if((2*pi-total-allowance).lo<=0)return false;

    I a((R-3).lo,rat(326,100).hi),q(S.lo,rat(213,50).hi),t(min_outer.lo,T.hi),mix=rat(3,5);
    auto anchor=[&](const char* name,I bound,bool joined){
        return verify_boxes(name,std::array<I,2>{a,q},std::array<real,2>{1,1},bound,
            [&](const auto& box,bool& valid){
                I r=box[0],b=box[1];
                if(abs_i(r-b).lo>1){valid=false;return I(0);}
                I single_angle=span_angle(r,b,1)+asin_i(1/b);
                I ray=asin_i(1/r),span(std::min(gap.hi,single_angle.hi));
                I cost=joined?span+ray:mix*span+(1-mix)*ray;
                return cost-w*(M-exact_rim_upper((b+1).hi));
            });
    };
    return anchor("nine-long-cap-crossing-pair",cross,true)
        &&anchor("nine-two-triangle-outer-end",opposite,false)
        &&verify_boxes("nine-two-triangle-paired-end",std::array<I,1>{t},std::array<real,1>{1},middle,
            [&](const auto& box,bool&){
                I u=box[0],r(std::max(a.lo,(u-2).lo));
                return 2*mix*asin_i(2/u)+2*(1-mix)*asin_i(1/r)-w*(M-exact_rim_upper(u.hi));
            });
}

bool verify_octagon_joined_cap(){
    I w=rat(3,2),single=rat(749,1000),end=rat(531,1000),mix=rat(13,20);
    if((2*pi-2*end-6*single-w*(15*M-pi)).lo<=0)return false;
    I a((R-3).lo,rat(326,100).hi),t(min_outer.lo,T.hi);
    return verify_boxes("octagon-joined-cap-end",std::array<I,2>{a,t},std::array<real,2>{1,1},end,
        [&](const auto& box,bool& valid){
            I r=box[0],u=box[1];
            if(abs_i(r-u).lo>2){valid=false;return I(0);}
            I p=exact_rim_upper(u.hi);
            return mix*asin_i(1/r)+(1-mix)*(span_angle(r,u,2)+p)-w*(M-p);
        });
}

bool verify_nine_distinct_two_caps(){
    const I w=rat(9,4),gap=rat(953,1000),single=rat(71955,100000),cap=rat(5502,10000);
    const I joined=rat(6891,10000),inside=rat(514,1000),allowance=w*(14*M-pi);
    if((2*pi-4*cap-2*joined-3*single-allowance).lo<=0
        ||(2*pi-2*cap-2*inside-5*single-allowance).lo<=0)return false;
    I a((R-3).lo,rat(326,100).hi),q(S.lo,rat(213,50).hi),t(min_outer.lo,T.hi);
    bool ordinary=verify_boxes("nine-two-caps-single-span",std::array<I,1>{t},std::array<real,1>{1},single,
        [&](const auto& box,bool&){return I(std::min(gap.hi,(2*asin_i(1/(box[0]-1))).hi))-w*(M-exact_rim_upper(box[0].hi));});
    bool ends=verify_boxes("nine-two-caps-end-span",std::array<I,2>{a,q},std::array<real,2>{1,1},cap,
        [&](const auto& box,bool& valid){
            I r=box[0],b=box[1];
            if(abs_i(r-b).lo>1){valid=false;return I(0);}
            I local=span_angle(r,b,1)+asin_i(1/b),mix=rat(69,200);
            return mix*I(std::min(gap.hi,local.hi))+(1-mix)*asin_i(1/r)-w*(M-exact_rim_upper((b+1).hi));
        });
    bool collar=verify_boxes("nine-two-caps-disjoint-join",std::array<I,2>{I(t.lo,rat(213,50).hi),q},
        std::array<real,2>{1,1},joined,[&](const auto& box,bool& valid){
            I r=box[0],b=box[1];
            if(abs_i(r-b).lo>1){valid=false;return I(0);}
            I p=exact_rim_upper(r.hi),beta=asin_i(1/b),mix=rat(131,200);
            return mix*I(std::min(gap.hi,(2*beta).hi))+(1-mix)*(beta+span_angle(r,b,1)+p)-w*(M-p);
        });
    bool ear=verify_boxes("nine-two-caps-inner-join",std::array<I,2>{a,t},std::array<real,2>{1,1},inside,
        [&](const auto& box,bool& valid){
            I r=box[0],u=box[1];
            if(abs_i(r-u).lo>2){valid=false;return I(0);}
            I p=exact_rim_upper(u.hi),mix=rat(69,100);
            return mix*asin_i(1/r)+(1-mix)*(span_angle(r,u,2)+p)-w*(M-p);
        });
    return ordinary&&ends&&collar&&ear;
}

bool verify_cap_join_endpoint(const char* label,bool cap_side,I w,I root,I join,I transfer_price,I bound,bool ear=false){
    I gap=rat(953,1000),a((R-3).lo,rat(326,100).hi),q(S.lo,rat(213,50).hi),t(min_outer.lo,rat(213,50).hi);
    return verify_boxes(label,std::array<I,3>{a,q,t},std::array<real,3>{1,1,1},bound,
        [&](const auto& box,bool& valid){
            I r=box[0],b=box[1],u=box[2];
            if(abs_i(r-b).lo>1||abs_i(u-b).lo>1){valid=false;return I(0);}
            I beta=asin_i(1/b),p=exact_rim_upper(u.hi),g=span_angle(r,b,1)+beta;
            I common=ear?-w*(rat(3,2)*M-(p+asin_i(1/u))/2):join*(beta+span_angle(u,b,1)+p)-w*(M-p);
            I span(std::min(gap.hi,g.hi)),transfer=transfer_price*(r-rat(19,10));
            if(cap_side)return common+root*asin_i(1/r)+(1-root-join)*span+transfer;
            return common+(1-join)*span-transfer;
        });
}

bool verify_nine_distinct_two_caps_zero_ends(){
    const I w=rat(9,4),gap=rat(953,1000),single=rat(71955,100000),root=rat(79,100),join=rat(12,100);
    const I ordinary=rat(665,1000),cap=rat(557,1000),far=rat(566,1000),end=ordinary+cap,allowance=w*(14*M-pi);
    if((2*pi-4*end-single-allowance).lo<=0||(2*pi-3*end-far-2*single-allowance).lo<=0)return false;
    I a((R-3).lo,rat(326,100).hi),q(S.lo,rat(213,50).hi);
    return verify_cap_join_endpoint("nine-two-caps-zero-end-ordinary",false,w,root,join,rat(1,10),ordinary)
        &&verify_cap_join_endpoint("nine-two-caps-zero-end-cap",true,w,root,join,rat(1,10),cap)
        &&verify_boxes("nine-two-caps-unilateral-far-end",
        std::array<I,2>{a,q},std::array<real,2>{1,1},far,[&](const auto& box,bool& valid){
            I r=box[0],b=box[1];
            if(abs_i(r-b).lo>1){valid=false;return I(0);}
            I g=span_angle(r,b,1)+asin_i(1/b);
            return root*asin_i(1/r)+(1-root)*I(std::min(gap.hi,g.hi))-w*(M-exact_rim_upper((b+1).hi));
        });
}

bool verify_octagon_one_cap(){
    const I w=rat(3,2),root=rat(7,10),join=rat(1,5),single=rat(749,1000),gap=rat(953,1000);
    const I ordinary=rat(686,1000),cap=rat(571,1000),regular=rat(555,1000),joined=rat(7027,10000);
    const I ear_ordinary=rat(690,1000),ear_cap=rat(508,1000),end=ordinary+cap,allowance=w*(15*M-pi);
    if((end-ear_ordinary-ear_cap).lo<=0)return false;
    for(I total:{2*end+4*single,end+regular+5*single,2*regular+2*joined+4*single})
        if((2*pi-total-allowance).lo<=0)return false;
    I a((R-3).lo,rat(326,100).hi),q(S.lo,rat(213,50).hi),t(min_outer.lo,rat(213,50).hi);
    return verify_cap_join_endpoint("octagon-cap-zero-end-ordinary",false,w,root,join,rat(1,10),ordinary)
        &&verify_cap_join_endpoint("octagon-cap-zero-end-cap",true,w,root,join,rat(1,10),cap)
        &&verify_cap_join_endpoint("octagon-cap-ear-end-ordinary",false,w,root,0,rat(3,25),ear_ordinary,true)
        &&verify_cap_join_endpoint("octagon-cap-ear-end-cap",true,w,root,0,rat(3,25),ear_cap,true)
        &&verify_boxes("octagon-cap-regular-end",std::array<I,2>{a,q},std::array<real,2>{1,1},regular,
            [&](const auto& box,bool& valid){
                I r=box[0],b=box[1];
                if(abs_i(r-b).lo>1){valid=false;return I(0);}
                I g=span_angle(r,b,1)+asin_i(1/b);
                return root*asin_i(1/r)+(1-root)*I(std::min(gap.hi,g.hi))
                    -w*(2*M-exact_rim_upper((b+1).hi)-exact_rim_upper((r+2).hi));
            })
        &&verify_boxes("octagon-cap-disjoint-join",std::array<I,2>{t,q},std::array<real,2>{1,1},joined,
            [&](const auto& box,bool& valid){
                I u=box[0],b=box[1];
                if(abs_i(u-b).lo>1){valid=false;return I(0);}
                I p=exact_rim_upper(u.hi),beta=asin_i(1/b),mix=rat(3,5);
                return mix*I(std::min(gap.hi,(2*beta).hi))+(1-mix)*(beta+span_angle(u,b,1)+p)-w*(M-p);
            });
}

const std::array<std::array<I,2>,8> fan_span_prices{{
    {I(1),rat(7864,10000)}, {rat(5,4),rat(76485,100000)}, {rat(3,2),rat(7486,10000)},
    {rat(7,4),rat(7363,10000)}, {I(6),rat(68435,100000)}, {I(10),rat(6767,10000)},
    {I(20),rat(6712,10000)}, {I(100),rat(667,1000)},
}};

bool verify_fan_span_prices(){
    I t(min_outer.lo,T.hi),gap=rat(953,1000);
    for(const auto& price:fan_span_prices){
        std::string label="fan-span-price-"+std::to_string(price[0].lo);
        if(!verify_boxes(label.c_str(),std::array<I,1>{t},std::array<real,1>{1},price[1],
            [&](const auto& box,bool&){
                I span=2*asin_i(1/(box[0]-1));
                return I(std::min(gap.hi,span.hi))-price[0]*(M-exact_rim_upper(box[0].hi));
            }))return false;
    }
    return true;
}

bool verify_octagon_long_runs(){
    I radial(min_outer.lo,T.hi);
    if((2*pi-2*asin_i(2/min_outer)-16*M).lo<=0)return false;
    struct RunBudget {
        int ordinary_count,group_count,other_fillers,reach;
        I price,ordinary,group;
        const char* name;
    };
    const std::array<RunBudget,2> cases{{
        {6,2,4,2,rat(371,100),rat(1593,1000),rat(2344,1000),"octagon-run-at-least-three"},
        {4,4,5,1,rat(712,100),rat(2401,1000),rat(2541,1000),"octagon-two-disjoint-ears"}
    }};
    for(const RunBudget& run:cases){
        I total=run.ordinary_count*run.ordinary+run.group_count*run.group-run.price*(pi-run.other_fillers*M);
        if((2*pi-total).lo<=0)return false;
        for(bool grouped:{false,true}){
            std::string label=std::string(run.name)+(grouped?"-group":"-ordinary");
            if(!verify_boxes(label.c_str(),std::array<I,1>{radial},std::array<real,1>{1},
                grouped?run.group:run.ordinary,[&](const auto& box,bool&){
                    I t=box[0],p=rim_width_upper(t.hi);
                    I reward=grouped?(p+asin_i(run.reach/t))/2:p;
                    return 2*asin_i(1/(t-1))+run.price*reward;
                }))return false;
        }
    }
    return true;
}

template<std::size_t N,class Eval>
real maximum_upper(std::array<I,N> initial,std::array<real,N> weights,real tolerance,Eval eval,real guide=-inf){
    std::vector<std::array<I,N>> pending{initial};
    real best=guide,upper=-inf;
    while(!pending.empty()){
        auto box=pending.back();pending.pop_back();
        bool valid=true;
        I bound=eval(box,valid);
        if(!valid)continue;
        if(bound.hi<=up(best+tolerance)){upper=std::max(upper,bound.hi);continue;}
        std::array<I,N> center{};
        std::size_t axis=0;
        real width=0;
        for(std::size_t i=0;i<N;i++){
            center[i]=I(box[i].lo+(box[i].hi-box[i].lo)/2);
            real w=(box[i].hi-box[i].lo)*weights[i];
            if(w>width){width=w;axis=i;}
        }
        bool center_valid=true;
        I sample=eval(center,center_valid);
        if(center_valid)best=std::max(best,sample.hi);
        if(width<1e-6||bound.hi<=up(best+tolerance)){upper=std::max(upper,bound.hi);continue;}
        auto other=box;
        box[axis].hi=center[axis].lo;other[axis].lo=center[axis].lo;
        pending.push_back(box);pending.push_back(other);
    }
    return upper;
}

struct GapPrices {
    I first_slope,second_slope,tilt,curve,empty;
    I shared=0,shared_radius=0;

    I projection_price(I z) const {
        I peak=tilt/(2*curve);
        I t(std::min(z.lo,peak.lo),std::min(z.hi,peak.hi));
        return tilt*t-curve*sq(t);
    }
};

// A path edge sees the occupancy of the two gaps at its ends.
enum class RimGap : int {plain,empty,group};
constexpr int gap_roles=3;

struct GapArcReward {
    I phase,span;
    I width,cone;
    std::vector<std::vector<real>> envelope;
    static constexpr int bins=2048;

    GapArcReward(RimGap left_gap,RimGap right_gap,I charge,bool ear,I ear_radius=0,
                 I regular_angle=0,I regular_radius=0,I shared=0,I shared_radius=0){
        auto phase_charge=[&](RimGap gap){
            if(gap==RimGap::empty)return -charge;
            if(gap==RimGap::group&&shared.hi>0)return -shared;
            return gap==RimGap::group&&!ear?I(.5):I(0);
        };
        int grouped=int(left_gap==RimGap::group)+int(right_gap==RimGap::group);
        int empty=int(left_gap==RimGap::empty)+int(right_gap==RimGap::empty);
        phase=phase_charge(left_gap)-phase_charge(right_gap);
        span=phase_charge(right_gap);
        width=1-I(.5)*grouped+empty*charge;
        cone=ear?I(.5)*grouped:I(0);
        if(left_gap==right_gap)phase=0;
        I max_radius=rat(1697,400),outer_max=rt(sq(max_radius)-1);
        I linear=0,offset=0;
        if(shared_radius.lo!=0||shared_radius.hi!=0){
            linear=(int(right_gap==RimGap::group)-int(left_gap==RimGap::group))*shared_radius;
            offset=-rat(7,2)*linear;
        }
        if(regular_angle.hi>0){
            width=width+empty*regular_angle;
            linear=-regular_radius*(2-empty)/2;
        }
        if(ear_radius.lo>0&&grouped==1){
            I u=ear_radius+1,turn=rt(sq(u)+1),mid=(min_outer+u+1)/2,chosen=rat(357,100);
            I t(std::min(mid.lo,chosen.lo),std::min(mid.hi,chosen.hi));
            if(t.lo>turn.hi&&(t-u-1).hi<0){
                I cosine=(sq(t)+sq(u)-1)/(2*t*u),sine=rt(nonneg(1-sq(cosine)));
                if(sine.lo>0){
                    I tangent=(sq(u)-1-sq(t))/(2*u*sq(t)*sine);
                    I constant=pi/2-asin_i(cosine)-tangent*t;
                    if(turn.hi>min_outer.lo)
                        constant.hi=std::max(constant.hi,(asin_i(1/min_outer)-tangent*min_outer).hi);
                    linear=tangent/2;
                    offset=constant/2;
                    cone=0;
                    outer_max.hi=std::min(outer_max.hi,(u+1).hi);
                }
            }
        }
        if(phase.lo==0&&phase.hi==0&&cone.hi==0&&linear.lo==0)return;
        // Cover each radial slice and tabulate a range maximum for later queries.
        int last=static_cast<int>(std::ceil((max_radius.hi-2)*bins));
        std::vector<real> slices(last+1,-inf);
        I phase_weight=abs_i(phase);
        for(int i=0;i<=last;i++){
            I q(2.+real(i)/bins,2.+real(i+1)/bins);
            if(!intersect(q,I(S.lo,max_radius.hi)))continue;
            I t(std::max(min_outer.lo,(q-1).lo),std::min(outer_max.hi,(q+1).hi));
            if(t.lo>t.hi)continue;
            slices[i]=maximum_upper(std::array<I,1>{t},std::array<real,1>{1},.00010,
                [&](const auto& box,bool& valid){
                    I r=box[0],sin2=1-sq(r-q);
                    if(sin2.hi<0){valid=false;return I(0);}
                    I angle=2*asin_mesh(rt(nonneg(sin2/(4*r*q))));
                    return width*rim_width_upper(r.hi)+phase_weight*angle+cone*asin_mesh(1/r)+linear*r+offset;
                });
        }
        envelope.push_back(std::move(slices));
        for(std::size_t step=1;2*step<=envelope[0].size();step*=2){
            const auto& last_layer=envelope.back();
            std::vector<real> layer(envelope[0].size()-2*step+1);
            for(std::size_t i=0;i<layer.size();i++)layer[i]=std::max(last_layer[i],last_layer[i+step]);
            envelope.push_back(std::move(layer));
        }
    }

    real radial_upper(I q) const {
        if(envelope.empty())return (width*rim_width_upper((q+1).hi)).hi;
        int first=std::max(0,static_cast<int>(std::floor(down(q.lo-2)*bins)));
        int last=std::min(static_cast<int>(envelope[0].size())-1,
                          static_cast<int>(std::floor(up(q.hi-2)*bins)));
        if(first>last)return -inf;
        int power=0,span=1;
        while(2*span<=last-first+1){span*=2;++power;}
        return std::max(envelope[power][first],envelope[power][last-span+1]);
    }
};

real regular_gap_upper(I anchor,I angle_price,I radius_price){
    I a=anchor.hi>=min_outer.lo?min_outer:I(anchor.hi);
    I outer_max=rt(sq(rat(1697,400))-1);
    I mean(min_outer.lo,outer_max.hi);
    I filler(min_outer.lo,std::min(outer_max.hi,(a+2).hi));
    if(filler.hi<filler.lo)return -inf;
    return maximum_upper(std::array<I,2>{mean,filler},std::array<real,2>{1,1},.00015,
        [&](const auto& box,bool& valid){
            I t=box[0],w=box[1],radius2=1-sq((w-a)/2);
            if(radius2.hi<0){valid=false;return I(0);}
            I h=rt(nonneg(radius2)),m=(a+w)/2,mark=rim_width_upper(w.hi);
            I span(std::min((rim_width_upper(t.hi)+mark).hi,asin_mesh((h+1)/t).hi));
            I horizontal=t*trig(span).c-m;
            if(horizontal.lo>1){valid=false;return I(0);}
            if(horizontal.lo>0){
                // At the largest possible angle, the horizontal residual
                // is positive. Separate the two cases for the vertical residual.
                I center=rt(1+a*w),cosine=(sq(t)+a*w)/(2*t*center);
                real bound=asin_mesh(h/t).hi;
                if(cosine.lo<=1){
                    I extra=2*asin_mesh(rt(nonneg((1-cosine)/2)));
                    bound=std::max(bound,(asin_mesh(h/center)+extra).hi);
                }
                span=I(std::min(span.hi,bound));
            }
            return mark+2*angle_price*span+radius_price*t;
        });
}

using GapMatrix=std::vector<real>;

GapMatrix gap_path_join(const GapMatrix& a,const GapMatrix& b,int n){
    GapMatrix result(n*n,-inf);
    for(int i=0;i<n;i++)for(int k=0;k<n;k++){
        real x=a[i*n+k];
        if(x==-inf)continue;
        for(int j=0;j<n;j++)result[i*n+j]=std::max(result[i*n+j],x+b[k*n+j]);
    }
    for(real& x:result)if(x!=-inf)x=up(x);
    return result;
}

Trig gap_bridge_trig(I half){
    if(half.hi<=2)return trig(half);
    Trig reflected=trig(pi-half);
    return {reflected.s,-reflected.c};
}

real split_gap_bridge(I a,I b,I span,int length,int ring,const GapPrices& price,real cap){
    int rest=ring-length;
    // A negative signed bridge projection only decreases the total price.
    I span_price=-price.first_slope*span-price.second_slope*(2*pi-span);
    real upper=span_price.hi;
    I diff=sq(a-b)/4,prod=a*b;
    std::vector<std::array<I,2>> pending{{span,I(0,2)}};
    while(!pending.empty()){
        auto box=pending.back();
        pending.pop_back();
        I D=box[0],g=box[1];
        Trig half=gap_bridge_trig(D/2);
        I x2=diff+prod*sq(half.s);
        if(!intersect(x2,I(0,4)))continue;
        I x=rt(x2),limit=2*rt(nonneg(1-sq(nonneg(x-1))));
        if(!intersect(g,I(0,limit.hi)))continue;
        I radius2=1-sq(nonneg(x-rt(nonneg(1-sq(g)/4))));
        if(radius2.hi<0)continue;
        I mid=(a+b)*half.c/2,radius=rt(nonneg(radius2));
        I position=mid+I(-radius.hi,radius.hi);
        I origin_strip=ring==8&&length==4?I((-g/2-1).lo,(g/2+1).hi):g/2+I(-1,1);
        if(!intersect(position,origin_strip))continue;
        I equal=(rat(length,ring)-rat(1,2))*g;
        auto joined_at=[&](I positions){
            I m(std::clamp(equal.lo,positions.lo,positions.hi),std::clamp(equal.hi,positions.lo,positions.hi));
            return (length*price.projection_price(half.s*(m+g/2)/length)
                +rest*price.projection_price(half.s*(-m+g/2)/rest)
                -price.first_slope*D-price.second_slope*(2*pi-D)).hi;
        };
        real joined=joined_at(position);
        if(ring==9&&length==5){
            // In this orientation the second core is outside the unit disk.
            I y=abs_i(a-b)*half.s/2+radius+rt(nonneg(sq(limit)-sq(g)))/2;
            if(y.hi<1){
                I horizontal=rt(1-sq(I(y.hi)));
                I low=position,high=position;
                joined=-inf;
                if(intersect(low,I(-inf,(-horizontal-g/2).hi)))joined=joined_at(low);
                if(intersect(high,I((horizontal-g/2).lo,inf)))joined=std::max(joined,joined_at(high));
            }
        }
        real dw=box[0].hi-box[0].lo,gw=box[1].hi-box[1].lo;
        if(joined<cap||joined<=upper||std::max(dw,gw)<=1./128){
            upper=std::max(upper,joined);
            continue;
        }
        int axis=dw>=gw?0:1;
        auto other=box;
        real center=box[axis].lo+(box[axis].hi-box[axis].lo)/2;
        box[axis].hi=other[axis].lo=center;
        pending.push_back(box);
        pending.push_back(other);
    }
    return upper;
}

const std::array<I,5> cap_gap_slopes{{0,rat(18,100),rat(36,100),rat(56,100),rat(82,100)}};
using CapGapSeams=std::array<std::array<GapMatrix,9>,5>;

std::vector<GapMatrix> cap_gap_matrices(const std::vector<I>& radii,int radial_steps,int first,int roles,
                                        I cap_span,I slope,const GapPrices& price,const CapGapSeams& seams,
                                        const std::vector<real>& filler_loss,bool primary_core){
    int n=static_cast<int>(radii.size());
    std::vector<GapMatrix> out(roles*roles*roles);
    for(auto& matrix:out)matrix.assign(n*n,-inf);
    struct CapAngle{I d;Trig full,half;};
    std::vector<CapAngle> angles;
    constexpr int cap_steps=128;
    for(int i=0;real(i)/cap_steps<cap_span.hi;i++){
        I d(real(i)/cap_steps,std::min(real(i+1)/cap_steps,cap_span.hi));
        angles.push_back({d,trig(d),trig(d/2)});
    }
    struct CapCell{int middle_max;std::array<real,5> adjustment;};
    std::array<GapMatrix,5> prefix;
    for(auto& p:prefix)p.resize(n);
    for(int i=0;i<n;i++)for(int j=i;j<n;j++){
        I a=radii[i],b=radii[j],mean=(a+b)/2,imbalance=(b-a)/2,prod=a*b;
        if(primary_core&&(a.lo>3||b.lo>3))continue;
        std::vector<CapCell> cells;
        cells.reserve(angles.size());
        for(const CapAngle& angle:angles){
            I x2=sq(mean*angle.half.s)+sq(imbalance*angle.half.c);
            if(!intersect(x2,I(0,1)))continue;
            I x=rt(x2),h=rt(nonneg(1-x2)),factor(0,(2*rt(prod)).hi);
            I projection=R-4;
            if(x.lo>0){
                if(!intersect(factor,prod*angle.full.s/x))continue;
                if(primary_core&&(1+prod*angle.full.c-h*factor).lo>4)continue;
                I exact=mean*angle.half.c-(h/x)*(mean*angle.half.s);
                projection=I(std::max(exact.lo,projection.lo),std::max(exact.hi,projection.hi));
            }
            I q=rt(nonneg(1+prod*angle.full.c+h*factor));
            real radial=up(std::min({q.hi,up(a.hi+1),up(b.hi+1)})+1);
            int middle_max=std::min(n-1,static_cast<int>(std::floor(radial*radial_steps))-first);
            if(middle_max<0)continue;
            I tilt=2*price.projection_price(angle.half.s*(projection-1)/2);
            CapCell cell{middle_max,{}};
            for(std::size_t k=0;k<cap_gap_slopes.size();k++)
                cell.adjustment[k]=((slope-cap_gap_slopes[k])*angle.d-tilt).hi;
            cells.push_back(cell);
        }
        if(cells.empty())continue;
        for(int u=0;u<roles;u++)for(int v=0;v<2;v++)for(int w=0;w<roles;w++){
            if(u==int(RimGap::group)&&w==int(RimGap::group))continue;
            for(std::size_t k=0;k<cap_gap_slopes.size();k++){
                const GapMatrix& left=seams[k][roles*u+v],&right=seams[k][roles*v+w];
                real mx=-inf;
                for(int j0=0;j0<n;j0++){
                    real joined=left[i*n+j0]+right[j0*n+j];
                    if(joined!=-inf){
                        joined=up(joined);
                        if(v==int(RimGap::plain)&&!filler_loss.empty())joined=up(joined+filler_loss[j0]);
                        mx=std::max(mx,joined);
                    }
                    prefix[k][j0]=mx;
                }
            }
            real upper=-inf;
            for(const CapCell& cell:cells){
                real bound=inf;
                for(std::size_t k=0;k<cap_gap_slopes.size();k++)
                    bound=std::min(bound,up(prefix[k][cell.middle_max]+cell.adjustment[k]));
                upper=std::max(upper,bound);
            }
            if(upper==-inf)continue;
            int forward=roles*(roles*u+v)+w,backward=roles*(roles*w+v)+u;
            real forward_bound=upper,backward_bound=upper;
            if(!filler_loss.empty()){
                if(w==int(RimGap::plain))forward_bound=up(upper+filler_loss[j]);
                if(u==int(RimGap::plain))backward_bound=up(upper+filler_loss[i]);
            }
            out[forward][i*n+j]=std::max(out[forward][i*n+j],forward_bound);
            out[backward][j*n+i]=std::max(out[backward][j*n+i],backward_bound);
        }
    }
    return out;
}

constexpr std::array<std::pair<int,int>,6> octagon_single_ears{{{0,2},{0,3},{0,4},{0,5},{0,6},{4,0}}};

struct NineJointCase {
    int length,cap0,cap1;
    std::vector<std::array<int,3>> remaining;
};

// Each triple gives a shared site and a pair of empty gaps after the first radial check.
const std::array<NineJointCase,8> nine_joint_cases{{
    {4,-1,-1,{{0,2,4},{0,4,6},{0,4,7}}},
    {3,3,-1,{{3,0,5},{3,1,5},{3,5,6},{3,5,7},{3,5,8},{5,0,3},{5,3,7}}},
    {4,0,2,{{2,0,4}}},
    {4,0,-1,{{0,2,4},{0,2,5},{0,2,6},{0,2,7},{0,4,6},{0,4,7},
              {2,0,4},{2,0,5},{2,0,6},{2,0,7},{2,0,8},{2,4,6},{2,4,7}}},
    {4,1,-1,{{1,3,4},{1,3,5},{1,3,6},{1,3,7},{1,3,8},
              {3,0,1},{3,1,5},{3,1,6},{3,1,7},{3,1,8}}},
    {4,4,-1,{{4,0,6},{4,1,6},{4,2,6},{4,6,8}}},
    {5,0,-1,{{0,2,5},{0,2,7}}},
    {5,5,-1,{{5,0,7},{5,1,7},{5,2,7},{5,3,7}}}
}};

enum class RimPathCase {double_fillers,ear,ear_reduction,regular,unshared_nine,shared_nine,shared_bridge_four,
                        cap_unshared_nine,cap_shared_nine,inactive_seam};

using SharedGapCells=std::array<std::array<std::array<std::vector<bool>,9>,9>,9>;

bool verify_radial_gap_patterns(int length,RimPathCase kind,int radial_steps,int angle_steps,
                                int special_edge=-1,bool ear_tangent=true,int second_cap=-1,
                                const SharedGapCells* surviving_pairs=nullptr,
                                const std::vector<std::array<int,3>>* expected=nullptr){
    bool reduced_ears=kind==RimPathCase::ear_reduction;
    bool ear=kind==RimPathCase::ear||reduced_ears,regular=kind==RimPathCase::regular;
    bool bridge_shared=kind==RimPathCase::shared_bridge_four;
    bool shared_pair=kind==RimPathCase::shared_nine||kind==RimPathCase::cap_shared_nine||bridge_shared;
    if(expected&&(!shared_pair||bridge_shared||surviving_pairs))throw std::logic_error("invalid shared reduction");
    bool inactive=kind==RimPathCase::inactive_seam;
    bool with_cap=kind==RimPathCase::cap_unshared_nine||kind==RimPathCase::cap_shared_nine;
    bool filler_discount=bridge_shared||(ear&&length==3)||surviving_pairs;
    int inactive_edge=inactive?special_edge:-1,cap_start=with_cap?special_edge:-1;
    bool nine=shared_pair||with_cap||kind==RimPathCase::unshared_nine;
    int ring=nine?9:8;
    const int rest=ring-length;
    I gap=2*asin_i(1/S),allowance=rat(7,4)*((nine||inactive?14:15)*M-pi),single=rat(737,1000);
    I off_min=2*pi-7*single-allowance;
    I min_gap=nonneg(2*pi-(ring-1-int(inactive))*single-int(inactive)*gap-allowance);
    bool off0=inactive&&inactive_edge<length,off1=inactive&&!off0;
    I cap_bonus=rat(1152,1000)-2*single,cap_span(0,(rat(1152,1000)+allowance).hi);
    auto side_cap=[&](int edges,bool off,bool cap){
        return std::min((edges*gap).hi,((edges-int(off))*single+int(off)*gap+allowance+int(cap)*cap_bonus).hi);
    };
    I side_span((2*pi-side_cap(rest,off1,with_cap&&!shared_pair&&cap_start>=length)).lo,
                side_cap(length,off0,with_cap&&!shared_pair&&cap_start<length));
    if(inactive)for(const auto& left:fan_span_prices)for(const auto& right:fan_span_prices){
        I rate=1/left[0]-1/right[0];
        if(rate.lo<=0&&rate.hi>=0)continue;
        I cap0=(length-int(off0))*left[1]+int(off0)*gap;
        I cap1=(rest-int(off1))*right[1]+int(off1)*gap;
        I split=(14*M-pi+cap0/left[0]+(cap1-2*pi)/right[0])/rate;
        if(rate.lo>0)side_span.hi=std::min(side_span.hi,split.hi);
        else side_span.lo=std::max(side_span.lo,split.lo);
    }
    I min_radius=R-3,max_radius=rat(1697,400);
    int first=static_cast<int>(std::floor(min_radius.lo*radial_steps));
    int n=static_cast<int>(std::ceil(min_outer.hi*radial_steps))-first;
    int n_bridge=3*radial_steps-first;
    constexpr int bands=8;
    const int bridge_cells=n_bridge*n_bridge*bands;
    std::vector<I> radii,bridge_radii;
    for(int i=0;i<n;i++){
        I a(real(first+i)/radial_steps,real(first+i+1)/radial_steps);
        intersect(a,I(min_radius.lo,min_outer.hi));
        radii.push_back(a);
        if(i<n_bridge)bridge_radii.push_back(a);
    }
    struct AngleCell{I angle;Trig full,half;};
    std::vector<AngleCell> angles;
    for(int i=static_cast<int>(std::floor(min_gap.lo*angle_steps));real(i)/angle_steps<gap.hi;i++){
        I d(real(i)/angle_steps,real(i+1)/angle_steps);
        if(intersect(d,I(min_gap.lo,gap.hi)))angles.push_back({d,trig(d),trig(d/2)});
    }
    struct Pattern {
        std::array<RimGap,9> gaps{};
        std::array<bool,9> regular_filler{};
        std::vector<bool> pending;
        I span;
    };
    std::vector<Pattern> patterns;
    // With a double gap there are at least two empty gaps. Select any two.
    // With a single ear at least one gap is empty. Select any one.
    if(inactive){
        Pattern pattern;
        pattern.pending.assign(bridge_cells,true);
        patterns.push_back(std::move(pattern));
    }else if(shared_pair){
        std::vector<int> groups=length==3?std::vector<int>{0,1,4,5,6}
            :length==4?std::vector<int>{0,1,2,5,6}:std::vector<int>{0,1,2,6,7};
        if(bridge_shared)groups={0};
        if(with_cap){
            groups.clear();
            for(int j=0;j<ring;j++){
                if(j==(cap_start+1)%ring||(second_cap>=0&&j==(second_cap+1)%ring))continue;
                if(second_cap>=0&&j!=cap_start&&j!=(cap_start+2)%ring&&j!=second_cap&&j!=(second_cap+2)%ring)continue;
                groups.push_back(j);
            }
        }
        auto add_pattern=[&](int group,const std::vector<int>& empty,std::vector<bool> pending){
            Pattern pattern;
            pattern.gaps[group]=RimGap::group;
            for(int z:empty)pattern.gaps[z]=RimGap::empty;
            if(filler_discount)for(int i=0;i<ring;i++)
                pattern.regular_filler[i]=pattern.gaps[i]==RimGap::plain;
            pattern.pending=std::move(pending);
            if(with_cap){
                auto span_side=[&](int start,int count){
                    I bound=count*single+allowance;
                    int before=(group+ring-1)%ring,after=group;
                    bool same=before>=start&&before<start+count&&after>=start&&after<start+count;
                    if(same)bound=bound+rat(1131,1000)-2*single;
                    for(int cap:{cap_start,second_cap})if(cap>=start&&cap+1<start+count){
                        bool touches=same&&(before==cap||before==cap+1||after==cap||after==cap+1);
                        if(!touches)bound=bound+cap_bonus;
                    }
                    return std::min(bound.hi,(count*gap).hi);
                };
                pattern.span=I((2*pi-span_side(length,rest)).lo,span_side(0,length));
            }
            patterns.push_back(std::move(pattern));
        };
        if(!surviving_pairs){
            for(int group:groups)for(int z=0;z<ring;z++)if(z!=group)for(int zz=z+1;zz<ring;zz++)if(zz!=group){
                if(bridge_shared&&!((z==2&&zz==4)||(z==4&&(zz==6||zz==7))))continue;
                add_pattern(group,{z,zz},std::vector<bool>(bridge_cells,true));
            }
        }else{
            // In each bridge cell, every pair drawn from the actual empty gaps must survive.
            for(int group:groups)for(int mask=1;mask<(1<<ring);mask++){
                if(mask&(1<<group))continue;
                std::vector<int> empty;
                for(int i=0;i<ring;i++)if(mask&(1<<i))empty.push_back(i);
                if(empty.size()<2||empty.size()>=static_cast<std::size_t>(ring-1))continue;
                std::vector<const std::vector<bool>*> tests;
                bool missing=false;
                for(std::size_t i=0;i<empty.size();i++)for(std::size_t j=i+1;j<empty.size();j++){
                    const auto& pair=(*surviving_pairs)[group][empty[i]][empty[j]];
                    missing=missing||pair.empty();
                    tests.push_back(&pair);
                }
                if(missing)continue;
                std::vector<bool> pending(bridge_cells);
                for(int p=0;p<bridge_cells;p++)pending[p]=std::all_of(tests.begin(),tests.end(),[&](auto pair){return (*pair)[p];});
                if(std::find(pending.begin(),pending.end(),true)!=pending.end())
                    add_pattern(group,empty,std::move(pending));
            }
        }
    }else if(nine){
        for(int a=0;a<9;a++)for(int b=a+1;b<9;b++)for(int c=b+1;c<9;c++)for(int d=c+1;d<9;d++){
            Pattern pattern;
            for(int k:{a,b,c,d})pattern.gaps[k]=RimGap::empty;
            pattern.pending.assign(bridge_cells,true);
            patterns.push_back(std::move(pattern));
        }
    }else for(int j: length==3?std::vector<int>{0,1,4,5}:std::vector<int>{0,1,2}){
        if(regular){
            Pattern pattern;
            pattern.gaps[j]=RimGap::empty;
            pattern.pending.assign(bridge_cells,true);
            patterns.push_back(std::move(pattern));
            continue;
        }
        for(int z=0;z<ring;z++)if(z!=j)for(int z2=ear?ring:z+1;z2<=(ear?ring:ring-1);z2++)if(z2!=j){
            Pattern pattern;
            pattern.gaps[j]=RimGap::group;
            pattern.gaps[z]=RimGap::empty;
            if(!ear)pattern.gaps[z2]=RimGap::empty;
            pattern.pending.assign(bridge_cells,true);
            if(filler_discount){
                for(int other:{(j+ring-1)%ring,(j+1)%ring})if(other!=z){
                    Pattern one=pattern;
                    for(int i=0;i<ring;i++)
                        one.regular_filler[i]=one.gaps[i]==RimGap::plain&&i!=other;
                    patterns.push_back(std::move(one));
                }
            }else patterns.push_back(std::move(pattern));
        }
    }
    if(patterns.empty())return true;
    I regular_angle=regular?rat(6,100):I(0),regular_radius=regular?rat(2,100):I(0);
    I need=regular?pi+2*pi*regular_angle:pi-(inactive?7:(ear||shared_pair)?6:5)*M;
    std::vector<GapPrices> prices{
        {rat(38,100),rat(length==3?41:38,100),rat(12,100),rat(10,100),rat(12,100)},
        {rat(32,100),rat(length==3?36:32,100),rat(105,1000),rat(9,100),rat(12,100)},
        {rat(45,100),rat(length==3?50:45,100),rat(135,1000),rat(11,100),rat(12,100)},
        {rat(41,100),rat(length==3?47:41,100),rat(105,1000),rat(9,100),rat(15,100)},
        {rat(32,100),rat(length==3?38:32,100),rat(10,100),rat(8,100),rat(15,100)},
    };
    if(inactive){
        prices.clear();
        if(inactive_edge==0)prices.push_back({rat(354,1000),rat(347,1000),rat(117,1000),rat(116,1000),0});
        if(inactive_edge==3)prices.push_back({rat(362,1000),rat(349,1000),rat(125,1000),rat(144,1000),0});
        if(inactive_edge==5)prices.push_back({rat(345,1000),rat(34,100),rat(124,1000),rat(149,1000),0});
        prices.push_back({rat(34,100),rat(35,100),rat(132,1000),rat(135,1000),0});
        prices.push_back({rat(358,1000),rat(346,1000),rat(113,1000),rat(107,1000),0});
    }else if(bridge_shared){
        prices.clear();
        for(const auto& p:std::array<std::array<int,7>,8>{{
            {290,330,135,850,160,230,100},{290,330,135,850,160,230,-100},
            {290,330,135,850,160,360,100},{290,330,135,850,160,360,-100},
            {310,350,145,850,135,290,150},{310,350,145,850,135,290,-150},
            {295,340,145,900,170,260,200},{295,340,145,900,170,260,-200}
        }})prices.push_back({rat(p[0],1000),rat(p[1],1000),rat(p[2],1000),rat(p[3]*p[2],1000000),
                             rat(p[4],1000),rat(p[5],1000),rat(p[6],1000)});
    }else if(shared_pair){
        prices.clear();
        for(const auto& p:std::array<std::array<int,5>,12>{{
            {360,400,135,160,360},{360,325,135,160,230},{290,330,85,90,230},
            {420,385,135,160,360},{420,460,135,160,360},{290,255,85,90,230},
            {360,400,85,90,360},{360,325,85,160,360},{420,460,85,90,230},
            {290,330,135,160,230},{290,255,135,160,230},{420,385,85,160,230}
        }})prices.push_back({rat(p[0],1000),rat(p[1],1000),rat(p[2],1000),rat(85*p[2],100000),
                             rat(p[3],1000),rat(p[4],1000)});
        if(with_cap)for(const auto& p:std::array<std::array<int,5>,4>{{
            {320,370,125,120,300},{350,400,150,160,360},
            {360,360,150,140,330},{390,360,150,160,320}
        }})prices.push_back({rat(p[0],1000),rat(p[1],1000),rat(p[2],1000),rat(85*p[2],100000),
                             rat(p[3],1000),rat(p[4],1000)});
    }else if(with_cap){
        prices.clear();
        for(const auto& p:std::array<std::array<int,4>,8>{{
            {320,370,125,120},{350,400,150,160},{360,360,150,140},{390,360,150,160},
            {430,430,140,200},{270,320,95,140},{300,260,90,90},{380,430,110,170}
        }})prices.push_back({rat(p[0],1000),rat(p[1],1000),rat(p[2],1000),rat(85*p[2],100000),rat(p[3],1000)});
    }else if(nine){
        prices.clear();
        for(const auto& p:std::array<std::array<int,4>,12>{{
            {350,350,150,160},{350,395,150,160},{350,310,150,160},
            {430,430,150,240},{430,390,150,240},{430,475,150,240},
            {270,315,100,160},{270,270,100,160},{270,230,100,160},
            {350,395,100,240},{350,310,100,240},{430,430,100,160}
        }})prices.push_back({rat(p[0],1000),rat(p[1],1000),rat(p[2],1000),rat(85*p[2],100000),rat(p[3],1000)});
    }
    std::vector<real> regular_bonus(n,0.);
    if(regular)for(int i=0;i<n;i++)
        regular_bonus[i]=regular_gap_upper(radii[i],regular_angle,regular_radius);
    std::array<I,bands> band_spans;
    std::array<std::vector<std::pair<I,I>>,bands> span_cells;
    real start=side_span.lo;
    for(int k=0;k<bands;k++){
        real end=k+1==bands?side_span.hi:side_span.lo+(side_span.hi-side_span.lo)*(k+1)/bands;
        band_spans[k]=I(start,end);
        for(int i=static_cast<int>(std::floor(start*angle_steps));real(i)/angle_steps<end;i++){
            I d(real(i)/angle_steps,real(i+1)/angle_steps);
            if(intersect(d,band_spans[k]))span_cells[k].emplace_back(d,gap_bridge_trig(d/2).s);
        }
        start=end;
    }
    if(with_cap&&shared_pair)for(Pattern& pattern:patterns)for(int k=0;k<bands;k++){
        I compatible=band_spans[k];
        if(!intersect(compatible,pattern.span))
            for(int p=k;p<bridge_cells;p+=bands)pattern.pending[p]=false;
    }
    auto role=[](RimGap a,RimGap b){return int(a)*gap_roles+int(b);};
    constexpr int inactive_tag=9,first_cap_tag=10;
    int cap_roles=shared_pair?3:2;
    int base_roles=with_cap?first_cap_tag+cap_roles*cap_roles*cap_roles:first_cap_tag;
    int edge_roles=(1+int(filler_discount))*base_roles;
    std::vector<real> filler_loss;
    if(filler_discount)for(I radius:radii)
        filler_loss.push_back(std::min(0.,(rim_width_upper((radius+2).hi)-M).hi));
    std::unordered_map<int,std::vector<GapArcReward>> rewards;
    std::unordered_map<int,std::vector<GapArcReward>> ear_tangents;
    for(const GapPrices& price:prices){
        int charge=1024*(1000*static_cast<int>(std::round(price.empty.lo*1000))
            +static_cast<int>(std::round(price.shared.lo*1000)))
            +static_cast<int>(std::round(price.shared_radius.lo*1000));
        auto& reward=rewards[charge];
        if(reward.empty())for(int a=0;a<gap_roles;a++)for(int b=0;b<gap_roles;b++){
            if(inactive||(((nine&&!shared_pair)||regular)&&(a==int(RimGap::group)||b==int(RimGap::group))))
                reward.emplace_back(RimGap::plain,RimGap::plain,price.empty,ear);
            else reward.emplace_back(RimGap(a),RimGap(b),price.empty,ear,0,regular_angle,regular_radius,price.shared,
                                     price.shared_radius);
        }
        auto& tangents=ear_tangents[charge];
        if(ear&&ear_tangent&&tangents.empty())for(int a=12;a<=21;a++){
            for(RimGap other:{RimGap::plain,RimGap::empty})
                tangents.emplace_back(RimGap::group,other,price.empty,true,rat(a,10));
        }
        auto radial_reward=[&](int tag,I q,I a,I b){
            RimGap start=RimGap(tag/gap_roles),end=RimGap(tag%gap_roles);
            if(ear&&ear_tangent&&(start==RimGap::group||end==RimGap::group)){
                bool group_at_start=start==RimGap::group;
                I point=group_at_start?a:b;
                int band=static_cast<int>(std::ceil(up(point.hi*10)));
                if(band>=12&&band<=21){
                    int empty=int((group_at_start?end:start)==RimGap::empty);
                    return tangents[2*(band-12)+empty].radial_upper(q);
                }
            }
            return reward[tag].radial_upper(q);
        };
        std::array<std::vector<GapMatrix>,2> edges;
        for(auto& side:edges){
            side.resize(edge_roles);
            for(auto& table:side)table.assign(n*n,-inf);
        }
        CapGapSeams cap_seams;
        if(with_cap)for(auto& slope:cap_seams)for(auto& table:slope)table.assign(n*n,-inf);
        for(int i=0;i<n;i++)for(int j=i;j<n;j++){
            I a=radii[i],b=radii[j];
            for(const AngleCell& cell:angles){
                I d=cell.angle;
                const Trig& h=cell.half;
                Edge e;
                if(!edge(a,b,cell.full,a*V{h.c,-h.s},b*unit(h),e))continue;
                I q=e.radius;
                if(!intersect(q,I(S.lo,max_radius.hi)))continue;
                if(h.s.lo>0&&!intersect(q,I(S.lo,(1/h.s).hi)))continue;
                I beta=asin_mesh(1/q);
                I phase_window((d-beta).lo,beta.hi);
                I theta,cap=R-4;
                if(e.x.lo>0){
                    I off=e.h/e.x;
                    I Py=e.midpoint.y-off*e.inward_scaled.y;
                    theta=d/2+asin_mesh(Py/q);
                    I exact=e.midpoint.x+off*e.inward_scaled.x;
                    cap=I(std::max(exact.lo,cap.lo),std::max(exact.hi,cap.hi));
                    if(!intersect(theta,phase_window))continue;
                }else theta=phase_window;
                I support2=1-sq(q*h.s);
                if(support2.hi<0)continue;
                I inverse=q*cell.full.c-2*h.c*rt(nonneg(support2));
                cap=I(std::max(cap.lo,inverse.lo),std::max(cap.hi,inverse.hi));
                I z=h.s*(cap-1);
                I tilt=price.projection_price(z);
                std::array<I,2> bases{price.first_slope*d-tilt,price.second_slope*d-tilt};
                bool primary_possible=!shared_pair||(a.lo<=3&&b.lo<=3&&(e.x.lo<=0||
                    (1+a*b*cell.full.c-e.h*a*b*cell.full.s/e.x).lo<=4));
                if(inactive){
                    I rim=rim_width_upper((q+1).hi);
                    for(int s=0;s<2;s++){
                        real& awake=edges[s][0][i*n+j];
                        awake=std::max(awake,(bases[s]+rim).hi);
                        edges[s][0][j*n+i]=awake;
                        if(d.hi>=off_min.lo){
                            real& asleep=edges[s][inactive_tag][i*n+j];
                            asleep=std::max(asleep,bases[s].hi);
                            edges[s][inactive_tag][j*n+i]=asleep;
                        }
                    }
                    continue;
                }
                for(int r=0;r<9;r++){
                    if(r==role(RimGap::group,RimGap::group))continue;
                    bool group=r/gap_roles==int(RimGap::group)||r%gap_roles==int(RimGap::group);
                    if(((nine&&!shared_pair)||regular)&&group)continue;
                    const GapArcReward& term=reward[r];
                    I base=term.span*d;
                    real rf=radial_reward(r,q,a,b),rb=ear?radial_reward(r,q,b,a):rf;
                    if(regular){
                        bool left=r/gap_roles==int(RimGap::plain),right=r%gap_roles==int(RimGap::plain);
                        auto bonus=[&](int first,int last){
                            real x=left?regular_bonus[first]:0,y=right?regular_bonus[last]:0;
                            return x==-inf||y==-inf?-inf:up(up(x+y)/2);
                        };
                        real bf=bonus(i,j),bb=bonus(j,i);
                        rb=rb==-inf||bb==-inf?-inf:up(rb+bb);
                        rf=rf==-inf||bf==-inf?-inf:up(rf+bf);
                    }
                    if(with_cap){
                        int tag=shared_pair?r:2*int(r/gap_roles==int(RimGap::empty))+int(r%gap_roles==int(RimGap::empty));
                        for(std::size_t k=0;k<cap_gap_slopes.size();k++){
                            I advance=cap_gap_slopes[k]*d+base;
                            if(rf!=-inf){
                                real& u=cap_seams[k][tag][i*n+j];
                                u=std::max(u,(advance+rf+term.phase*theta).hi);
                            }
                            if(rb!=-inf){
                                real& v=cap_seams[k][tag][j*n+i];
                                v=std::max(v,(advance+rb+term.phase*(d-theta)).hi);
                            }
                        }
                    }
                    for(int s=0;s<2;s++){
                        if(s==1&&!primary_possible)continue;
                        if(rf!=-inf){
                            real& u=edges[s][r][i*n+j];
                            u=std::max(u,(bases[s]+base+rf+term.phase*theta).hi);
                        }
                        if(rb!=-inf){
                            real& v=edges[s][r][j*n+i];
                            v=std::max(v,(bases[s]+base+rb+term.phase*(d-theta)).hi);
                        }
                    }
                }
            }
        }
        if(with_cap){
            for(int side=0;side<2;side++){
                if(int(cap_start>=length)!=side&&(second_cap<0||int(second_cap>=length)!=side))continue;
                auto caps=cap_gap_matrices(radii,radial_steps,first,cap_roles,cap_span,
                                           side?price.second_slope:price.first_slope,price,cap_seams,filler_loss,
                                           shared_pair&&side==1);
                for(std::size_t tag=0;tag<caps.size();tag++)edges[side][first_cap_tag+tag]=std::move(caps[tag]);
            }
        }
        if(filler_discount)for(auto& side:edges)for(int tag=0;tag<base_roles;tag++){
            const GapMatrix& original=side[tag];
            GapMatrix& discounted=side[base_roles+tag];
            for(int i=0;i<n;i++)for(int j=0;j<n;j++)
                if(original[i*n+j]!=-inf)discounted[i*n+j]=up(original[i*n+j]+filler_loss[j]);
        }
        std::vector<real> bridge(bridge_cells,-inf);
        for(int i=0;i<n_bridge;i++)for(int j=i;j<n_bridge;j++){
            I a=bridge_radii[i],b=bridge_radii[j],difference=sq(a-b)/4,prod=a*b;
            for(int k=0;k<bands;k++){
                real upper=-inf;
                for(const auto& cell:span_cells[k]){
                    const auto& [d,sine]=cell;
                    I x2=difference+prod*sq(sine);
                    if(!intersect(x2,I(0,4)))continue;
                    I diameter=2*rt(nonneg(1-sq(nonneg(rt(x2)-1))));
                    I upper_price=ring*price.projection_price(sine*diameter/ring);
                    upper=std::max(upper,(upper_price-price.first_slope*d-price.second_slope*(2*pi-d)).hi);
                }
                bridge[(i*n_bridge+j)*bands+k]=bridge[(j*n_bridge+i)*bands+k]=upper;
            }
        }
        std::array<std::unordered_map<std::uint64_t,GapMatrix>,2> path_cache;
        auto prefix_path=[&](auto&& self,int side,std::uint64_t key)->const GapMatrix&{
            std::uint64_t prefix=key/edge_roles;
            int tag=static_cast<int>(key%edge_roles);
            if(prefix==1)return edges[side][tag];
            auto& cache=path_cache[side];
            if(auto it=cache.find(key);it!=cache.end())return it->second;
            GapMatrix matrix=gap_path_join(self(self,side,prefix),edges[side][tag],n);
            return cache.emplace(key,std::move(matrix)).first->second;
        };
        auto path=[&](const Pattern& pattern,int side){
            int start=side?length:0,count=side?rest:length;
            std::uint64_t key=1;
            for(int k=0;k<count;k++){
                int i=start+k;
                int tag=role(pattern.gaps[i],pattern.gaps[(i+1)%ring]);
                if(inactive&&i==inactive_edge)tag=inactive_tag;
                if(with_cap&&(i==cap_start||i==second_cap)){
                    tag=first_cap_tag+cap_roles*(cap_roles*int(pattern.gaps[i])+int(pattern.gaps[(i+1)%ring]))
                        +int(pattern.gaps[(i+2)%ring]);
                    ++k;
                }
                if(tag<first_cap_tag&&filler_discount&&pattern.regular_filler[(i+1)%ring])tag+=base_roles;
                key=edge_roles*key+tag;
            }
            return &prefix_path(prefix_path,side,key);
        };
        std::vector<real> longest(bridge_cells,-inf);
        for(const Pattern& pattern:patterns){
            const GapMatrix& a=*path(pattern,0),&b=*path(pattern,1);
            for(int i=0;i<n_bridge;i++)for(int j=0;j<n_bridge;j++){
                int p=(i*n_bridge+j)*bands;
                real sum=up(a[i*n+j]+b[j*n+i]);
                for(int k=0;k<bands;k++)if(pattern.pending[p+k])longest[p+k]=std::max(longest[p+k],sum);
            }
        }
        for(int i=0;i<n_bridge;i++)for(int j=0;j<n_bridge;j++)for(int k=0;k<bands;k++){
            int p=(i*n_bridge+j)*bands+k;
            real cap=down(need.lo-longest[p]);
            if(bridge[p]>=cap&&bridge[p]<up(cap+.10)){
                real refined=split_gap_bridge(bridge_radii[i],bridge_radii[j],band_spans[k],length,ring,price,cap);
                bridge[p]=std::min(bridge[p],refined);
            }
        }
        real worst=-inf;
        std::uint64_t pending=0;
        for(Pattern& pattern:patterns){
            const GapMatrix& a=*path(pattern,0),&b=*path(pattern,1);
            for(int i=0;i<n_bridge;i++)for(int j=0;j<n_bridge;j++){
                int p=(i*n_bridge+j)*bands;
                real sum=up(a[i*n+j]+b[j*n+i]);
                for(int k=0;k<bands;k++)if(pattern.pending[p+k]){
                    real score=up(sum+bridge[p+k]);
                    worst=std::max(worst,score);
                    if(score<need.lo)pattern.pending[p+k]=false;
                    else ++pending;
                }
            }
        }
        std::cout<<"radial gap patterns "<<length<<' '<<ear<<" upper "<<std::setprecision(10)<<worst
                 <<" target "<<need.lo<<" remaining "<<pending<<'\n'<<std::flush;
        if(!pending)return true;
    }
    SharedGapCells residual;
    bool ears_match=true,pairs_match=true;
    for(const Pattern& pattern:patterns){
        std::size_t left=static_cast<std::size_t>(std::count(pattern.pending.begin(),pattern.pending.end(),true));
        if(!left)continue;
        std::cout<<"remaining pattern";
        for(int i=0;i<ring;i++)if(pattern.gaps[i]!=RimGap::plain)
            std::cout<<' '<<i<<(pattern.gaps[i]==RimGap::empty?'z':'g');
        std::cout<<": "<<left<<" cells\n";
        if(reduced_ears){
            std::pair<int,int> layout{-1,-1};
            for(int i=0;i<ring;i++){
                if(pattern.gaps[i]==RimGap::group)layout.first=i;
                if(pattern.gaps[i]==RimGap::empty)layout.second=i;
            }
            ears_match=ears_match&&std::find(octagon_single_ears.begin(),octagon_single_ears.end(),layout)
                                   !=octagon_single_ears.end();
        }
        if(shared_pair&&!bridge_shared&&!surviving_pairs){
            int group=-1;
            std::vector<int> empty;
            for(int i=0;i<ring;i++){
                if(pattern.gaps[i]==RimGap::group)group=i;
                if(pattern.gaps[i]==RimGap::empty)empty.push_back(i);
            }
            if(expected){
                std::array<int,3> key{group,empty[0],empty[1]};
                pairs_match=pairs_match&&std::find(expected->begin(),expected->end(),key)!=expected->end();
            }else residual[group][empty[0]][empty[1]]=pattern.pending;
        }
    }
    if(expected)return pairs_match;
    if(shared_pair&&!bridge_shared&&!surviving_pairs){
        std::cout<<"checking actual occupied gaps\n"<<std::flush;
        return verify_radial_gap_patterns(length,kind,radial_steps,angle_steps,special_edge,ear_tangent,second_cap,&residual);
    }
    return reduced_ears&&ears_match;
}

bool verify_nine_joint_reduction(int index){
    if(index<0||index>=static_cast<int>(nine_joint_cases.size()))throw std::logic_error("invalid nine-edge case");
    const auto& c=nine_joint_cases[index];
    bool cap=c.cap0>=0;
    return verify_radial_gap_patterns(c.length,cap?RimPathCase::cap_shared_nine:RimPathCase::shared_nine,
                                      cap?128:256,512,c.cap0,true,c.cap1,nullptr,&c.remaining);
}

struct FanHighRadius {
    I radius,seam_radius,radial_cap,half_angle,gap,single,allowance;
    std::vector<real> widths;

    FanHighRadius(I target,I span_limit)
        :radius(target),seam_radius(radius-2),radial_cap(rt(sq(radius)-1)),half_angle(asin_i(1/radius)),
         gap(2*asin_i(1/seam_radius)),single(span_limit),allowance(rat(7,4)*(15*half_angle-pi)){
        I cap_squared=sq(radius)-1;
        for(int i=0;3.+real(i)/mesh<radial_cap.lo;i++){
            I t(std::max(3.+real(i)/mesh,(radius-1).hi));
            I h=(cap_squared-sq(t))/(2*t);
            widths.push_back(asin_i(rt(nonneg(1-sq(h)))/radius).hi);
        }
    }

    I rim_width(real t) const {
        if(t>=radial_cap.lo)return I(half_angle.hi);
        int k=std::max(0,static_cast<int>(std::ceil(t*mesh))-3*mesh);
        return k<static_cast<int>(widths.size())?I(widths[k]):I(half_angle.hi);
    }
};

struct FanSpanTable {
    I slope,tilt,curve;
    bool sharp_anchor;
    std::array<std::unordered_map<int,real>,2> anchors,interior;
    const FanHighRadius* high=nullptr;
    static constexpr int steps=256;
    static constexpr int lower_steps=128;

    I price(I value) const {
        if(curve.hi==0)return tilt*value;
        I peak=tilt/(2*curve);
        I x(std::min(value.lo,peak.lo),std::min(value.hi,peak.hi));
        return tilt*x-curve*sq(x);
    }

    real upper(bool asleep,I anchor,I projection){
        bool at_bridge=anchor.lo>0;
        bool constrained=!at_bridge||projection.hi>0;
        int lo_steps=at_bridge?32:lower_steps,hi_steps=at_bridge?32:steps;
        int lo=static_cast<int>(std::floor(std::clamp(projection.lo,0.,4.)*lo_steps));
        int hi=constrained?static_cast<int>(std::ceil(std::clamp(projection.hi,0.,4.)*hi_steps)):4*hi_steps;
        int band=at_bridge?static_cast<int>(std::floor(anchor.lo*steps)):0;
        int index=(band*(4*lo_steps+1)+lo)*(4*hi_steps+1)+hi;
        auto& table=at_bridge?anchors[asleep]:interior[asleep];
        if(auto it=table.find(index);it!=table.end())return it->second;
        I a(at_bridge?real(band)/steps:0,at_bridge?real(band+1)/steps:0);
        real minimum_projection=real(lo)/lo_steps,maximum_projection=real(hi)/hi_steps;
        I w=rat(7,4),single=rat(737,1000),gap=rat(953,1000),allowance=w*(14*M-pi);
        I start=asleep?2*pi-7*single-allowance:2*pi-6*single-gap-allowance;
        I minimum_q=S,minimum_radius=R-3;
        if(high){
            gap=high->gap;
            start=2*pi-7*high->single-high->allowance;
            minimum_q=high->seam_radius;
            minimum_radius=high->radius-3;
        }
        I q(minimum_q.lo,at_bridge?std::min((a+1).hi,rat(213,50).hi):rat(213,50).hi),d(start.lo,gap.hi);
        if(q.lo>q.hi){table.emplace(index,-inf);return -inf;}
        auto evaluate=[&](const auto& box,bool& valid){
            I b=box[0],angle=box[1];
            Trig half=trig(angle/2);
            I h2=1-sq(b*half.s);
            if(h2.hi<0){valid=false;return I(0);}
            I cosine=1-2*sq(half.s),inner=b*cosine-2*half.c*rt(nonneg(h2));
            if(high){
                I radial_projection=minimum_radius-1;
                inner=I(std::max(inner.lo,radial_projection.lo),std::max(inner.hi,radial_projection.hi));
            }
            if(at_bridge){
                I ar=rt(sq(b)-1);
                ar=I(std::clamp(ar.lo,a.lo,a.hi),std::clamp(ar.hi,a.lo,a.hi));
                if(abs_i(ar-b).lo>1){valid=false;return I(0);}
                I cap=2*asin_mesh(rt(nonneg((1-sq(ar-b))/(4*ar*b))))+asin_mesh(1/b);
                if(angle.lo>cap.hi){valid=false;return I(0);}
                if(sharp_anchor){
                    I phase=(sq(a)+sq(b)-1)/(2*a*b);
                    if(!intersect(phase,I(0,1))){valid=false;return I(0);}
                    I phase_sine=rt(nonneg(1-sq(phase))),sine=2*half.s*half.c;
                    I remainder=sine*phase-cosine*phase_sine;
                    I support=1-sq(b*remainder);
                    if(support.hi<0){valid=false;return I(0);}
                    I other=b*(cosine*phase+sine*phase_sine)-rt(nonneg(support));
                    other=I(std::max(other.lo,minimum_radius.lo),std::max(other.hi,minimum_radius.hi));
                    I projection_bound=(a+other)*half.c-b*(phase*half.c+phase_sine*half.s);
                    inner=I(std::max(inner.lo,projection_bound.lo),std::max(inner.hi,projection_bound.hi));
                }
            }
            if(constrained){
                if(inner.lo>maximum_projection){valid=false;return I(0);}
                inner=I(std::max(inner.lo,minimum_projection),std::max(inner.hi,minimum_projection));
            }
            I reward=asleep?I(0):high?high->rim_width((b+1).hi):rim_width_upper((b+1).hi);
            return reward+slope*angle-price(half.s*(inner-1));
        };
        real guide=-inf;
        for(real t:{2.20,2.35,2.50,2.65,2.80,3.05})for(real delta:{.66,.72,.77,.82,.87,.92,.95}){
            if(t<q.lo||t>q.hi||delta<d.lo||delta>d.hi)continue;
            bool valid=true;
            I candidate=evaluate(std::array<I,2>{I(t),I(delta)},valid);
            if(valid)guide=std::max(guide,candidate.hi);
        }
        real value=maximum_upper(std::array<I,2>{q,d},std::array<real,2>{1,3},0.00011,evaluate,guide);
        table.emplace(index,value);
        return value;
    }
};

bool verify_high_fan_span(const FanHighRadius& target){
    return verify_boxes("high-octagon-single-span",std::array<I,1>{I((target.radius-1).lo,target.radial_cap.hi)},
        std::array<real,1>{1},target.single,[&](const auto& box,bool&){
            I t=box[0];
            return 2*asin_mesh(1/(t-1))-rat(7,4)*(target.half_angle-target.rim_width(t.hi));
        });
}

bool verify_high_octagon_fan(const FanHighRadius& target,int length){
    I s0=length==3?rat(448,1000):rat(498,1000),s1=length==3?rat(517,1000):s0;
    I v=rat(length==3?120:127,1000);
    FanSpanTable first{s0,v,0,true,{}, {},&target},second{s1,v,0,true,{}, {},&target};
    int rest=8-length;
    auto span_cap=[&](int n){return std::min((n*target.gap).hi,(n*target.single+target.allowance).hi);};
    I radial((target.radius-3).lo,3),span((2*pi-span_cap(rest)).lo,span_cap(length));
    I interior_projection(0,4);
    real normal0=first.upper(false,0,interior_projection),normal1=second.upper(false,0,interior_projection);
    std::string label="high-octagon-fan-"+std::to_string(length);
    return verify_boxes(label.c_str(),std::array<I,3>{radial,radial,span},std::array<real,3>{1,1,2},pi-7*target.half_angle,
        [&](const auto& box,bool& valid){
            I a=box[0],b=box[1],D=box[2],sine=trig(D/2).s;
            I x2=sq(a-b)/4+a*b*sq(sine);
            if(!intersect(x2,I(0,4))){valid=false;return I(0);}
            I diameter=2*rt(nonneg(1-sq(nonneg(rt(x2)-1))));
            I bound=(length-2)*I(normal0)+(rest-2)*I(normal1)+v*sine*diameter-s0*D-s1*(2*pi-D);
            for(I radius:{a,b}){
                int lo=static_cast<int>(std::floor(radius.lo*FanSpanTable::steps));
                int hi=static_cast<int>(std::floor(radius.hi*FanSpanTable::steps));
                real best=-inf;
                for(int i=lo;i<=hi;i++){
                    I bin(real(i)/FanSpanTable::steps);
                    real p=first.upper(false,bin,0),q=second.upper(false,bin,0);
                    if(p!=-inf&&q!=-inf)best=std::max(best,up(p+q));
                }
                if(best==-inf){valid=false;return I(0);}
                bound=bound+I(best);
            }
            return bound;
        });
}

bool verify_high_octagon(I radius,I single){
    FanHighRadius target(radius,single);
    return verify_high_fan_span(target)&&verify_high_octagon_fan(target,3)&&verify_high_octagon_fan(target,4);
}

I fan_direction_cap(I axis,I radius,I away){
    real r=radius.hi;
    if(away.hi>=(pi/2).lo)return I(r);
    I x(std::clamp(axis.hi,-r,r));
    Trig end=trig(I(away.hi));
    if(x.hi>=(r*end.c).lo)return I(r);
    return x*end.c+rt(nonneg(sq(I(r))-sq(x)))*end.s;
}

bool verify_octagon_fan(const char* label,int length,int inactive,I s0,I s1,I v,bool projected=false,I curve=0,
                        bool sharp=false,I span_slice=I(0,7),bool full_bridge=false,bool compressed_bridge=false){
    if(curve.hi>0&&!projected)throw std::logic_error("quadratic price requires the signed bridge projection");
    FanSpanTable inner{s0,v,curve,sharp,{}, {}},outer{s1,v,curve,sharp,{}, {}};
    I gap=rat(953,1000),single=rat(737,1000),allowance=rat(7,4)*(14*M-pi),need=pi-7*M;
    auto span_cap=[&](int n,bool asleep){return I(std::min((n*gap).hi,((n-asleep)*single+int(asleep)*gap+allowance).hi));};
    int rest=8-length;
    I a((R-3).lo,3.),span((2*pi-span_cap(rest,inactive>=length)).lo,span_cap(length,inactive<length).hi);
    for(const auto& left:fan_span_prices)for(const auto& right:fan_span_prices){
        I rate=1/left[0]-1/right[0];
        if(rate.lo<=0&&rate.hi>=0)continue;
        bool off0=inactive<length,off1=!off0;
        I left_cap=(length-off0)*left[1]+int(off0)*gap;
        I right_cap=(rest-off1)*right[1]+int(off1)*gap;
        I edge=(14*M-pi+left_cap/left[0]+(right_cap-2*pi)/right[0])/rate;
        if(rate.lo>0)span.hi=std::min(span.hi,edge.hi);
        else span.lo=std::max(span.lo,edge.lo);
    }
    if(!intersect(span,span_slice))return true;
    return verify_boxes(label,std::array<I,5>{a,a,span,I(projected?-2:0,2),full_bridge?I(-2,2):I(0)},
        std::array<real,5>{1,1,2,1,full_bridge?.75:0.},need,
        [&](const auto& box,bool& valid){
            I a0=box[0],a1=box[1],d=box[2],g=box[3];
            Trig half=trig(d/2);
            I chord=sq(a0-a1)/4+a0*a1*sq(half.s);
            if(!intersect(chord,I(0,4))){valid=false;return I(0);}
            I x=rt(chord),diameter=2*rt(nonneg(1-sq(nonneg(x-1))));
            if(projected&&!intersect(g,I(-diameter.hi,diameter.hi))){valid=false;return I(0);}
            I gy=box[4],g2=full_bridge?sq(g)+sq(gy):sq(g);
            if(full_bridge&&!intersect(g2,I(0,sq(diameter).hi))){valid=false;return I(0);}
            I h=rt(nonneg(1-g2/4)),loss=nonneg(x-h),room=1-sq(loss);
            I bridge_height=(a0+a1)*half.s/2;
            I tangential_cap=rt(nonneg(sq(diameter)-sq(g)));
            I offset_y;
            if(compressed_bridge){
                if(bridge_height.lo>1&&!intersect(g,I(0,2))){valid=false;return I(0);}
                I strip=1-nonneg(bridge_height-h);
                if(strip.hi<0){valid=false;return I(0);}
                offset_y=I(0,strip.hi);
                I threshold=nonneg(bridge_height-1);
                if(threshold.lo>0){
                    I g_square=sq(g),denominator=g_square/4+sq(threshold);
                    I tighter=g_square/denominator-g_square;
                    if(tighter.hi<0){valid=false;return I(0);}
                    tangential_cap.hi=std::min(tangential_cap.hi,rt(nonneg(tighter)).hi);
                }
            }
            bool has_lens=full_bridge&&g2.lo>0;
            V separation{};
            if(has_lens){
                V diff{(a0-a1)*half.c/2,-(a0+a1)*half.s/2};
                V n=V{gy,-g}/rt(g2);
                separation=diff-h*n;
                room.hi=std::min(room.hi,(1-norm2(separation)).hi);
            }
            if(room.hi<0){valid=false;return I(0);}
            I rho=rt(I(0,room.hi)),mid=(a0+a1)*half.c/2;
            auto lens_offset=[&](V direction){
                real radius=(rho*norm(direction)).hi;
                I support;
                if(has_lens&&lens_support(direction,2*separation,support))
                    radius=std::min(radius,(support-dot(direction,separation)).hi);
                return I(-radius,radius);
            };
            I offsets=has_lens?lens_offset(V{1,0}):I(-rho.hi,rho.hi);
            I axis0=mid+offsets+g/2,axis1=-mid+offsets+g/2;
            I radial0=1+(full_bridge?rt(g2):projected?diameter:g),lateral=0;
            if(projected)lateral=abs_i(a0-a1)*half.s/2+rho+tangential_cap/2;
            I ym=(a1-a0)*half.s/2,ys=has_lens?lens_offset(V{0,1}):offsets;
            I side0y=ym+ys+gy/2,side1y=-ym+ys+gy/2;
            if(compressed_bridge){
                real cap=std::min(rho.hi,offset_y.hi);
                I shift=I(-cap,cap)+I(-tangential_cap.hi,tangential_cap.hi)/2;
                side0y=ym+shift;
                side1y=-ym+shift;
                lateral=abs_i(ym)+abs_i(shift);
            }
            auto direction=[&](int side,I angle){
                if(abs_i(angle).hi>2)return I(0,side?2:(1+radial0).hi);
                Trig tr=signed_trig(angle);
                I ax=side?axis1:axis0,ay=side?side1y:side0y;
                real r=side?1:radial0.hi;
                if(!intersect(ax,I(-r,r))||!intersect(ay,I(-r,r)))return I(0,1+r);
                I u=1+ax*tr.c+ay*tr.s;
                if(has_lens){
                    V z=unit(tr);
                    I base=1+dot(z,V{(side?-mid:mid)+g/2,(side?-ym:ym)+gy/2});
                    I direct=base+lens_offset(z);
                    u=I(std::max(u.lo,direct.lo),std::min(u.hi,direct.hi));
                }
                return I(std::max(u.lo,down(1-r)),std::min(u.hi,up(1+r)));
            };
            I sum=-2*pi*s1-(s0-s1)*d;
            if(curve.hi==0)sum=sum+v*half.s*g;
            else{
                I projection=mid+offsets;
                if(!intersect(projection,g/2+I(-1,1))){valid=false;return I(0);}
                I equal=(rat(length,8)-rat(1,2))*g;
                I m(std::clamp(equal.lo,projection.lo,projection.hi),std::clamp(equal.hi,projection.lo,projection.hi));
                sum=sum+length*inner.price(half.s*(m+g/2)/length)+rest*outer.price(half.s*(-m+g/2)/rest);
            }
            for(int end=0;end<2;end++){
                I r=end?a1:a0;
                bool off0=inactive==(end?length-1:0),off1=inactive==(end?length:7);
                I p0=0,p1=0;
                if(full_bridge||compressed_bridge){
                    auto edge_angle=[&](bool asleep){return I((asleep?2*pi-7*single-allowance:
                        2*pi-6*single-gap-allowance).lo,gap.hi);};
                    I o0=(d-edge_angle(off0))/2,o1=(2*pi-d-edge_angle(off1))/2;
                    p0=direction(0,end?o0:-o0);
                    p1=direction(1,end?-o1:o1);
                }
                int lo=static_cast<int>(std::floor(r.lo*FanSpanTable::steps));
                int hi=static_cast<int>(std::floor(r.hi*FanSpanTable::steps));
                real bound=-inf;
                for(int j=lo;j<=hi;j++){
                    I band(real(j)/FanSpanTable::steps);
                    real left=inner.upper(off0,band,p0),right=outer.upper(off1,band,p1);
                    if(left!=-inf&&right!=-inf)bound=std::max(bound,up(left+right));
                }
                if(bound==-inf){valid=false;return I(0);}
                sum=sum+I(bound);
            }
            for(int side=0;side<2;side++){
                int n=side?rest:length;
                I arc=side?2*pi-d:d,axis=side?axis1:axis0,radius=side?I(1):radial0;
                for(int j=1;j<n-1;j++){
                    I offset=nonneg(rat(2*std::max(j,n-j-1)+1,2)*gap-arc/2);
                    real hi=(1+fan_direction_cap(axis,radius,offset)).hi,lo=0;
                    if(projected&&offset.hi<(pi/2).lo){
                        Trig tr=trig(I(offset.hi));
                        I azimuth=axis*I(tr.c.lo,1);
                        lo=(1+azimuth-I(std::min(lateral.hi,radius.hi))*tr.s).lo;
                    }
                    I projection(lo,hi);
                    if(full_bridge||compressed_bridge){
                        I angle((arc/2-rat(2*n-2*j-1,2)*gap).lo,(rat(2*j+1,2)*gap-arc/2).hi);
                        I precise=direction(side,angle);
                        if(!intersect(projection,precise)){valid=false;return I(0);}
                    }
                    real bound=(side?outer:inner).upper(inactive==j+(side?length:0),0,projection);
                    if(bound==-inf){valid=false;return I(0);}
                    sum=sum+I(bound);
                }
            }
            return sum;
        });
}

bool verify_octagon_fan_interior_inactive(bool near_primary){
    if(near_primary)return verify_octagon_fan("octagon-fan-inner-inactive-primary",4,5,rat(33,100),rat(34,100),rat(73,1000));
    return verify_octagon_fan("octagon-fan-inner-inactive-secondary",4,1,rat(367,1000),rat(357,1000),rat(76,1000));
}

bool verify_octagon_fan_bridge_four(bool near_primary,int part,bool compressed_bridge=false){
    struct Band {int lo,hi,s0,s1,v;};
    const std::array<Band,5> secondary{{{0,303,250,520,60}, {303,316,300,400,75},
        {316,329,350,350,60}, {329,341,400,300,75}, {341,700,520,250,75}}};
    const std::array<Band,5> primary{{{0,290,250,520,75}, {290,303,300,400,60},
        {303,316,350,300,60}, {316,329,400,250,60}, {329,700,520,250,60}}};
    const auto& bands=near_primary?primary:secondary;
    if(part<-1||part>=static_cast<int>(bands.size()))return false;
    for(int j=0;j<static_cast<int>(bands.size());j++){
        if(part>=0&&j!=part)continue;
        const Band& p=bands[j];
        std::string label=std::string("octagon-fan-four-bridge-")+(near_primary?"primary-":"secondary-")+std::to_string(j);
        if(!verify_octagon_fan(label.c_str(),4,near_primary?4:0,rat(p.s0,1000),rat(p.s1,1000),rat(p.v,1000),
            true,0,true,I(rat(p.lo,100).lo,rat(p.hi,100).hi),near_primary&&j==2&&!compressed_bridge,compressed_bridge))return false;
    }
    return true;
}

bool verify(Case kind){
    const bool block=kind==Case::cap_one || kind==Case::cap_two;
    const bool double_price=kind==Case::normal_double || kind==Case::cap_two;
    const char* name=block?(double_price?"cap-two":"cap-one")
                          :(double_price?"normal-double":"normal");
    int dims=block?5:3, radii=block?3:2;
    std::array<I,5> initial{};
    for(int i=0;i<dims;i++)initial[i]=i<radii?I(rat(118,100).lo,3.25):I(0,rat(953,1000).hi);
    if(block){
        real delta=rat(91,100).hi,shift=rat(953,2000).hi;
        initial={I(rat(118,100).lo,3.),I(rat(118,100).lo,rat(3271,1000).hi),
                 I(double_price?0:-delta,delta),I(0,rat(953,1000).hi),I(-shift,shift)};
    }
    I cap=block?(double_price?cap_block:I(27)):(double_price?rat(-35,100):cap_normal);
    std::array<real,5> weights{};
    for(int i=0;i<dims;i++)weights[i]=i<radii?1:4;
    return verify_boxes(name,initial,weights,cap,[&](const auto& box,bool& valid){
        return block?midpoint_block_upper(box,valid,double_price?2:1):normal_upper(box,valid,double_price?2:1);
    });
}

bool verify_mixed(bool block,bool active,bool other_inactive=false){
    const char* name=block?(other_inactive?(active?"mixed-cap-other-inactive":"mixed-cap-both-inactive")
                                          :(active?"mixed-cap":"mixed-cap-inactive"))
                          :(active?"mixed-normal":"mixed-normal-inactive");
    const I end_rad(rat(118,100).lo,3.), gap(0,rat(953,1000).hi);
    const real delta=rat(91,100).hi,shift=rat(953,2000).hi;
    Mixed mixed{active};
    if(!block){
        std::array<I,3> initial{end_rad,end_rad,gap};
        I cap=active?rat(246,100):rat(601,200);
        return verify_boxes(name,initial,std::array<real,3>{1,1,4},cap,[&](const auto& box,bool& valid){
            return normal_upper({box[0],box[1],box[2],I(0),I(0)},valid,1,&mixed);
        });
    }
    std::array<I,5> initial{end_rad,I(end_rad.lo,rat(3271,1000).hi),I(-delta,delta),gap,I(-shift,shift)};
    I cap=other_inactive?(active?I(30):rat(285,10)):(active?rat(318,10):rat(2982,100));
    return verify_boxes(name,initial,std::array<real,5>{1,1,1,4,4},cap,[&](const auto& box,bool& valid){
        return midpoint_block_upper(box,valid,2,&mixed,other_inactive?2:0);
    });
}

bool verify_cap_partition(int length,int inactive,bool extra=false,int prices=0){
    const I end_rad(rat(118,100).lo,3.), gap(0,rat(953,1000).hi);
    const real delta=rat(91,100).hi,shift=rat(953,2000).hi;
    if(length==1){
        std::array<I,3> initial{end_rad,end_rad,gap};
        const char* name=prices?"priced-normal-inactive":"ordinary-inactive";
        I cap=prices?rat(1123,250):rat(513,50);
        return verify_boxes(name,initial,std::array<real,3>{1,1,4},cap,
            [&](const auto& box,bool& valid){
                return normal_upper({box[0],box[1],box[2],I(0),I(0)},valid,prices,nullptr,true);
            });
    }
    if(length==2){
        std::array<I,5> initial{end_rad,I(end_rad.lo,rat(3271,1000).hi),
                               I(inactive==1?-delta:0,delta),gap,I(-shift,shift)};
        const auto caps=prices?std::array<I,3>{cap_block,rat(307,10),rat(297,10)}
                              :std::array<I,3>{rat(2147,100),rat(202,10),rat(1912,100)};
        const char* name=prices?(inactive==1?"cap-two-one-inactive":"cap-two-two-inactive")
                               :(inactive==0?"triangle-cap":inactive==1?"triangle-cap-one-inactive":"triangle-cap-two-inactive");
        return verify_boxes(name,initial,std::array<real,5>{1,1,1,4,4},caps[inactive],
            [&](const auto& box,bool& valid){return midpoint_block_upper(box,valid,prices,nullptr,(1<<inactive)-1);});
    }
    std::array<I,3> initial{end_rad,I(0,delta),I(0,rat(203,100).hi)};
    const std::array<I,3> caps{rat(3042,100),rat(301,10),rat(2919,100)};
    const char* name=extra?(inactive==0?"quadrilateral-extra":inactive==1?"quadrilateral-extra-one-inactive"
                                         :"quadrilateral-extra-two-inactive")
                          :(length==3?(inactive==0?"quadrilateral-cap":inactive==1?"quadrilateral-cap-one-inactive"
                                                   :"quadrilateral-cap-two-inactive"):"long-cap-root");
    return verify_boxes(name,initial,std::array<real,3>{1,1,4},length==3?caps[inactive]:rat(2066,100),
        [&](const auto& box,bool& valid){return root_cap_upper(box,valid,length==3,inactive,extra);});
}

bool verify_reverse_cap(int omitted,const StarPrices& star=standard_prices,I limit=I(16)){
    const I end_rad(rat(118,100).lo,3.);
    const real delta=rat(91,100).hi,half_gap=rat(953,2000).hi;
    std::array<I,5> initial{end_rad,I(end_rad.lo,rat(3271,1000).hi),I(-delta,delta),
                           I(-half_gap,half_gap),I(-rat(953,1000).hi,0)};
    const char* name=omitted==0?"reverse-cap":omitted==1?"reverse-cap-first-inactive":"reverse-cap-second-inactive";
    return verify_boxes(name,initial,std::array<real,5>{1,1,1,4,4},omitted?rat(154,10):limit,
        [&](const auto& box,bool& valid){return midpoint_block_upper(box,valid,0,nullptr,omitted,true,0,star);});
}

bool verify_shared_triangle(bool symmetric,bool active,int inactive){
    const I end_rad(rat(118,100).lo,3.),gap(0,rat(953,1000).hi);
    const real delta=rat(91,100).hi,shift=rat(953,2000).hi;
    std::array<I,5> initial{end_rad,I(end_rad.lo,rat(3271,1000).hi),I(-delta,delta),gap,I(-shift,shift)};
    const int caps[2][2][2]={{{2490,2370},{2632,2515}},{{1922,1814},{1972,1851}}};
    Mixed mixed{active,symmetric};
    std::string name=std::string(symmetric?"shared-triangle-symmetric":"shared-triangle-ordinary")
        +(active?"-active-":"-inactive-")+std::to_string(inactive);
    return verify_boxes(name.c_str(),initial,std::array<real,5>{1,1,1,4,4},rat(caps[symmetric][active][inactive],100),
        [&](const auto& box,bool& valid){return midpoint_block_upper(box,valid,symmetric?0:1,&mixed,inactive?2:0);});
}

bool verify_shared_quad(RootShared shared,bool active,int inactive){
    const I end_rad(rat(118,100).lo,3.);
    const real delta=rat(91,100).hi;
    I gap(0,rat(203,100).hi);
    std::string name=std::string(shared==RootShared::inside?"shared-quad-inside":
        shared==RootShared::endpoint?"shared-quad-ordinary":"shared-quad-symmetric")
        +(active?"-active-":"-inactive-")+std::to_string(inactive);
    if(shared==RootShared::inside){
        const int caps[]={2715,2650,2588};
        std::array<I,3> initial{end_rad,I(0,delta),gap};
        return verify_boxes(name.c_str(),initial,std::array<real,3>{1,1,4},rat(caps[inactive],100),
            [&](const auto& box,bool& valid){return root_cap_upper(box,valid,true,inactive,false,shared);});
    }
    const int caps[2][2][3]={{{3482,3418,3086},{3599,3533,3200}},{{3020,2957,2630},{3037,2974,2644}}};
    std::array<I,4> initial{end_rad,I(-delta,delta),gap,I(min_outer.lo,rat(104,25).hi)};
    return verify_boxes(name.c_str(),initial,std::array<real,4>{1,1,4,1},
        rat(caps[shared==RootShared::symmetric][active][inactive],100),[&](const auto& box,bool& valid){
            return root_cap_upper({box[0],box[1],box[2]},valid,true,inactive,false,shared,box[3],active);
        });
}

real annular_support(I vx,I vy,I norm_sq,I floor,I ceiling){
    I top=vy+1;
    real highest=-inf;
    I top_norm=norm_sq+2*vy+1;
    if(top_norm.hi>=sq(floor).lo && top_norm.lo<=sq(ceiling).hi)highest=top.hi;
    if((sq(vx)+sq(ceiling-vy)).lo<=1)highest=std::max(highest,ceiling.hi);
    for(I radius:{floor,ceiling}){
        I a=norm_sq,lower=sq(radius-1),upper=sq(radius+1);
        if(!intersect(a,I(lower.lo,upper.hi)))continue;
        I height=rt(nonneg((upper-a)*(a-lower)));
        I y=((sq(radius)+a-1)*vy+abs_i(vx)*height)/(2*a);
        highest=std::max(highest,y.hi);
    }
    return std::min({top.hi,ceiling.hi,highest});
}

bool verify_annular_pair(){
    I cutoff=rat(213,50),cap=rat(1897,1000);
    I radial(min_outer.lo,rt(sq(cutoff)-1).hi);
    std::array<I,4> initial{I(R.lo,cutoff.hi),radial,radial,I((cap/4).lo,1)};
    return verify_boxes("annular-outer-pair",initial,std::array<real,4>{2,1,1,2},cap,
        [](const auto& box,bool& valid){
            I big=box[0],a=box[1],b=box[2],z=box[3];
            I floor=big-1,ceiling=rt(sq(big)-1);
            I radial_domain(floor.lo,ceiling.hi);
            if(!intersect(a,radial_domain)||!intersect(b,radial_domain)||a.lo>b.hi){valid=false;return I(0);}
            a.hi=std::min(a.hi,b.hi);
            b.lo=std::max(b.lo,a.lo);
            I a2=sq(a),b2=sq(b),mx=(b2-a2)/(4*z),base=mx-z;
            I y2=a2-sq(base);
            if(y2.hi<0){valid=false;return I(0);}
            I my=rt(nonneg(y2)),h=rt(nonneg(1-sq(z)));
            I norm_domain(sq(a-1).lo,sq(a+1).hi);
            I total=0;
            for(int side:{1,-1}){
                I vy=side*my+h;
                I norm_sq=a2+1+2*z*base+2*side*h*my;
                if(!intersect(norm_sq,norm_domain)){valid=false;return I(0);}
                real bound=annular_support(mx,vy,norm_sq,floor,ceiling);
                if(bound==-inf){valid=false;return I(0);}
                total=total+bound;
            }
            return z*total;
        });
}

bool verify_inactive_without_area(int prices){
    I radial(rat(118,100).lo,3.);
    std::array<I,3> initial{radial,radial,I(0,rat(953,1000).hi)};
    return verify_boxes(prices?"priced-inactive-without-area":"inactive-without-area",initial,
        std::array<real,3>{1,1,4},prices?rat(358,100):rat(932,100),[&](const auto& box,bool& valid){
            return normal_upper({box[0],box[1],box[2],I(0),I(0)},valid,prices,nullptr,true,true);
        });
}

bool verify_spaced_normal(int flags){
    I radial(rat(118,100).lo,3.);
    std::array<I,3> initial{radial,radial,I(0,rat(953,1000).hi)};
    return verify_boxes(flags==2?"one-joined-normal":"two-joined-normal",initial,std::array<real,3>{1,1,4},
        flags==2?rat(1077,100):rat(936,100),[&](const auto& box,bool& valid){
            return normal_upper({box[0],box[1],box[2],I(0),I(0)},valid,0,nullptr,false,false,flags);
        });
}

bool verify_spaced_triangle(int joins){
    I radial(rat(118,100).lo,3.),gap(0,rat(953,1000).hi);
    real delta=rat(91,100).hi,shift=rat(953,2000).hi;
    std::array<I,5> initial{radial,I(radial.lo,rat(3271,1000).hi),I(0,delta),gap,I(-shift,shift)};
    std::string name="joined-triangle-"+std::to_string(joins);
    return verify_boxes(name.c_str(),initial,std::array<real,5>{1,1,1,4,4},joins==2?rat(199,10):rat(221,10),
        [&](const auto& box,bool& valid){return midpoint_block_upper(box,valid,0,nullptr,0,false,joins);});
}

bool verify_spaced_quad(bool extra){
    std::array<I,3> initial{I(rat(118,100).lo,3.),I(0,rat(91,100).hi),I(0,rat(203,100).hi)};
    return verify_boxes(extra?"joined-quad-extra":"joined-quad-internal",initial,std::array<real,3>{1,1,4},rat(298,10),
        [&](const auto& box,bool& valid){return root_cap_upper(box,valid,true,0,extra,RootShared::joined);});
}

bool verify_ten_ring(int length,int omitted=0,bool extra=false){
    I radial(rat(118,100).lo,3.),gap(0,rat(953,1000).hi);
    real delta=rat(91,100).hi,shift=rat(953,2000).hi;
    if(length==1){
        std::array<I,3> initial{radial,radial,gap};
        return verify_boxes(omitted?"ten-ring-normal-omit":"ten-ring-normal",initial,std::array<real,3>{1,1,4},
            omitted?rat(567,100):rat(735,100),[&](const auto& box,bool& valid){
                return normal_upper({box[0],box[1],box[2],I(0),I(0)},valid,0,nullptr,omitted>0,false,0,ten_ring_prices);
            });
    }
    if(length==2){
        std::array<I,5> initial{radial,I(radial.lo,rat(3271,1000).hi),I(omitted==1?-delta:0,delta),gap,I(-shift,shift)};
        const int caps[]={1476,1290,1133};
        const char* name=omitted==0?"ten-ring-triangle":omitted==1?"ten-ring-triangle-omit-1":"ten-ring-triangle-omit-2";
        return verify_boxes(name,initial,std::array<real,5>{1,1,1,4,4},rat(caps[omitted],100),
            [&](const auto& box,bool& valid){return midpoint_block_upper(box,valid,0,nullptr,(1<<omitted)-1,false,0,ten_ring_prices);});
    }
    std::array<I,3> initial{radial,I(0,delta),I(0,rat(203,100).hi)};
    const int caps[]={2160,2031,1928,1599};
    std::string name=std::string(extra?"ten-ring-quad-extra-":"ten-ring-quad-")+std::to_string(omitted);
    return verify_boxes(name.c_str(),initial,std::array<real,3>{1,1,4},rat(caps[omitted],100),[&](const auto& box,bool& valid){
        return root_cap_upper(box,valid,true,omitted,extra,RootShared::none,I(0),false,ten_ring_prices);
    });
}

bool verify_outer_angle_block(int length,int radial_ends){
    I radial(rat(118,100).lo,3.),gap(0,rat(953,1000).hi);
    std::string name=std::string(length==1?"outer-angle-normal-":"outer-angle-triangle-")+std::to_string(radial_ends);
    if(length==1){
        const int limits[]{6936,6906,7050};
        std::array<I,3> initial{radial,radial,gap};
        return verify_boxes(name.c_str(),initial,std::array<real,3>{1,1,4},rat(limits[radial_ends],1000),
            [&](const auto& box,bool& valid){
                return normal_upper({box[0],box[1],box[2],0,0},valid,0,nullptr,false,false,0,priced_ring,radial_ends);
            });
    }
    const int limits[]{13650,13570,13380};
    real delta=rat(91,100).hi,shift=rat(953,2000).hi;
    std::array<I,5> initial{radial,I(radial.lo,rat(3271,1000).hi),I(radial_ends==1?-delta:0,delta),gap,I(-shift,shift)};
    I bound=rat(limits[radial_ends],1000);
    return verify_boxes(name.c_str(),initial,std::array<real,5>{1,1,1,4,4},bound,
        [&](const auto& box,bool& valid){
            return midpoint_block_upper(box,valid,0,nullptr,0,0,0,priced_ring,radial_ends,bound.lo);
        });
}

I outer_angular_reach(I a){
    I cosine=(sq(a)+sq(min_outer)-4)/(2*a*min_outer);
    return pi/2-asin_mesh(I(std::clamp(cosine.lo,-1.,1.)));
}

bool verify_priced_variant(int length,PricedSeam left,PricedSeam right,int backward,int radial_ends,
                           int upper,bool middle=false,I inactive_span=0,const StarPrices& prices=priced_ring,
                           I endpoint_price=rat(4,5),bool anchor_span=false){
    I radial(rat(118,100).lo,3.),gap(0,rat(953,1000).hi),bound=rat(upper,1000);
    std::string name="priced-seam-"+std::to_string(length)+"-"+std::to_string(static_cast<int>(left))
        +std::to_string(static_cast<int>(right))+"-"+std::to_string(backward)+"-"+std::to_string(radial_ends);
    if(inactive_span.lo>0)name+="-span";
    if(anchor_span)name+="-anchor";
    if(&prices==&twin_ring)name+="-twin";
    if(&prices==&chord_ring)name+="-chord";
    if(&prices==&seven_chord_ring)name+="-seven-chord";
    if(endpoint_price.hi<0)name+="-opposite-transfer";
    if(length==1){
        StarPrices star=prices;
        if(middle)star.azimuth=star.azimuth-shallow_price;
        if(inactive_span.lo>0&&left==PricedSeam::inactive_no_area)star.azimuth=star.azimuth-inactive_span;
        std::array<I,3> initial{radial,radial,gap};
        return verify_boxes(name.c_str(),initial,std::array<real,3>{1,1,4},bound,
            [&](const auto& box,bool& valid){
                I cost=normal_upper({box[0],box[1],box[2],0,0},valid,0,nullptr,false,false,0,star,radial_ends,left,endpoint_price);
                if(valid&&anchor_span)cost=cost+inactive_span*outer_angular_reach(box[0]);
                return cost;
            });
    }
    real delta=rat(91,100).hi,shift=rat(953,2000).hi;
    I base=backward?I(-shift,shift):gap;
    I difference=backward==1?I(-gap.hi,0):backward==2?gap:I(-shift,shift);
    std::array<I,5> initial{radial,I(radial.lo,rat(3271,1000).hi),I(left==right&&!backward?0:-delta,delta),base,difference};
    return verify_boxes(name.c_str(),initial,std::array<real,5>{1,1,1,4,4},bound,
        [&](const auto& box,bool& valid){
            I anchor=0;
            if(anchor_span){
                I a=box[0]+box[2];
                if(!intersect(a,radial)){valid=false;return I(0);}
                anchor=inactive_span*outer_angular_reach(a);
            }
            I cost=midpoint_block_upper(box,valid,0,nullptr,0,backward,0,prices,radial_ends,(bound-anchor).lo,
                                         left,right,inactive_span,endpoint_price);
            return cost+anchor;
        },3000000000);
}

bool verify_chord_inactive_short(int length){
    using PS=PricedSeam;
    auto bound=[&](PS a,PS b,int upper,I price=0){
        return verify_priced_variant(length,a,b,0,0,upper,false,price,chord_ring,rat(4,5),price.lo>0);
    };
    if(length==1)return bound(PS::omit,PS::full,7490)&&bound(PS::inactive_no_area,PS::full,6670)
        &&bound(PS::inactive_no_area,PS::full,5990,rat(5,2));
    return bound(PS::full,PS::omit,15060)&&bound(PS::omit,PS::omit,13470)
        &&bound(PS::full,PS::inactive_no_area,14250)&&bound(PS::omit,PS::inactive_no_area,12650)
        &&bound(PS::full,PS::inactive_no_area,13320,rat(5,2))&&bound(PS::omit,PS::inactive_no_area,11680,rat(5,2));
}

bool verify_twin_short_caps(bool triangles){
    using PS=PricedSeam;
    if(triangles){
        return verify_priced_variant(2,PS::half,PS::full,0,0,13420,false,0,twin_ring)
            &&verify_priced_variant(2,PS::full,PS::half,0,1,13290,false,0,twin_ring)
            &&verify_priced_variant(2,PS::half,PS::half,0,0,11700,false,0,twin_ring);
    }
    return verify_priced_variant(1,PS::full,PS::full,0,0,7803,false,0,twin_ring)
        &&verify_priced_variant(1,PS::full,PS::full,0,1,7730,false,0,twin_ring)
        &&verify_priced_variant(1,PS::half,PS::full,0,0,5750,false,0,twin_ring)
        &&verify_priced_variant(1,PS::omit,PS::full,0,0,3920,true,0,twin_ring);
}

bool verify_narrow_inactive_pair(){
    using PS=PricedSeam;
    I radial((min_outer-2).lo,3),gap(0,rat(953,1000).hi);
    StarPrices narrow=priced_ring;
    narrow.azimuth=narrow.azimuth-3;
    bool normal=verify_boxes("priced-seam-inactive-anchor",std::array<I,3>{radial,radial,gap},
        std::array<real,3>{1,1,4},rat(362,100),[&](const auto& box,bool& valid){
            I base=normal_upper({box[0],box[1],box[2],0,0},valid,0,nullptr,false,false,0,narrow,0,PS::inactive_no_area);
            if(!valid)return I(0);
            I a=box[0],cosine=(sq(a)+sq(min_outer)-4)/(2*a*min_outer);
            I angle=pi/2-asin_mesh(I(std::clamp(cosine.lo,-1.,1.)));
            return base+3*angle;
        });
    return normal&&verify_priced_variant(2,PS::full,PS::inactive_no_area,0,0,9240,false,3)
        &&verify_priced_variant(2,PS::omit,PS::inactive_no_area,0,0,7550,false,3)
        &&verify_priced_variant(2,PS::half,PS::inactive_no_area,0,0,7550,false,3);
}

bool verify_priced_inactive_triangles(bool reverse,bool halves=false){
    using PS=PricedSeam;
    struct Variant {PS first,second; std::array<int,3> limit;};
    const std::array<Variant,6> variants{{
        {PS::full,PS::omit,{11980,8250,9020}},
        {PS::omit,PS::omit,{10430,6490,6490}},
        {PS::full,PS::inactive,{12480,8920,9460}},
        {PS::omit,PS::inactive,{10890,7140,6820}},
        {PS::full,PS::inactive_no_area,{11180,7790,8220}},
        {PS::omit,PS::inactive_no_area,{9620,5950,5800}},
    }};
    const std::array<Variant,3> shared{{
        {PS::omit,PS::half,{10500,6960,8070}},
        {PS::inactive,PS::half,{10980,7400,8690}},
        {PS::inactive_no_area,PS::half,{9690,6130,7480}},
    }};
    auto verify=[&](const Variant& v){
        if(!reverse){
            return verify_priced_variant(2,v.first,v.second,0,0,v.limit[0]);
        }
        return verify_priced_variant(2,v.first,v.second,1,0,v.limit[1])
            &&(v.first==v.second||verify_priced_variant(2,v.first,v.second,2,0,v.limit[2]));
    };
    return halves?std::all_of(shared.begin(),shared.end(),verify):std::all_of(variants.begin(),variants.end(),verify);
}

bool verify_double_mixed_triangle(){
    I radial(rat(118,100).lo,3.),gap(0,rat(953,1000).hi);
    real delta=rat(91,100).hi,shift=rat(953,2000).hi;
    std::array<I,5> initial{radial,I(radial.lo,rat(3271,1000).hi),I(0,delta),gap,I(-shift,shift)};
    Mixed mixed{true,false,true};
    return verify_boxes("double-mixed-triangle",initial,std::array<real,5>{1,1,1,4,4},rat(307,10),
        [&](const auto& box,bool& valid){return midpoint_block_upper(box,valid,2,&mixed);});
}

bool verify_ten_ring_shared_normal(){
    I radial(rat(118,100).lo,3.);
    std::array<I,3> initial{radial,radial,I(0,rat(953,1000).hi)};
    Mixed mixed{true,true,false,true};
    return verify_boxes("ten-ring-shared-normal",initial,std::array<real,3>{1,1,4},rat(54,10),[&](const auto& box,bool& valid){
        return normal_upper({box[0],box[1],box[2],I(0),I(0)},valid,0,&mixed,false,false,0,ten_ring_prices);
    });
}

bool verify_ten_ring_shared_triangle(bool both,int backward=0){
    I radial(rat(118,100).lo,3.),gap(0,rat(953,1000).hi);
    real delta=rat(91,100).hi,shift=rat(953,2000).hi;
    I base=backward?I(-shift,shift):gap;
    I difference=backward==1?I(-gap.hi,0):backward==2?gap:I(-shift,shift);
    std::array<I,5> initial{radial,I(radial.lo,rat(3271,1000).hi),I(both&&!backward?0:-delta,delta),base,difference};
    Mixed mixed{true,true,both,true};
    std::string name=std::string("ten-ring-shared-triangle-")+(both?"both":"one");
    if(backward)name+="-reverse-"+std::to_string(backward);
    I cap=backward?(both?rat(10):rat(1192,100)):(both?rat(1146,100):rat(66,5));
    return verify_boxes(name.c_str(),initial,std::array<real,5>{1,1,1,4,4},cap,[&](const auto& box,bool& valid){
            return midpoint_block_upper(box,valid,0,&mixed,0,backward,0,ten_ring_prices);
        });
}

bool verify_ten_ring_shared_middle(){
    I radial(rat(118,100).lo,3.);
    std::array<I,3> initial{radial,radial,I(0,rat(953,1000).hi)};
    StarPrices middle{ten_ring_prices.azimuth-shallow_price,ten_ring_prices.tilt,ten_ring_prices.angle,true};
    return verify_boxes("ten-ring-shared-middle",initial,std::array<real,3>{1,1,4},rat(351,100),
        [&](const auto& box,bool& valid){
            return normal_upper({box[0],box[1],box[2],I(0),I(0)},valid,0,nullptr,true,false,0,middle);
        });
}

bool verify_ten_ring_free_quad(){
    std::array<I,3> initial{I(rat(118,100).lo,3.),I(0,rat(91,100).hi),I(0,rat(203,100).hi)};
    return verify_boxes("ten-ring-free-quad",initial,std::array<real,3>{1,1,4},rat(216,10),
        [](const auto& box,bool& valid){
            return root_cap_upper(box,valid,true,0,false,RootShared::free_middle,I(0),false,ten_ring_prices);
        });
}

bool verify_ten_ring_crossed_quad(bool both){
    real delta=rat(91,100).hi;
    std::array<I,3> initial{I(rat(118,100).lo,3.),I(both?0:-delta,delta),I(0,rat(203,100).hi)};
    RootShared kind=both?RootShared::cross_both:RootShared::cross_one;
    return verify_boxes(both?"ten-ring-cross-quad-both":"ten-ring-cross-quad-one",initial,
        std::array<real,3>{1,1,4},both?rat(2355,100):rat(225,10),[&](const auto& box,bool& valid){
            return root_cap_upper(box,valid,true,0,false,kind,I(0),false,ten_ring_prices);
        });
}

bool verify_ten_ring_side_quad(int l,int r,int bound){
    real delta=rat(91,100).hi;
    std::array<I,3> initial{I(rat(118,100).lo,3.),I(l==r?0:-delta,delta),I(0,rat(203,100).hi)};
    std::string name="ten-ring-side-quad-"+std::to_string(l)+std::to_string(r);
    return verify_boxes(name.c_str(),initial,std::array<real,3>{1,1,4},rat(bound,100),[&](const auto& box,bool& valid){
        return root_cap_upper(box,valid,true,0,false,RootShared::none,I(0),false,ten_ring_prices,l,r);
    });
}

template<int RimPrice=6,bool OuterAngle=false> bool verify_rim_priced_quad(int l,int r,int bound,I radius_transfer=0,
                                                                        const StarPrices& prices=ten_ring_prices){
    real delta=rat(91,100).hi;
    real span_low=prices.core_chord.lo!=1?(2*pi-6*rat(953,1000)).lo:0;
    std::array<I,3> initial{I(rat(118,100).lo,3.),I(l==r?0:-delta,delta),I(span_low,rat(203,100).hi)};
    std::string name=std::string(OuterAngle?"outer-angle-quad-":RimPrice?"rim-priced-quad-":"clipped-side-quad-")
        +std::to_string(l)+std::to_string(r);
    if(radius_transfer.lo>0)name+="-radius-transfer";
    if(&prices==&chord_ring)name+="-chord";
    if(&prices==&seven_chord_ring)name+="-seven-chord";
    return verify_boxes(name.c_str(),initial,std::array<real,3>{1,1,4},rat(bound,100),[&](const auto& box,bool& valid){
        I root=root_cap_upper(box,valid,false,0,false,RootShared::none,I(0),false,prices);
        if(!valid)return I(0);
        I radial(rat(118,100).lo,3.),a=box[0]-box[1],b=box[0]+box[1];
        if(!intersect(a,radial)||!intersect(b,radial)){valid=false;return I(0);}
        auto kind=[](int charge){return charge==0?2:charge==1?1:0;};
        real left=crossed_side_upper<RimPrice,OuterAngle>(a,kind(l)),right=crossed_side_upper<RimPrice,OuterAngle>(b,kind(r));
        if(left==-inf||right==-inf){valid=false;return I(0);}
        I cost=root+area_peak+3*(OuterAngle?outer_angle_area:area_peak)+fan_ceiling+I(left)+I(right);
        if(radius_transfer.lo>0)cost=cost+radius_transfer*(a+b-rat(7,2));
        return cost;
    });
}

bool verify_typed_quad(bool transfer=false){
    I radial(rat(118,100).lo,3);
    real delta=rat(91,100).hi;
    const int limits[2][3]{{1208,1386,1496},{1118,1306,1412}};
    for(int scored=0;scored<3;scored++){
        std::array<I,3> initial{radial,I(scored?-delta:0,delta),I(0,rat(203,100).hi)};
        std::string label="outer-angle-typed-quad-"+std::to_string(scored);
        if(transfer)label+="-radius-transfer";
        if(!verify_boxes(label.c_str(),initial,std::array<real,3>{1,1,4},rat(limits[transfer][scored],100),
            [&](const auto& box,bool& valid){
                I root=root_cap_upper(box,valid,false,0,false,RootShared::none,0,false,ten_ring_prices);
                if(!valid)return I(0);
                I base=root+area_peak;
                if(transfer)base=base+rat(8,5)*(box[0]-rat(7,4));
                if(!scored)return base;
                I anchor=box[0]+box[1];
                if(!intersect(anchor,radial)){valid=false;return I(0);}
                real side=crossed_side_upper<0,true>(anchor,scored==1?2:1);
                if(side==-inf){valid=false;return I(0);}
                return base+outer_angle_area+side;
            }))return false;
    }
    return true;
}

bool verify_chord_inactive_root(int scored,int limit,I anchor_price=0){
    I radial(rat(118,100).lo,3);
    real delta=rat(91,100).hi;
    I gap=rat(953,1000);
    std::array<I,3> initial{radial,I(scored?-delta:0,delta),I((2*pi-6*gap).lo,rat(203,100).hi)};
    std::string label="chord-inactive-root-"+std::to_string(scored)+"-"+std::to_string(static_cast<int>(2*anchor_price.lo));
    return verify_boxes(label.c_str(),initial,std::array<real,3>{1,1,4},rat(limit,100),[&](const auto& box,bool& valid){
        I base=root_cap_upper(box,valid,false,0,false,RootShared::none,0,false,chord_ring)+area_peak;
        if(!valid||!scored)return base;
        I a=box[0]-box[1],b=box[0]+box[1];
        if(!intersect(a,radial)||!intersect(b,radial)){valid=false;return I(0);}
        real side=crossed_side_upper<0,true>(b,2);
        if(side==-inf){valid=false;return I(0);}
        base=base+I(side);
        if(anchor_price.lo>0){
            I remaining=nonneg(box[2]-2*gap);
            base=base+outer_angle_area+fan_ceiling+anchor_price*(outer_angular_reach(a)-remaining);
        }
        return base;
    });
}

bool verify_single_active_quad_end(){
    real delta=rat(91,100).hi;
    std::array<I,3> initial{I(rat(118,100).lo,3.),I(-delta,delta),I(0,rat(203,100).hi)};
    return verify_boxes("single-active-quad-end",initial,std::array<real,3>{1,1,4},rat(171,10),
        [&](const auto& box,bool& valid){
            return root_cap_upper(box,valid,true,0,false,RootShared::one_active_end,I(0),false,ten_ring_prices);
        });
}

struct InteriorChord {
    I x, h;
    V midpoint, inward_scaled;
};

bool interior_chord(V a,V b,InteriorChord& chord){
    I x2=norm2(b-a)/4;
    if(!intersect(x2,I(0,1)))return false;
    chord={rt(x2),rt(nonneg(1-x2)),I(.5)*(a+b),I(.5)*left(b-a)};
    return true;
}

bool outside_vertex(const InteriorChord& chord,V point){
    V offset=point-chord.midpoint;
    I height=dot(offset,chord.inward_scaled);
    if(height.lo>0)return false;
    if(chord.x.lo<=0)return true;
    I power=norm2(offset)-sq(chord.x),offset_power=2*(chord.h/chord.x)*height;
    return (power+offset_power).lo<=0&&(power-offset_power).hi>=0;
}

bool trim_outer_vertex(const InteriorChord& chord,V ray,I& radius){
    if(chord.x.lo>0){
        V support=chord.midpoint-(chord.h/chord.x)*chord.inward_scaled;
        I transverse=sq(det(ray,support));
        if(transverse.lo>1)return false;
        I center=dot(ray,support),extent=rt(nonneg(1-transverse));
        if(!intersect(radius,I((center-extent).lo,(center+extent).hi)))return false;
    }
    return outside_vertex(chord,radius*ray);
}

bool strict_end_cost(const Edge& e,I anchor,bool upper,int charge,I& cost){
    I full=cap_fan_score(score_upper(up(e.radius.hi+1)),ten_ring_prices);
    if(!charge){cost=e.outer_area+full;return true;}
    I share=full/2;
    if(charge==1 && !arc_reward(e,upper,5,share))return false;
    I direct=e.outer_area+share+fan_ceiling/2;
    real side=crossed_side_upper(anchor,charge==1);
    if(side==-inf)return false;
    cost=I(std::min(direct.hi,(area_peak+I(side)).hi));
    return true;
}

real rim_radius_lower(real half_angle){
    static const auto table=[] {
        std::vector<real> values;
        for(int i=0;i<=static_cast<int>(std::floor(M.hi*mesh));i++){
            Trig angle=trig(I(real(i)/mesh));
            values.push_back((R*angle.c-rt(nonneg(1-R2*sq(angle.s)))).lo);
        }
        return values;
    }();
    int i=std::clamp(static_cast<int>(std::floor(half_angle*mesh)),0,static_cast<int>(table.size())-1);
    return std::max(min_outer.lo,table[i]);
}

I coupled_end_cost(const Edge& e,I a,I b,bool at_end,real t_lower,int rim_charge,I fallback){
    I q(std::max(e.radius.lo,S.lo),e.radius.hi);
    I t=q+1;
    I rim=rim_width_upper(t.hi);
    I loose=fallback+rim_charge*rim;
    FanDerivative derivative;
    if(e.x.lo<=0 || t_lower>t.hi || !fan_derivative(t.hi,derivative))return loose;
    I slope=(5+rim_charge)*derivative.rim+derivative.area/2;
    I penalty(( (slope-shallow_price/(I(t_lower)*t))*q/t ).lo);
    if(penalty.lo<=0)return loose;

    I py(-1,1);
    if(!intersect(py,e.midpoint.y-(e.h/e.x)*e.inward_scaled.y))return loose;
    I signed_price=at_end?shallow_price:-shallow_price;
    I phase=shallow_price*asin_mesh((at_end?py:-py)/q);
    I u((1/I(t_lower)).hi);
    I phase_error=shallow_price*(asin_mesh(u)-u);
    V v{(e.x*e.h+e.inside_area)/q+penalty,(sq(a)-sq(b))/(4*q)+signed_price/t};
    I support=norm(v);
    I cut(std::clamp(((sq(I(t_lower))-sq(q)-1)/(2*q)).lo,-1.,1.));
    if(support.lo>0 && (v.x/support).hi<cut.lo){
        I segment=cut*v.x+rt(nonneg(1-sq(cut)))*abs_i(v.y);
        support=I(std::min(support.hi,segment.hi));
    }
    I joint=e.x*e.h+score_upper(t.hi)/2+fan_ceiling/2+rim_charge*rim+phase+phase_error+support-penalty;
    return I(std::min(loose.hi,joint.hi));
}

struct StrictQuadPrices {
    std::array<PricedSeam,3> seams;
    I end_transfer;
    bool other_ear;
};

I strict_quad_upper(const std::array<I,7>& box,bool& valid,int reversed,int lcharge,int rcharge,I threshold,
                    bool weighted=false,const StrictQuadPrices* typed=nullptr){
    I a=box[0],b=box[1],span=box[2],rj=box[3],rl=box[4],d0=box[5],d2=box[6];
    I gap(0,rat(953,1000).hi),allowed=reversed==1?-gap:gap;
    I d1=span-d0-d2;
    if(!intersect(d1,allowed)||!intersect(span,d0+d1+d2)
        ||!intersect(d0,span-d1-d2)||!intersect(d2,span-d0-d1)){valid=false;return 0;}
    I half=span/2;
    Trig mid=trig(half);
    V axy=a*V{mid.c,-mid.s},bxy=b*unit(mid);
    InteriorChord root,ear;
    I mx=(a+b)*mid.s/2,dy=(b-a)*mid.c/2;
    I x2=sq(mx)+sq(dy);
    if(!intersect(x2,I(0,1))){valid=false;return 0;}
    root={rt(x2),rt(nonneg(1-x2)),I(.5)*(axy+bxy),V{-mx,dy}};
    I transfer=0,weighted_left=0,weighted_right=0;
    if(weighted&&!typed){
        real left_side=crossed_side_upper<0,true>(a,1),right_side=crossed_side_upper<0,true>(b,1);
        if(left_side==-inf||right_side==-inf){valid=false;return 0;}
        transfer=rat(4,5)*(a+b-rat(7,2));
        weighted_left=outer_angle_area+left_side;
        weighted_right=outer_angle_area+right_side;
        I base=root_cap_upper({(a+b)/2,(b-a)/2,span},valid,false,0,false,RootShared::none,0,false,ten_ring_prices);
        if(!valid)return 0;
        I coarse=base+area_peak+outer_angle_area+fan_ceiling+weighted_left+weighted_right+transfer;
        if(coarse.hi<threshold.lo)return coarse;
    }
    V jray=unit(signed_trig(d0-half)),lray=unit(signed_trig(half-d2));
    if(typed&&typed->other_ear){
        if(!trim_outer_vertex(root,lray,rl)||!interior_chord(axy,rl*lray,ear)
            ||!trim_outer_vertex(ear,jray,rj)){valid=false;return 0;}
    }else if(!trim_outer_vertex(root,jray,rj)||!interior_chord(rj*jray,bxy,ear)
        ||!trim_outer_vertex(ear,lray,rl)){valid=false;return 0;}

    I core;
    if(!central(root.x,root.h,root.midpoint,root.inward_scaled,V{-ten_ring_prices.tilt*mid.s,0},ten_ring_prices.angle,core)){
        valid=false;return 0;
    }
    Trig tr0=signed_trig(d0),tr1=signed_trig(d1),tr2=signed_trig(d2);
    Edge first,middle,last;
    if(!edge(a,rj,tr0,V{a,0},rj*unit(tr0),first,reversed==0)
       ||!edge(rj,rl,tr1,{}, {},middle,reversed==1)
       ||!edge(rl,b,tr2,rl*V{tr2.c,-tr2.s},V{b,0},last,reversed==2)){
        valid=false;return 0;
    }
    if(typed){
        I left_cost,mid_cost,right_cost;
        if(!priced_seam_upper(first,a,rj,typed->seams[0],false,left_cost)
           ||!priced_seam_upper(middle,rj,rl,typed->seams[1],false,mid_cost)
           ||!priced_seam_upper(last,rl,b,typed->seams[2],true,right_cost)){
            valid=false;return 0;
        }
        I subtotal=ten_ring_prices.azimuth*span+core+first.inside_area+middle.inside_area+last.inside_area
            +typed->end_transfer*(b-rat(7,4));
        I result=subtotal+left_cost+mid_cost+right_cost;
        if(result.hi<threshold.lo)return result;
        auto refine=[](const Edge& e,PricedSeam mode,I old){
            if(mode!=PricedSeam::full)return old;
            I bound=coupled_outer_upper(e)-priced_ring.outer_angle*asin_lower(e.x.lo);
            return I(std::min(bound.hi,old.hi));
        };
        return subtotal+refine(first,typed->seams[0],left_cost)+refine(middle,typed->seams[1],mid_cost)
            +refine(last,typed->seams[2],right_cost);
    }
    real lt=up(1+first.radius.hi),rtop=up(1+last.radius.hi);
    if(!weighted&&(12*M+rim_width_upper(lt)+rim_width_upper(rtop)-pi).hi<0){valid=false;return 0;}
    I lcost,rcost;
    if(!strict_end_cost(first,a,false,lcharge,lcost)||!strict_end_cost(last,b,true,rcharge,rcost)){
        valid=false;return 0;
    }
    I fixed=ten_ring_prices.azimuth*span+core+first.inside_area+middle.inside_area+last.inside_area
        +middle.outer_area+fan_ceiling;
    if(weighted){
        I p=priced_ring.outer_angle;
        I left=coupled_end_cost(first,a,rj,false,min_outer.lo,0,lcost)-p*asin_lower(first.x.lo);
        I right=coupled_end_cost(last,rl,b,true,min_outer.lo,0,rcost)-p*asin_lower(last.x.lo);
        return fixed+transfer-p*asin_lower(middle.x.lo)
            +I(std::min(weighted_left.hi,left.hi))+I(std::min(weighted_right.hi,right.hi));
    }
    I result=fixed+lcost+rcost;
    if(result.hi<threshold.lo||lcharge!=1||rcharge!=1)return result;
    I needed=pi-12*M;
    real l_lower=rim_radius_lower((needed-rim_width_upper(rtop)).lo);
    real r_lower=rim_radius_lower((needed-rim_width_upper(lt)).lo);
    for(int charge:{0,2,5,10}){
        I joined=fixed+coupled_end_cost(first,a,rj,false,l_lower,charge,lcost)
            +coupled_end_cost(last,rl,b,true,r_lower,charge,rcost)-charge*needed;
        result=I(std::min(result.hi,joined.hi));
        if(result.hi<threshold.lo)break;
    }
    return result;
}

bool verify_strict_quad(int reversed,int lcharge,int rcharge,I bound,bool weighted=false){
    I endpoint(rat(118,100).lo,3),middle(rat(118,100).lo,rat(3271,1000).hi),gap(0,rat(953,1000).hi);
    real span_low=weighted?(2*pi-6*gap.hi).lo:0;
    std::array<I,7> initial{endpoint,endpoint,I(span_low,rat(203,100).hi),middle,middle,
                            reversed==0?-gap:gap,reversed==2?-gap:gap};
    std::string name=std::string(weighted?"outer-angle-strict-quad-":"strict-quad-")
        +std::to_string(lcharge)+std::to_string(rcharge)+"-"+std::to_string(reversed);
    return verify_boxes(name.c_str(),initial,std::array<real,7>{1,1,4,1,1,4,4},bound,
        [&](const auto& box,bool& valid){return strict_quad_upper(box,valid,reversed,lcharge,rcharge,bound,weighted);},
        8000000000);
}

bool verify_inactive_phase_quad(int variant){
    using PS=PricedSeam;
    const int limits[]{1825,1845,1495};
    I endpoint(rat(118,100).lo,3),middle(rat(118,100).lo,rat(3271,1000).hi),gap(0,rat(953,1000).hi);
    I span((2*pi-6*gap.hi).lo,rat(203,100).hi),bound=rat(limits[variant],100);
    for(bool other_ear:{false,true}){
        StrictQuadPrices prices{{PS::inactive_phase,variant==2?PS::omit:PS::full,variant==1?PS::half:PS::full},
                                variant==2?I(0):rat(4,5),other_ear};
        for(int reversed:{-1,0,1,2}){
            std::array<I,7> initial{endpoint,endpoint,span,middle,middle,reversed==0?-gap:gap,reversed==2?-gap:gap};
            std::string label="inactive-phase-quad-"+std::to_string(variant)+"-"+std::to_string(other_ear)
                +"-"+std::to_string(reversed);
            if(!verify_boxes(label.c_str(),initial,std::array<real,7>{1,1,4,1,1,4,4},bound,
                [&](const auto& box,bool& valid){return strict_quad_upper(box,valid,reversed,0,0,bound,true,&prices);},
                3000000000))return false;
        }
    }
    return true;
}

I reversed_quad_upper(const std::array<I,7>& box,bool& valid,int reversed){
    std::array<I,3> d{box[4],box[5],box[6]};
    d[reversed]=-d[reversed];
    I span=d[0]+d[1]+d[2];
    if(span.hi<=0)return 3*(2*area_peak+fan_ceiling);
    if(!intersect(span,I(0,rat(203,100).hi))){valid=false;return 0;}
    const I half=span/2;
    Trig h=trig(half);
    V a=box[0]*V{h.c,-h.s},j=box[1]*unit(signed_trig(d[0]-half));
    V l=box[2]*unit(signed_trig(d[0]+d[1]-half)),b=box[3]*unit(h);
    InteriorChord root,ear;
    if(!interior_chord(a,b,root)||!interior_chord(j,b,ear)
       ||!outside_vertex(root,j)||!outside_vertex(ear,l)){valid=false;return 0;}
    V linear{-ten_ring_prices.tilt*h.s,0};
    I core;
    if(!central(root.x,root.h,root.midpoint,root.inward_scaled,linear,ten_ring_prices.angle,core)){
        valid=false;return 0;
    }
    I cost=ten_ring_prices.azimuth*span+core;
    std::array<V,4> points{a,j,l,b};
    for(int i=0;i<3;i++){
        Edge e;
        if(!edge(box[i],box[i+1],signed_trig(d[i]),points[i],points[i+1],e,reversed==i)){
            valid=false;return 0;
        }
        cost=cost+e.inside_area+e.outer_area+cap_fan_score(score_upper(up(e.radius.hi+1)),ten_ring_prices);
    }
    return cost;
}

bool verify_reversed_quad(int reversed){
    I endpoint(rat(118,100).lo,3),middle(rat(118,100).lo,rat(3271,1000).hi),gap(0,rat(953,1000).hi);
    std::array<I,7> initial{endpoint,middle,middle,endpoint,gap,gap,gap};
    std::string name="reversed-quad-"+std::to_string(reversed);
    return verify_boxes(name.c_str(),initial,std::array<real,7>{1,1,1,1,4,4,4},rat(2084,100),
        [&](const auto& box,bool& valid){return reversed_quad_upper(box,valid,reversed);});
}

real bridge_support(V v,V A,V B,I x,I x2,I radius=1){
    I length=norm(v);
    real bound=std::min({(radius*length).hi,(dot(v,A)+2*length).hi,(dot(v,B)+2*length).hi});
    if(x.lo>0 && length.lo>0){
        V diff=B-A;
        I projection=dot(v,diff)/length;
        if((x2-abs_i(projection)).lo>0){
            I h=rt(nonneg(4-x2));
            I cap=dot(v,I(.5)*(A+B))+h*abs_i(dot(v,left(diff))/(2*x));
            bound=std::min(bound,cap.hi);
        }
    }
    return bound;
}

template<std::size_t N>
bool bridge_angle_and_support(V A,V B,I x,I x2,const std::array<V,N>& points,
                              const std::array<bool,N>& known,V tilt,V linear,
                              I& angle,real& tilt_support,real& linear_support){
    tilt_support=bridge_support(tilt,A,B,x,x2);
    linear_support=bridge_support(linear,A,B,x,x2);
    real height=0;
    if(x.lo>0){
        V outward=left(A-B)/(2*x);
        V midpoint=I(.5)*(A+B);
        I reach=1+2*rt(nonneg(1-sq(nonneg(x-1))));
        I tilt_norm=norm(tilt),linear_norm=norm(linear);
        for(std::size_t i=0;i<N;i++)if(known[i]){
            height=std::max(height,(dot(points[i]-midpoint,outward)-1).lo);
            tilt_support=std::min(tilt_support,(dot(tilt,points[i])+reach*tilt_norm).hi);
            linear_support=std::min(linear_support,(dot(linear,points[i])+reach*linear_norm).hi);
        }
    }
    I length2=x2+sq(I(height));
    if(length2.lo>4)return false;
    angle=2*asin_lower((rt(length2)/2).lo);
    return true;
}

const StarPrices three_fan_prices{3,rat(7,2),1,true};
const StarPrices three_fan_wide_prices{rat(7,2),rat(17,5),rat(4,5),true};
const I three_fan_anchor=rat(9,5);

bool verify_three_fan_normal(bool anchored,bool wide=false,bool inactive=false){
    I radial((R-3).lo,3),gap(0,rat(953,1000).hi);
    const auto& price=wide?three_fan_wide_prices:three_fan_prices;
    const char* label=inactive?(anchored?"three-fan-inactive-anchor":"three-fan-inactive-normal")
        :wide?(anchored?"three-fan-wide-anchor":"three-fan-wide-normal")
             :(anchored?"nine-three-fan-anchor":"nine-three-fan-normal");
    I threshold=rat(inactive?(anchored?5530:5300):wide?(anchored?7101:7142):(anchored?6585:6615),1000);
    return verify_boxes(label,std::array<I,3>{radial,radial,gap},std::array<real,3>{1,1,4},threshold,
        [&](const auto& box,bool& valid){
            I a=box[0],b=box[1],d=box[2];
            Trig half=trig(d/2);
            Edge e;
            if(!edge(a,b,trig(d),a*V{half.c,-half.s},b*unit(half),e)){valid=false;return I(0);}
            I local;
            if(!central(e.x,e.h,e.midpoint,e.inward_scaled,V{-price.tilt*half.s,0},price.angle,local)){
                valid=false;return I(0);
            }
            I outer=inactive?e.outer_area:I(std::min(outer_tangent_upper(e).hi,coupled_outer_upper(e).hi));
            return e.inside_area+local+price.azimuth*d+outer-(anchored?a-three_fan_anchor:I(0));
        });
}

bool verify_three_fan_cross_normal(){
    I radial((R-3).lo,3),gap(0,rat(953,1000).hi);
    const auto& price=three_fan_wide_prices;
    return verify_boxes("three-fan-crossed-normal",std::array<I,3>{radial,radial,gap},
        std::array<real,3>{1,1,4},rat(696,100),[&](const auto& box,bool& valid){
            I a=box[0],b=box[1],d=box[2];
            Trig tr=trig(d),half=trig(d/2);
            Edge e;
            I inner,outer;
            if(!edge(a,b,tr,a*V{tr.c,-tr.s},V{b,0},e)||
               !central(e.x,e.h,e.midpoint,e.inward_scaled,(-price.tilt*half.s)*V{half.c,-half.s},price.angle,inner)||
               !strict_end_cost(e,b,true,1,outer)){
                valid=false;return I(0);
            }
            outer=coupled_end_cost(e,a,b,true,min_outer.lo,0,outer);
            return e.inside_area+inner+price.azimuth*d+outer-b+three_fan_anchor;
        });
}

bool verify_three_fan_primary_pair(){
    I radial((R-3).lo,3),gap(0,rat(953,1000).hi);
    I span(0,std::min((rat(1131,1000)+rat(7,4)*(14*M-pi)).hi,(2*asin_i(2/min_outer)).hi));
    const auto& price=three_fan_wide_prices;
    return verify_boxes("three-fan-primary-pair",std::array<I,5>{radial,radial,radial,gap,gap},
        std::array<real,5>{1,1,1,4,4},rat(1365,100),[&](const auto& box,bool& valid){
            I a=box[0],b=box[1],j=box[2],d0=box[3],d1=box[4],D=d0+d1;
            if(!intersect(D,span)){valid=false;return I(0);}
            Trig half=trig(D/2);
            V A=a*V{half.c,-half.s},B=b*unit(half),J=j*unit(signed_trig((d0-d1)/2));
            Edge e,f;
            if(!edge(a,j,trig(d0),A,J,e)||!edge(j,b,trig(d1),J,B,f)){valid=false;return I(0);}
            V chord=I(.5)*left(B-A),tilt{-price.tilt*half.s,0};
            I each=e.outer_area+f.outer_area,tilt_norm=norm(tilt);
            I area=I(std::min((4+tilt_norm).hi,(2*each+tilt_norm).hi));
            real radius=up(std::min(e.radius.hi,f.radius.hi)+1);
            if(half.s.lo>0)radius=std::min(radius,(2/half.s).hi);
            I wedge=e.inside_area+f.inside_area;
            for(const Edge* known:{&e,&f})if(known->x.lo>0){
                V Q=known->midpoint+(known->h/known->x)*known->inward_scaled;
                V P=known->midpoint-(known->h/known->x)*known->inward_scaled;
                I c_bound,tilt_bound;
                if(!lens_support(chord+tilt,Q,c_bound)||!lens_support(tilt,Q,tilt_bound)){
                    valid=false;return I(0);
                }
                I inner=I(std::min((wedge+c_bound).hi,(each+tilt_bound).hi));
                I outer=I(std::min(each.hi,(norm(chord)-dot(chord,P)-wedge).hi));
                area=I(std::min({area.hi,(inner+outer).hi,(4+tilt_bound).hi}));
            }
            if(e.x.lo>0&&f.x.lo>0){
                V P0=e.midpoint-(e.h/e.x)*e.inward_scaled,P1=f.midpoint-(f.h/f.x)*f.inward_scaled;
                V Q0=e.midpoint+(e.h/e.x)*e.inward_scaled,Q1=f.midpoint+(f.h/f.x)*f.inward_scaled;
                V outside=P1-P0,inside=Q1-Q0;
                I distance=norm2(outside);
                if(!intersect(distance,I(0,4))){valid=false;return I(0);}
                radius=std::min(radius,(norm(I(.5)*(P0+P1))+rt(nonneg(1-distance/4))).hi);
                if(radius<min_outer.lo){valid=false;return I(0);}
                auto core=[&](V direction,I& upper){
                    I s0,s1,s2;
                    if(!lens_support(direction,Q0,s0)||!lens_support(direction,Q1,s1)
                       ||!lens_support(direction,inside,s2))return false;
                    upper=I(std::min({s0.hi,s1.hi,(dot(direction,Q0)+s2).hi}));
                    return true;
                };
                I inside_support,outside_support,tilt_support;
                if(!core(chord+tilt,inside_support)||!core(tilt,tilt_support)
                   ||!lens_support(-I(1)*chord,outside,outside_support)){
                    valid=false;return I(0);
                }
                I joint=inside_support-dot(chord,P0)+outside_support;
                I partial=wedge+inside_support+each;
                area=I(std::min({area.hi,joint.hi,partial.hi,(4+tilt_support).hi}));
            }
            I angle=asin_lower(e.x.lo)+asin_lower(f.x.lo);
            I transfer(std::max({0.,(three_fan_anchor-a).hi,(three_fan_anchor-b).hi}));
            return area+cap_fan_score(score_upper(radius),price)+fan_ceiling+price.azimuth*D-price.angle*angle+transfer;
        });
}

bool verify_three_fan_cap(){
    I radial((R-3).lo,3),middle((R-3).lo,rat(3271,1000).hi),gap(0,rat(953,1000).hi);
    I span(0,(rat(1152,1000)+rat(7,4)*(14*M-pi)).hi);
    const auto& price=three_fan_wide_prices;
    return verify_boxes("three-fan-main-cap",std::array<I,5>{radial,radial,middle,gap,gap},
        std::array<real,5>{1,1,1,4,4},rat(14085,1000),
        [&](const auto& box,bool& valid){
            I a=box[0],b=box[1],rj=box[2],d0=box[3],d1=box[4],D=d0+d1;
            if(!intersect(D,span)){valid=false;return I(0);}
            Trig half=trig(D/2);
            V A=a*V{half.c,-half.s},B=b*unit(half),ray=unit(signed_trig((d0-d1)/2));
            InteriorChord chord;
            if(!interior_chord(A,B,chord)||!trim_outer_vertex(chord,ray,rj)){valid=false;return I(0);}
            V J=rj*ray;
            I inside;
            if(!central(chord.x,chord.h,chord.midpoint,chord.inward_scaled,V{-price.tilt*half.s,0},price.angle,inside)){
                valid=false;return I(0);
            }
            Edge first,last;
            if(!edge(a,rj,trig(d0),A,J,first)||!edge(rj,b,trig(d1),J,B,last)){valid=false;return I(0);}
            auto outside=[](const Edge& e){return I(std::min(outer_tangent_upper(e).hi,coupled_outer_upper(e).hi));};
            return first.inside_area+last.inside_area+inside+outside(first)+outside(last)+price.azimuth*D;
        },3000000000);
}

enum class ThreeFanBlock {plain, wide, cap_endpoint, inactive_endpoint, internal_shared, crossed_endpoint};

bool verify_three_fan_block(ThreeFanBlock kind=ThreeFanBlock::plain){
    bool wide=kind!=ThreeFanBlock::plain,cap_endpoint=kind==ThreeFanBlock::cap_endpoint;
    bool inactive_end=kind==ThreeFanBlock::inactive_endpoint,shared=kind==ThreeFanBlock::internal_shared;
    bool crossed=kind==ThreeFanBlock::crossed_endpoint;
    I radial((R-3).lo,3),middle((R-3).lo,rat(3271,1000).hi),gap(0,rat(953,1000).hi);
    I allowance=rat(7,4)*(14*M-pi),ordinary_span=rat(737,1000);
    I span((2*pi-6*ordinary_span-allowance).lo,(3*ordinary_span+allowance).hi);
    if(cap_endpoint)span.lo=(2*pi-4*ordinary_span-rat(1152,1000)-allowance).lo;
    if(inactive_end)span=I((2*pi-5*ordinary_span-allowance).lo,(2*ordinary_span+gap+allowance).hi);
    if(shared)span.hi=(ordinary_span+rat(1131,1000)+allowance).hi;
    const auto& price=wide?three_fan_wide_prices:three_fan_prices;
    const char* label=crossed?"three-fan-crossed-block":shared?"three-fan-internal-shared":inactive_end?"three-fan-inactive-end"
        :wide?(cap_endpoint?"three-fan-wide-cap-end":"three-fan-wide-block"):"nine-three-fan-block";
    I threshold=rat(crossed?2372:inactive_end?2208:wide?(cap_endpoint?2362:2355):2228,100);
    return verify_boxes(label,std::array<I,7>{radial,radial,span,middle,middle,gap,gap},
        std::array<real,7>{1,1,4,1,1,4,4},threshold,
        [&](const auto& box,bool& valid){
            I a=box[0],b=box[1],D=box[2],rj=box[3],rl=box[4],d0=box[5],d2=box[6],d1=D-d0-d2;
            if(!intersect(d1,gap)||!intersect(d0,D-d1-d2)||!intersect(d2,D-d0-d1)){valid=false;return I(0);}
            Trig half=trig(D/2);
            I x2=sq(a-b)/4+a*b*sq(half.s);
            if(!intersect(x2,I(0,4))){valid=false;return I(0);}
            I x=rt(x2);
            std::array<I,4> radii{a,rj,rl,b};
            std::array<V,4> points{a*V{half.c,-half.s},rj*unit(signed_trig(d0-D/2)),
                                   rl*unit(signed_trig(D/2-d2)),b*unit(half)};
            I wedge=0,outer=0;
            std::array<Edge,3> edges{};
            std::array<V,3> supports{};
            std::array<bool,3> defined{};
            std::array<I,3> angles{d0,d1,d2};
            for(int i=0;i<3;i++){
                Edge& e=edges[i];
                if(!edge(radii[i],radii[i+1],trig(angles[i]),points[i],points[i+1],e)){valid=false;return I(0);}
                wedge=wedge+e.inside_area;
                if(!crossed||i!=0){
                    outer=outer+e.outer_area;
                    if(!inactive_end||i!=0)outer=outer+cap_fan_score(score_upper(up(e.radius.hi+1)),price);
                }
                if(e.x.lo>0){
                    defined[i]=true;
                    supports[i]=e.midpoint+(e.h/e.x)*e.inward_scaled;
                    for(int j=0;j<i;j++)if(defined[j]&&norm2(supports[j]-supports[i]).lo>4){
                        valid=false;return I(0);
                    }
                }
            }
            V A=points.front(),B=points.back(),tilt{-price.tilt*half.s,0};
            V linear=tilt+I(.5)*left(B-A);
            I bridge_angle;
            real tilt_support,linear_support;
            if(!bridge_angle_and_support(A,B,x,x2,supports,defined,tilt,linear,bridge_angle,tilt_support,linear_support)){
                valid=false;return I(0);
            }
            I exact=wedge+linear_support;
            I bridge_area=2*x*rt(nonneg(1-sq(nonneg(x-1))));
            I cap=I(std::min((5*area_peak).hi,(3*area_peak+bridge_area).hi))+tilt_support;
            I adjustment=-2*area_peak+price.azimuth*D
                -price.angle*bridge_angle+b-three_fan_anchor
                +(cap_endpoint?I(0):a-three_fan_anchor);
            I crossed_outside=0;
            if(crossed){
                adjustment=adjustment+nonneg(three_fan_anchor-b);
                Edge local;
                Trig tr=trig(d0);
                if(!edge(a,rj,tr,V{a,0},rj*unit(tr),local)||!strict_end_cost(local,a,false,1,crossed_outside)){
                    valid=false;return I(0);
                }
                crossed_outside=coupled_end_cost(local,a,rj,false,min_outer.lo,0,crossed_outside);
            }
            if(shared){
                adjustment=adjustment+I(std::max({0.,(three_fan_anchor-a).hi,(three_fan_anchor-b).hi}));
                const Edge& first=edges[0];
                const Edge& second=edges[1];
                I last(std::min(outer_tangent_upper(edges[2]).hi,coupled_outer_upper(edges[2]).hi));
                I exterior=first.outer_area+second.outer_area;
                I block=I(std::min(exact.hi,cap.hi))+exterior+2*fan_ceiling;
                if(first.x.lo>0&&second.x.lo>0){
                    V P=first.midpoint-(first.h/first.x)*first.inward_scaled;
                    V Q=second.midpoint-(second.h/second.x)*second.inward_scaled;
                    V coefficient=I(.5)*left(A-points[2]),delta=Q-P;
                    I distance=norm2(delta),support;
                    if(!intersect(distance,I(0,4))||!lens_support(coefficient,delta,support)){
                        valid=false;return I(0);
                    }
                    I radius=norm(I(.5)*(P+Q))+rt(nonneg(1-distance/4));
                    radius.hi=std::min({radius.hi,up(first.radius.hi+1),up(second.radius.hi+1)});
                    if(radius.hi<min_outer.lo){valid=false;return I(0);}
                    I scores=cap_fan_score(score_upper(radius.hi),price)+fan_ceiling;
                    I joint=dot(coefficient,P)+support;
                    I joint_exact=linear_support+edges[2].inside_area+joint+scores;
                    I joint_cap=cap+I(std::min(exterior.hi,(joint-first.inside_area-second.inside_area).hi))+scores;
                    block=I(std::min({block.hi,joint_exact.hi,joint_cap.hi}));
                }
                return block+last+adjustment;
            }
            I common=I(std::min(exact.hi,cap.hi))+adjustment+crossed_outside;
            I result=common+outer;
            if(result.hi<threshold.lo)return result;
            outer=0;
            for(std::size_t i=crossed?1:0;i<edges.size();i++)outer=outer+
                (inactive_end&&i==0?edges[i].outer_area:outer_tangent_upper(edges[i]));
            result=common+outer;
            if(result.hi<threshold.lo)return result;
            outer=0;
            for(std::size_t i=crossed?1:0;i<edges.size();i++){
                const Edge& e=edges[i];
                outer=outer+(inactive_end&&i==0?e.outer_area:I(std::min(outer_tangent_upper(e).hi,coupled_outer_upper(e).hi)));
            }
            return common+outer;
        },3000000000);
}

enum class FatShared {none, endpoint, inside, both_ends};

I fat_cap_upper(const std::array<I,5>& box,bool& valid,FatShared shared,int omitted,I radius=1){
    I m=box[0],tj=box[1],z=box[2],d=box[3],e=box[4];
    I a=m-z,b=m+z,radial(rat(118,100).lo,(2+radius).hi);
    if(!intersect(a,radial)||!intersect(b,radial)){valid=false;return 0;}
    I gap(0,rat(953,1000).hi),d1=d+e,d2=d-e;
    if(!intersect(d1,gap)||!intersect(d2,gap)){valid=false;return 0;}
    Trig tr=trig(d),shift=signed_trig(e);
    I x2=sq(m*tr.s)+sq(z*tr.c);
    if(!intersect(x2,I(0,4))){valid=false;return 0;}
    I x=rt(x2);
    V A{a*tr.c,-a*tr.s},B{b*tr.c,b*tr.s},U{-ten_ring_prices.tilt*tr.s,0};
    I wedge=tj*(m*tr.s*shift.c-z*tr.c*shift.s);
    I wedge_plus_support=wedge+bridge_support(U+V{-m*tr.s,z*tr.c},A,B,x,x2,radius);
    I area_plus_tilt(std::min(wedge_plus_support.hi,up(4+bridge_support(U,A,B,x,x2,radius))));

    // Maximize the cosine over the rectangle of possible distances to c.
    // For either distance separately the maximum is at an endpoint.
    real cosine=-inf;
    for(I p:{a-radius,I(2)})for(I q:{b-radius,I(2)})
        cosine=std::max(cosine,((sq(p)+sq(q)-4*x2)/(2*p*q)).hi);
    I angle=nonneg(pi/2-asin_mesh(I(std::clamp(cosine,-1.,1.))));
    Edge first,second;
    Trig tr1=trig(d1),tr2=trig(d2);
    V F{},G{},H{},J{};
    if(shared==FatShared::endpoint||shared==FatShared::both_ends){F={a,0};G=tj*unit(tr1);}
    if(shared==FatShared::inside){F=a*V{tr1.c,-tr1.s};G={tj,0};H={tj,0};J=b*unit(tr2);}
    if(shared==FatShared::both_ends){H=tj*V{tr2.c,-tr2.s};J={b,0};}
    if(!edge(a,tj,tr1,F,G,first)||!edge(tj,b,tr2,H,J,second)){valid=false;return 0;}
    I f=cap_fan_score(score_upper(up(first.radius.hi+1)),ten_ring_prices);
    I g=cap_fan_score(score_upper(up(second.radius.hi+1)),ten_ring_prices);
    if(shared!=FatShared::none && !arc_reward(first,shared==FatShared::inside,5,f)){valid=false;return 0;}
    if(shared==FatShared::inside && !arc_reward(second,false,5,g)){valid=false;return 0;}
    if(shared==FatShared::both_ends && !arc_reward(second,true,5,g)){valid=false;return 0;}
    if(omitted&1)f=0;
    if(omitted&2)g=0;
    return area_plus_tilt-2*area_peak+8*d-I(angle.lo)+first.outer_area+second.outer_area+f+g;
}

bool verify_fat_cap(FatShared shared,int omitted=0,bool wide=false){
    I radius=wide?wide_ring.core_radius:I(1);
    real delta=wide?rat(95,100).hi:rat(91,100).hi;
    std::array<I,5> initial{I(rat(118,100).lo,wide?(2+radius).hi:3.),I(rat(118,100).lo,rat(3271,1000).hi),
                           I(shared==FatShared::endpoint||omitted==1?-delta:0,delta),I(0,rat(953,1000).hi),
                           I(-rat(953,2000).hi,rat(953,2000).hi)};
    const char* name=shared==FatShared::none?"fat-cap-two":shared==FatShared::endpoint?"fat-cap-shared-end":"fat-cap-shared-inside";
    I cap=shared==FatShared::none?rat(1471,100):shared==FatShared::endpoint?rat(1285,100):rat(1065,100);
    if(shared==FatShared::both_ends){name="fat-cap-shared-both-ends";cap=rat(108,10);}
    if(omitted==1){name="fat-cap-omitted-one";cap=rat(1295,100);}
    if(omitted==3){name="fat-cap-omitted-two";cap=rat(112,10);}
    if(wide){
        switch(shared){
            case FatShared::none: cap=rat(1495,100);break;
            case FatShared::endpoint: cap=rat(132,10);break;
            case FatShared::inside: cap=rat(1145,100);break;
            case FatShared::both_ends: cap=rat(116,10);break;
        }
    }
    std::string label=wide?std::string("wide-")+name:name;
    return verify_boxes(label.c_str(),initial,std::array<real,5>{1,1,1,4,4},cap,
        [&](const auto& box,bool& valid){return fat_cap_upper(box,valid,shared,omitted,radius);});
}

bool verify_wide_regular(int length,int shared,bool three=false,int tighter_bound=0,int omitted=0){
    const StarPrices& prices=three?wide_three_ring:wide_ring;
    I radial(rat(118,100).lo,std::min((2+prices.core_radius).hi,rat(3271,1000).hi)),gap(0,rat(953,1000).hi);
    Mixed mixed{true,true,shared==2,true};
    std::string name=std::string(three?"wide-three-regular-":"wide-regular-")
        +std::to_string(length)+"-"+std::to_string(shared);
    if(tighter_bound)name+="-tight";
    if(omitted)name+="-omitted-"+std::to_string(omitted);
    if(length==1){
        std::array<I,3> initial{radial,radial,gap};
        I limit=tighter_bound?rat(tighter_bound,100):three?rat(shared?505:683,100):shared?I(5):rat(69,10);
        return verify_boxes(name.c_str(),initial,std::array<real,3>{1,1,4},limit,
            [&](const auto& box,bool& valid){
                return normal_upper({box[0],box[1],box[2],0,0},valid,0,shared?&mixed:nullptr,omitted>0,false,0,prices);
            });
    }
    real delta=rat(three?105:95,100).hi;
    if(length==2){
        real shift=rat(953,2000).hi;
        std::array<I,5> initial{radial,I(radial.lo,rat(3271,1000).hi),I(shared==1||omitted==1?-delta:0,delta),
                               gap,I(-shift,shift)};
        const int bounds[2][3]{{1425,1260,1095},{1357,1225,1045}};
        return verify_boxes(name.c_str(),initial,std::array<real,5>{1,1,1,4,4},
            rat(tighter_bound?tighter_bound:bounds[three][shared],100),
            [&](const auto& box,bool& valid){
                return midpoint_block_upper(box,valid,0,shared?&mixed:nullptr,(1<<omitted)-1,0,0,prices);
            },tighter_bound?3000000000:1000000000);
    }
    std::array<I,3> initial{radial,I(shared==1?-delta:0,delta),I(0,rat(203,100).hi)};
    const int bounds[2][3]{{2160,2230,2330},{2005,2070,2130}};
    return verify_boxes(name.c_str(),initial,std::array<real,3>{1,1,4},rat(tighter_bound?tighter_bound:bounds[three][shared],100),
        [&](const auto& box,bool& valid){
            return root_cap_upper(box,valid,true,omitted,false,RootShared::free_middle,0,false,prices,
                                  shared>=1,shared>=2);
        });
}

I opposite_angle(I radius){
    // For t in [1,1.455], the endpoint constraint
    // a^2+t^2+2at cos(theta) <= 4 is weakest at the smallest a.
    I a(radius.lo),ceiling=wide_three_ring.core_radius;
    I peak=rt(nonneg(sq(a)-4));
    I t(std::clamp(peak.lo,1.,ceiling.lo),std::clamp(peak.hi,1.,ceiling.hi));
    I cosine=(4-sq(a)-sq(t))/(2*a*t);
    return pi/2-asin_mesh(I(std::clamp(cosine.hi,-1.,1.)));
}

enum class FatThreePair { none, active, inactive, active_third_inactive };

I wide_fat_three_upper(const std::array<I,7>& box,bool& valid,int shares,bool distinct,int omitted,FatThreePair pair){
    I a=box[0],b=box[1],span=box[2],rj=box[3],rl=box[4],d0=box[5],d2=box[6];
    I gap(0,rat(953,1000).hi),d1=span-d0-d2;
    if(!intersect(d1,gap)||!intersect(span,d0+d1+d2)
        ||!intersect(d0,span-d1-d2)||!intersect(d2,span-d0-d1)){valid=false;return 0;}
    I xi_a=opposite_angle(a),xi_b=opposite_angle(b);
    if(!intersect(span,I((xi_a+xi_b).lo,span.hi))){valid=false;return 0;}
    I half=span/2;
    I epsilon(std::max(-half.hi,(xi_a-half).lo),std::min(half.hi,(half-xi_b).hi));
    if(epsilon.lo>epsilon.hi){valid=false;return 0;}
    Trig h=trig(half);
    I mean=(a+b)/2,imbalance=(b-a)/2;
    I x2=sq(mean*h.s)+sq(imbalance*h.c);
    if(!intersect(x2,I(0,4))){valid=false;return 0;}
    V A=a*V{h.c,-h.s},B=b*unit(h);
    V tilt{-wide_three_ring.tilt*h.s,0},linear=tilt+V{-mean*h.s,imbalance*h.c};
    I radius=wide_three_ring.core_radius;
    I arc_support=I(1,radius.hi)*dot(linear,-1*unit(signed_trig(epsilon)));
    I core(std::min(arc_support.hi,bridge_support(linear,A,B,rt(x2),x2,radius)));
    I angle=2*asin_lower((rt(x2)/2).lo);
    Trig tr0=trig(d0),tr1=trig(d1),tr2=trig(d2);
    Edge first,middle,last;
    if(!edge(a,rj,tr0,V{a,0},rj*unit(tr0),first)
       ||!edge(rj,rl,tr1,{},{},middle)
       ||!edge(rl,b,tr2,rl*V{tr2.c,-tr2.s},V{b,0},last)){valid=false;return 0;}
    if(pair!=FatThreePair::none){
        I wedge_and_area=first.inside_area+middle.inside_area+first.outer_area+middle.outer_area;
        real radial_upper=up(1+std::min(first.radius.hi,middle.radius.hi));
        if(first.x.lo>0&&middle.x.lo>0){
            V J=rj*unit(signed_trig(d0-half)),L=rl*unit(signed_trig(half-d2));
            V P=I(.5)*(A+J)-(first.h/(2*first.x))*left(J-A);
            V Q=I(.5)*(J+L)-(middle.h/(2*middle.x))*left(L-J);
            I distance=norm2(Q-P);
            if(distance.lo>4){valid=false;return 0;}
            I power=norm(I(.5)*(P+Q))+rt(nonneg(1-distance/4));
            radial_upper=std::min(radial_upper,power.hi);
            V linear=I(.5)*left(A-L);
            I support;
            if(!lens_support(linear,Q-P,support)){valid=false;return 0;}
            wedge_and_area=I(std::min(wedge_and_area.hi,(dot(linear,P)+support).hi));
        }
        if(radial_upper<min_outer.lo){valid=false;return 0;}
        I paired_score=pair==FatThreePair::inactive?I(0):
            cap_fan_score(score_upper(radial_upper),ten_ring_prices);
        I last_cost=pair==FatThreePair::active_third_inactive?last.outer_area:outer_tangent_upper(last);
        return 4*span-angle-2*area_peak+core+wedge_and_area+last.inside_area
            +paired_score+fan_ceiling+last_cost;
    }
    auto end=[&](const Edge& e,I p,I q,bool upper,I& cost){
        if(omitted&(upper?4:1)){cost=e.outer_area;return true;}
        if(!(shares&(upper?2:1))){cost=outer_tangent_upper(e);return true;}
        I reward;
        if(!arc_reward(e,upper,5,reward))return false;
        cost=coupled_end_cost(e,p,q,upper,min_outer.lo,0,e.outer_area+reward+fan_ceiling/2);
        return true;
    };
    I cost0,cost2;
    if(!end(first,a,rj,false,cost0)||!end(last,rl,b,true,cost2)){valid=false;return 0;}
    I middle_cost=omitted&2?middle.outer_area:distinct?outer_tangent_upper(middle):middle.outer_area+fan_ceiling;
    return 4*span-angle-2*area_peak+core+first.inside_area+middle.inside_area+last.inside_area
        +cost0+middle_cost+cost2;
}

bool verify_wide_fat_three(int shares,bool distinct=false,int omitted=0,FatThreePair pair=FatThreePair::none){
    I radial(rat(118,100).lo,rat(3271,1000).hi),gap(0,rat(953,1000).hi);
    std::array<I,7> initial{radial,radial,3*gap,radial,radial,gap,gap};
    std::string label="wide-fat-three-"+std::to_string(shares);
    if(distinct)label+="-distinct";
    if(omitted)label+="-omitted-"+std::to_string(omitted);
    I limit=omitted?rat(omitted==1?2462:2280,100):distinct?rat(2543,100):rat(262,10);
    if(pair!=FatThreePair::none){
        label+="-pair-"+std::to_string(static_cast<int>(pair));
        limit=pair==FatThreePair::active?rat(2543,100):rat(2462,100);
    }
    return verify_boxes(label.c_str(),initial,std::array<real,7>{1,1,4,1,1,4,4},
        limit,[&](const auto& box,bool& valid){return wide_fat_three_upper(box,valid,shares,distinct,omitted,pair);},
        distinct?4000000000:1000000000);
}

bool verify_wide_inactive_pair_normal(){
    StarPrices prices=wide_three_ring;
    prices.azimuth=rat(3,2);
    I radial(rat(118,100).lo,rat(3271,1000).hi),gap(0,rat(953,1000).hi);
    return verify_boxes("wide-three-inactive-pair-normal",std::array<I,3>{radial,radial,gap},
        std::array<real,3>{1,1,4},rat(315,100),[&](const auto& box,bool& valid){
            return normal_upper({box[0],box[1],box[2],0,0},valid,0,nullptr,true,false,0,prices);
        });
}

bool verify_degree_four_fat_three(int shares){
    I radial(rat(118,100).lo,3),middle(rat(118,100).lo,rat(3271,1000).hi),gap(0,rat(953,1000).hi);
    I span((2*pi-6*gap.hi).lo,rat(shares?2309:2411,1000).hi);
    std::array<I,7> initial{radial,radial,span,middle,middle,gap,gap};
    std::string label="degree-four-fat-three-"+std::to_string(shares);
    return verify_boxes(label.c_str(),initial,std::array<real,7>{1,1,4,1,1,4,4},
        rat(241,10),[&](const auto& box,bool& valid){
            I a=box[0],b=box[1],D=box[2],rj=box[3],rl=box[4],d0=box[5],d2=box[6];
            I d1=D-d0-d2;
            if(!intersect(d1,gap)||!intersect(D,d0+d1+d2)
               ||!intersect(d0,D-d1-d2)||!intersect(d2,D-d0-d1)){valid=false;return I(0);}
            I half=D/2;
            Trig h=trig(half);
            V A=a*V{h.c,-h.s},B=b*unit(h),J=rj*unit(signed_trig(d0-half));
            V lray=unit(signed_trig(half-d2));
            InteriorChord ear,first_chord;
            if(!interior_chord(J,B,ear)||!trim_outer_vertex(ear,lray,rl)||!interior_chord(A,J,first_chord)){
                valid=false;return I(0);
            }
            if(ear.x.lo>0&&first_chord.x.lo>0){
                V Q=ear.midpoint+(ear.h/ear.x)*ear.inward_scaled;
                V P=first_chord.midpoint+(first_chord.h/first_chord.x)*first_chord.inward_scaled;
                if(norm2(Q-P).lo>4){valid=false;return I(0);}
            }
            I mean=(a+b)/2,imbalance=(b-a)/2;
            I x2=sq(mean*h.s)+sq(imbalance*h.c);
            if(!intersect(x2,I(0,4))){valid=false;return I(0);}
            I x=rt(x2);
            V tilt{-ten_ring_prices.tilt*h.s,0},linear=tilt+V{-mean*h.s,imbalance*h.c};
            Trig tr0=trig(d0),tr1=trig(d1),tr2=trig(d2);
            Edge first,mid,last;
            if(!edge(a,rj,tr0,V{a,0},rj*unit(tr0),first)
               ||!edge(rj,rl,tr1,{},{},mid)
               ||!edge(rl,b,tr2,rl*V{tr2.c,-tr2.s},V{b,0},last)){valid=false;return I(0);}
            I wedge=first.inside_area+mid.inside_area+last.inside_area;
            I cap=4+area_peak+bridge_support(tilt,A,B,x,x2);
            I exact=wedge+bridge_support(linear,A,B,x,x2);
            I left_cost,right_cost;
            if(!strict_end_cost(first,a,false,shares&1,left_cost)||!strict_end_cost(last,b,true,shares>>1,right_cost)){
                valid=false;return I(0);
            }
            left_cost=shares&1?coupled_end_cost(first,a,rj,false,min_outer.lo,0,left_cost):outer_tangent_upper(first);
            right_cost=shares&2?coupled_end_cost(last,rl,b,true,min_outer.lo,0,right_cost):outer_tangent_upper(last);
            return I(std::min(cap.hi,exact.hi))-2*area_peak+4*D-2*asin_lower((x/2).lo)
                +left_cost+mid.outer_area+fan_ceiling+right_cost;
        },3000000000);
}

const StarPrices crossed_two_cap_prices{3,rat(15,4),rat(4,5),true};

bool verify_two_cap_crossed_normal(bool shared){
    I radial(rat(118,100).lo,3),gap(0,rat(953,1000).hi);
    return verify_boxes(shared?"degree-four-two-caps-normal-half":"degree-four-two-caps-normal",
        std::array<I,3>{radial,radial,gap},std::array<real,3>{1,1,4},rat(shared?634:676,100),
        [&](const auto& box,bool& valid){
            I a=box[0],b=box[1],d=box[2];
            Trig tr=trig(d),half=trig(d/2);
            Edge e;
            if(!edge(a,b,tr,a*V{tr.c,-tr.s},V{b,0},e)){valid=false;return I(0);}
            const StarPrices& p=crossed_two_cap_prices;
            I local;
            if(!central(e.x,e.h,e.midpoint,e.inward_scaled,(-p.tilt*half.s)*V{half.c,-half.s},p.angle,local)){
                valid=false;return I(0);
            }
            I outside;
            if(shared){
                if(!strict_end_cost(e,b,true,1,outside)){valid=false;return I(0);}
                outside=coupled_end_cost(e,a,b,true,min_outer.lo,0,outside);
            }else outside=I(std::min(outer_tangent_upper(e).hi,coupled_outer_upper(e).hi));
            return local+e.inside_area+p.azimuth*d+outside;
        });
}

bool verify_two_cap_fat_pair(bool crossed){
    I radial(rat(118,100).lo,3),middle(rat(118,100).lo,rat(3271,1000).hi),gap(0,rat(953,1000).hi);
    I span((2*pi-5*gap.hi).lo,rat(crossed?2723:2918,1000).hi);
    std::array<I,9> initial{radial,radial,span,middle,middle,middle,gap,gap,gap};
    const StarPrices& p=crossed?crossed_two_cap_prices:ten_ring_prices;
    return verify_boxes(crossed?"degree-four-two-caps-crossed-pair":"degree-four-two-caps-internal-pair",
        initial,std::array<real,9>{1,1,4,1,1,1,4,4,4},rat(crossed?2995:3155,100),
        [&](const auto& box,bool& valid){
            I a=box[0],b=box[1],D=box[2],rj=box[3],rl=box[4],rk=box[5];
            I d0=box[6],d1=box[7],d3=box[8],d2=D-d0-d1-d3;
            if(!intersect(d2,gap)||!intersect(d0,D-d1-d2-d3)||!intersect(d1,D-d0-d2-d3)
               ||!intersect(d3,D-d0-d1-d2)){valid=false;return I(0);}
            I half=D/2;
            Trig h=trig(half);
            V A=a*V{h.c,-h.s},B=b*unit(h),Jray=unit(signed_trig(d0-half));
            V L=rl*unit(signed_trig(d0+d1-half)),Kray=unit(signed_trig(half-d3));
            InteriorChord left_cap,right_cap;
            if(!interior_chord(A,L,left_cap)||!interior_chord(L,B,right_cap)
                ||!trim_outer_vertex(left_cap,Jray,rj)||!trim_outer_vertex(right_cap,Kray,rk)){
                valid=false;return I(0);
            }
            std::array<bool,2> defined{left_cap.x.lo>0,right_cap.x.lo>0};
            std::array<V,2> supports{};
            if(defined[0])supports[0]=left_cap.midpoint+(left_cap.h/left_cap.x)*left_cap.inward_scaled;
            if(defined[1])supports[1]=right_cap.midpoint+(right_cap.h/right_cap.x)*right_cap.inward_scaled;
            if(defined[0]&&defined[1]&&norm2(supports[0]-supports[1]).lo>4){valid=false;return I(0);}
            V J=rj*Jray,K=rk*Kray;
            I mean=(a+b)/2,imbalance=(b-a)/2,x2=sq(mean*h.s)+sq(imbalance*h.c);
            if(!intersect(x2,I(0,4))){valid=false;return I(0);}
            I x=rt(x2);
            V tilt{-p.tilt*h.s,0},linear=tilt+V{-mean*h.s,imbalance*h.c};
            Edge first,inner_left,inner_right,last;
            Trig first_trig=trig(d0);
            if(!edge(a,rj,first_trig,V{a,0},rj*unit(first_trig),first)||!edge(rj,rl,trig(d1),J,L,inner_left)
                ||!edge(rl,rk,trig(d2),L,K,inner_right)||!edge(rk,b,trig(d3),{}, {},last)){
                valid=false;return I(0);
            }
            I wedge=first.inside_area+inner_left.inside_area+inner_right.inside_area+last.inside_area;
            I bridge_angle;
            real tilt_support,linear_support;
            if(!bridge_angle_and_support(A,B,x,x2,supports,defined,tilt,linear,bridge_angle,tilt_support,linear_support)){
                valid=false;return I(0);
            }
            I ear0=first.inside_area+inner_left.inside_area-det(A,L)/2;
            I ear1=inner_right.inside_area+last.inside_area-det(L,B)/2;
            I ears(std::min(ear0.hi,triangle_area_upper(left_cap.x).hi)+
                   std::min(ear1.hi,triangle_area_upper(right_cap.x).hi));
            ears.hi=up(ears.hi);
            I area_cap=4+ears+tilt_support,exact=wedge+linear_support;
            I central_wedge=(det(A,L)+det(L,B))/2;
            I split_area=ears+central_wedge+linear_support;
            auto full=[](const Edge& e){return I(std::min(outer_tangent_upper(e).hi,coupled_outer_upper(e).hi));};
            I cost=I(std::min({area_cap.hi,exact.hi,split_area.hi}))-2*area_peak+p.azimuth*D-p.angle*bridge_angle;
            if(crossed){
                I outside;
                if(!strict_end_cost(first,a,false,1,outside)){valid=false;return I(0);}
                outside=coupled_end_cost(first,a,rj,false,min_outer.lo,0,outside);
                return cost+outside+full(inner_left)+full(inner_right)+full(last);
            }
            I paired=inner_left.outer_area+inner_right.outer_area+2*fan_ceiling;
            if(inner_left.x.lo>0&&inner_right.x.lo>0){
                V P=inner_left.midpoint-(inner_left.h/inner_left.x)*inner_left.inward_scaled;
                V Q=inner_right.midpoint-(inner_right.h/inner_right.x)*inner_right.inward_scaled;
                V delta=Q-P,coefficient=left(J-K)/2;
                I distance=sq(norm(delta));
                if(!intersect(distance,I(0,4))){valid=false;return I(0);}
                I support;
                if(!lens_support(coefficient,delta,support)){valid=false;return I(0);}
                I radius=norm((P+Q)/2)+rt(nonneg(1-distance/4));
                radius.hi=std::min({radius.hi,up(1+inner_left.radius.hi),up(1+inner_right.radius.hi)});
                if(radius.hi<min_outer.lo){valid=false;return I(0);}
                I joint=dot(coefficient,P)+support-inner_left.inside_area-inner_right.inside_area
                    +cap_fan_score(score_upper(radius.hi),ten_ring_prices)+fan_ceiling;
                paired=I(std::min(paired.hi,joint.hi));
            }
            return cost+full(first)+paired+full(last);
        },3000000000);
}

bool verify_degree_four_fat_four(int shares,bool second_ear,int shortcut=-1){
    I radial(rat(118,100).lo,3),middle(rat(118,100).lo,rat(3271,1000).hi),gap(0,rat(953,1000).hi);
    bool reduced=shortcut>=0;
    I root_span(0,rat(203,100).hi),span((2*pi-(reduced?4:5)*gap.hi).lo,(gap+root_span).hi);
    I double_gap(0,(2*gap).hi);
    std::array<I,9> initial{radial,radial,span,middle,middle,middle,gap,
                           shortcut==1?double_gap:gap,shortcut==3?double_gap:gap};
    std::string label="degree-four-fat-four-"+std::to_string(second_ear)+"-"+std::to_string(shares);
    if(reduced)label+="-shortcut-"+std::to_string(shortcut);
    return verify_boxes(label.c_str(),initial,std::array<real,9>{1,1,4,1,1,1,4,4,4},
        reduced?rat(3855,100):rat(306,10),
        [&](const auto& box,bool& valid){
            I a=box[0],b=box[1],D=box[2],d0=box[6],d1=box[7],d3=box[8];
            I cap_span=D-d0;
            if(!intersect(cap_span,root_span)||!intersect(D,d0+cap_span)){valid=false;return I(0);}
            I d2=cap_span-d1-d3;
            if(!intersect(d2,shortcut==2?double_gap:gap)
               ||!intersect(d1,cap_span-d2-d3)||!intersect(d3,cap_span-d1-d2)){
                valid=false;return I(0);
            }
            I half=D/2;
            I directions(-half.hi,half.hi),jangle=d0-half,langle=d0+d1-half,mangle=half-d3;
            if(!intersect(jangle,directions)||!intersect(langle,directions)||!intersect(mangle,directions)){
                valid=false;return I(0);
            }
            Trig h=trig(half);
            V A=a*V{h.c,-h.s},B=b*unit(h);
            V jray=unit(signed_trig(jangle)),lray=unit(signed_trig(langle)),mray=unit(signed_trig(mangle));
            I rj=box[3],rl=box[4],rm=box[5];
            V J=rj*jray;
            InteriorChord first_chord,cap,ear;
            if(!interior_chord(A,J,first_chord)||!interior_chord(J,B,cap)){valid=false;return I(0);}
            if(second_ear){
                if(!trim_outer_vertex(cap,mray,rm)||!interior_chord(J,rm*mray,ear)||!trim_outer_vertex(ear,lray,rl)){
                    valid=false;return I(0);
                }
            }else if(!trim_outer_vertex(cap,lray,rl)||!interior_chord(rl*lray,B,ear)||!trim_outer_vertex(ear,mray,rm)){
                valid=false;return I(0);
            }
            if(cap.x.lo>0&&first_chord.x.lo>0){
                V P=first_chord.midpoint+(first_chord.h/first_chord.x)*first_chord.inward_scaled;
                V Q=cap.midpoint+(cap.h/cap.x)*cap.inward_scaled;
                if(norm2(Q-P).lo>4){valid=false;return I(0);}
            }
            I mean=(a+b)/2,imbalance=(b-a)/2,x2=sq(mean*h.s)+sq(imbalance*h.c);
            if(!intersect(x2,I(0,4))){valid=false;return I(0);}
            I x=rt(x2);
            V tilt{-ten_ring_prices.tilt*h.s,0},linear=tilt+V{-mean*h.s,imbalance*h.c};
            Trig tr0=trig(d0),tr3=trig(d3);
            Edge first,mid1,mid2,last;
            auto middle_edge=[&](I p,I q,Trig tr,int index,Edge& e){
                if(index!=shortcut)return edge(p,q,tr,{},{},e);
                I x2_short=(sq(p-q)+2*p*q*(1-tr.c))/4;
                if(x2_short.lo>1)return false;
                e.inside_area=p*q*tr.s/2;
                e.outer_area=2*area_peak+fan_ceiling;
                return true;
            };
            if(!edge(a,rj,tr0,V{a,0},rj*unit(tr0),first)
               ||!middle_edge(rj,rl,trig(d1),1,mid1)||!middle_edge(rl,rm,trig(d2),2,mid2)
               ||(shortcut!=3&&!edge(rm,b,tr3,rm*V{tr3.c,-tr3.s},V{b,0},last))){
                valid=false;return I(0);
            }
            if(shortcut==3){
                I x2_short=(sq(rm-b)+2*rm*b*(1-tr3.c))/4;
                if(x2_short.lo>1){valid=false;return I(0);}
                last.inside_area=rm*b*tr3.s/2;
            }
            I wedge=first.inside_area+mid1.inside_area+mid2.inside_area+last.inside_area;
            I added_area=reduced?area_peak:I(0);
            I area_cap=4+2*area_peak+added_area+bridge_support(tilt,A,B,x,x2);
            I exact=wedge+added_area+bridge_support(linear,A,B,x,x2);
            I left_cost,right_cost;
            if(!strict_end_cost(first,a,false,shares&1,left_cost)){valid=false;return I(0);}
            left_cost=shares&1?coupled_end_cost(first,a,rj,false,min_outer.lo,0,left_cost):outer_tangent_upper(first);
            if(shortcut==3){
                real end=shares&2?crossed_side_upper(b,true):
                    cap_fan_score(score_upper(up(2+b.hi)),ten_ring_prices).hi;
                if(end==-inf){valid=false;return I(0);}
                right_cost=2*area_peak+fan_ceiling+end;
            }else{
                if(!strict_end_cost(last,b,true,shares>>1,right_cost)){valid=false;return I(0);}
                right_cost=shares&2?coupled_end_cost(last,rm,b,true,min_outer.lo,0,right_cost):outer_tangent_upper(last);
            }
            return I(std::min(area_cap.hi,exact.hi))-2*area_peak+4*D-2*asin_lower((x/2).lo)
                +left_cost+mid1.outer_area+mid2.outer_area+2*fan_ceiling+right_cost;
        },5000000000);
}

I mark_at(I x,I weight=lambda){
    return x*(1+2*rt(nonneg(1-sq(x))))-2*weight*asin_mesh(x);
}

I mark_upper(I x){
    I peak=root2/2;
    if(x.hi<peak.lo)return mark_at(I(x.hi));
    if(x.lo>peak.hi)return mark_at(I(x.lo));
    return 1+peak-lambda*pi/2;
}

bool verify_inactive_mark_loss(int variant=0){
    const I u=pi/14;
    const bool weighted=variant>0;
    const I charge=weighted?rat(1,2):I(0),bonus=variant==2?rat(4,25):I(0);
    const I tangent_weight=lambda-charge/2,weight=tangent_weight-bonus/2;
    const Trig at=trig(u);
    const I root=rt(1-sq(R*at.s)),t=R*at.c-root,x=t*at.s;
    const I slope=(1+2*(1-2*sq(x)-tangent_weight)/rt(1-sq(x)))*t*(R*sq(at.s)/root+at.c)/2;
    const I cap=mark_at(x,tangent_weight)-charge*pi
        +(variant==2?rat(75,1000):weighted?rat(-25,100):rat(-47,100));
    const I cy=(rt(33+32*weight)-1)/8,peak=rt(1-sq(cy));
    const I radii(min_outer.lo,rat(104,25).hi),gaps(0,(2*M).hi);
    std::array<I,3> initial{radii,radii,gaps};
    const char* name=variant==2?"inactive-mark-vertex-price":weighted?"inactive-weighted-mark-loss":"inactive-mark-loss";
    return verify_boxes(name,initial,std::array<real,3>{1,1,4},cap,
        [&](const auto& box,bool& valid){
            I a=box[0],b=box[1],d=box[2];
            if(a.lo>b.hi || !intersect(d,I(0,(rim_width_upper(a.hi)+rim_width_upper(b.hi)).hi))){
                valid=false;return I(0);
            }
            Trig angle=trig(d);
            Edge e;
            if(!edge(a,b,angle,V{a,0},b*unit(angle),e)){valid=false;return I(0);}
            I price=slope*(2*u-d),obtuse=0;
            I bound=mark_upper(e.x)+price;
            if(weighted){
                I location=peak;
                if(e.x.hi<peak.lo)location=I(e.x.hi);
                if(e.x.lo>peak.hi)location=I(e.x.lo);
                I short_chord(e.x.lo);
                obtuse=short_chord-(2*lambda+charge+bonus)*asin_lower(short_chord.lo)+bonus*pi;
                I acute=mark_at(location,weight)-charge*pi;
                bound=I(std::max(acute.hi,obtuse.hi))+price;
            }
            if(bound.hi<cap.lo||e.x.lo<=0)return bound;
            V qxy=e.midpoint+(e.h/e.x)*e.inward_scaled;
            I q=norm(qxy);
            if(!intersect(q,I(S.lo,rat(104,25).hi+1))){valid=false;return I(0);}
            I cut=(sq(min_outer)-sq(q)-1)/(2*q);
            if(cut.lo>1){valid=false;return I(0);}
            I cosine=(e.h-e.inside_area/e.x)/q;
            if(!intersect(cosine,I(-1,1))){valid=false;return I(0);}
            if(cut.lo<=cosine.hi)return bound;
            I low(cut.lo),support=low*cosine+rt(nonneg(1-sq(low)))*rt(nonneg(1-sq(cosine)));
            if(weighted){
                real max_area=std::min(e.outer_area.hi,(e.x*(e.h+support)).hi);
                if(max_area<=0){valid=false;return I(0);}
                I intersection_angle=2*atan_i(sq(e.x)/I(max_area));
                I base_angle=asin_mesh(e.x);
                real apex=std::max(base_angle.hi,std::min(intersection_angle.hi,(pi-base_angle).hi));
                I radial=I(max_area)+e.x*e.h-2*lambda*asin_lower(e.x.lo)+(charge+bonus)*I(apex)-charge*pi;
                return I(std::min(bound.hi,(I(std::max(radial.hi,obtuse.hi))+price).hi));
            }
            return bound-e.x*nonneg(1-support);
        });
}

I inactive_transition_cap(real length){
    constexpr int table[][2]{{850,505},{950,567},{1050,643},{1150,717},{1238,780},
                             {1320,833},{1400,881},{1480,925},{1570,966},{1660,996}};
    for(const auto& row:table)if(length<=rat(row[0],1000).lo)return rat(row[1],1000);
    return rat(1012,1000);
}

bool verify_inactive_joint_star(){
    I u=pi/14,charge=rat(1,2),bonus=rat(4,25),weight=lambda-charge/2;
    Trig at=trig(u);
    I root=rt(1-sq(R*at.s)),t=R*at.c-root,x=t*at.s;
    I slope=(1+2*(1-2*sq(x)-weight)/rt(1-sq(x)))*t*(R*sq(at.s)/root+at.c)/2;
    I limit=mark_at(x,weight)-charge*pi+rat(1795,1000);
    I radii(min_outer.lo,rat(104,25).hi),gaps(0,(2*M).hi);
    std::array<I,4> initial{radii,radii,gaps,I(0,pi.hi)};
    return verify_boxes("inactive-joint-star",initial,std::array<real,4>{1,1,4,2},limit,
        [&](const auto& box,bool& valid){
            I a=box[0],b=box[1],d=box[2],alpha=box[3];
            if(a.lo>b.hi||!intersect(d,I(0,(rim_width_upper(a.hi)+rim_width_upper(b.hi)).hi))){
                valid=false;return I(0);
            }
            Trig angle=trig(d);
            Edge e;
            if(!edge(a,b,angle,V{a,0},b*unit(angle),e)){valid=false;return I(0);}
            I base=asin_lower(e.x.lo);
            if(!intersect(alpha,I(base.lo,(pi-base).hi))){valid=false;return I(0);}
            real area=e.outer_area.hi;
            if(e.x.lo>0){
                V Q=e.midpoint+(e.h/e.x)*e.inward_scaled;
                I q=norm(Q);
                if(!intersect(q,I(S.lo,rat(104,25).hi+1))){valid=false;return I(0);}
                I cut=(sq(min_outer)-sq(q)-1)/(2*q);
                I cosine=(e.h-e.inside_area/e.x)/q;
                if(cut.lo>1||!intersect(cosine,I(-1,1))){valid=false;return I(0);}
                if(cut.lo>cosine.hi){
                    I k(cut.lo);
                    I support=k*cosine+rt(nonneg(1-sq(k)))*rt(nonneg(1-sq(cosine)));
                    area=std::min(area,(e.x*(e.h+support)).hi);
                }
            }
            Trig h=trig(alpha/2);
            real short_leg=rat(619,500).hi,long_leg=2;
            if(h.s.lo>0){
                area=std::min(area,(sq(e.x)*nonneg(h.c)/h.s).hi);
                short_leg=std::min(short_leg,(e.x/h.s).hi);
            }
            if(area<0){valid=false;return I(0);}
            I sine=2*h.s*h.c,cosine=1-2*sq(h.s);
            if(sine.lo>0){
                I product((2*I(area)/sine).hi);
                I sum2=4*sq(e.x)+2*product*nonneg(1+cosine);
                I diff2=4*sq(e.x)-2*product*nonneg(1-cosine);
                short_leg=std::min(short_leg,((rt(nonneg(sum2))-rt(nonneg(diff2)))/2).hi);
            }
            I long_sine=trig(I(std::min(alpha.lo,(pi/2).lo))).s;
            if(long_sine.lo>0)long_leg=std::min(long_leg,(2*e.x/long_sine).hi);
            return I(area)+e.x*e.h-2*lambda*base+(charge+bonus)*alpha-charge*pi+slope*(2*u-d)
                +inactive_transition_cap(short_leg)+inactive_transition_cap(long_leg);
        });
}

bool verify_mark_pair(const FanHighRadius* target=nullptr){
    const I u=pi/14;
    const I radius=target?target->radius:R,half_angle=target?target->half_angle:M,weight=target?I(0):lambda;
    const Trig at=trig(u);
    const I root=rt(1-sq(radius*at.s)),t=radius*at.c-root,x=t*at.s;
    const I slope=(1+2*(1-2*sq(x)-weight)/rt(1-sq(x)))*t*(radius*sq(at.s)/root+at.c)/2;
    const I cap=2*mark_at(x,weight)-rat(target?5:7,100);
    const I radii((radius-1).lo,target?target->radial_cap.hi:rat(104,25).hi),gaps(0,(2*half_angle).hi);
    const std::array<I,5> initial{radii,radii,I(0,rat(1,2).hi),gaps,I(-half_angle.hi,half_angle.hi)};
    const I zero_peak=rt(1-sq((rt(I(33))-1)/8));
    auto width=[&](real a){return target?target->rim_width(a):rim_width_upper(a);};
    auto mark_bound=[&](I a){
        if(!target)return mark_upper(a);
        if(a.hi<zero_peak.lo)return mark_at(I(a.hi),0);
        if(a.lo>zero_peak.hi)return mark_at(I(a.lo),0);
        return mark_at(zero_peak,0);
    };
    return verify_boxes(target?"high-fourteen-mark-pair":"mark-pair-fourteen",initial,
        std::array<real,5>{1,1,1,4,4},cap,[&](const auto& box,bool& valid){
            I a=box[0]-box[2],b=box[1],c=box[0]+box[2];
            I d1=box[3]+box[4],d2=box[3]-box[4];
            if(!intersect(a,radii)||!intersect(c,radii)||!intersect(d1,gaps)||!intersect(d2,gaps)
                ||!intersect(d1,I(0,(width(a.hi)+width(b.hi)).hi))
                ||!intersect(d2,I(0,(width(b.hi)+width(c.hi)).hi))){valid=false;return I(0);}
            Trig f=trig(d1),g=trig(d2);
            V A=a*V{f.c,-f.s},B{b,0},C=c*unit(g);
            Edge first,second;
            if(!edge(a,b,f,A,B,first)||!edge(b,c,g,B,C,second)){valid=false;return I(0);}
            I price=slope*(4*u-2*box[3]);
            I bound=mark_bound(first.x)+mark_bound(second.x)+price;
            if(first.x.lo<=0 || second.x.lo<=0 || bound.hi<cap.lo)return bound;

            V n1=first.inward_scaled/first.x,n2=second.inward_scaled/second.x;
            V q1=first.midpoint+first.h*n1,q2=second.midpoint+second.h*n2;
            V v=I(.5)*left(C-A),diff=q2-q1;
            I support;
            if(!lens_support(v,diff,support)){valid=false;return I(0);}
            I area=first.inside_area+second.inside_area+dot(v,q1)+support;
            I flank=first.x*first.h+second.x*second.h
                    -2*weight*(asin_lower(first.x.lo)+asin_lower(second.x.lo));
            I squared_gap=norm2(diff+n2-n1);
            I penalty=first.x*second.x*squared_gap/(2*(first.x+second.x));
            return I(std::min((bound-penalty).hi,(area+flank+price).hi));
        });
}

bool verify_mark_triple(){
    const I u=pi/14;
    const Trig at=trig(u);
    const I root=rt(1-sq(R*at.s)),t=R*at.c-root,x=t*at.s;
    const I slope=(1+2*(1-2*sq(x)-lambda)/rt(1-sq(x)))*t*(R*sq(at.s)/root+at.c)/2;
    const I cap=3*mark_at(x)-rat(21,100);
    const I radial(min_outer.lo,rat(104,25).hi),gap(0,(2*M).hi);
    const std::array<I,7> initial{radial,radial,radial,radial,gap,gap,gap};
    return verify_boxes("mark-triple-fourteen",initial,std::array<real,7>{1,1,1,1,4,4,4},cap,
        [&](const auto& box,bool& valid){
            if(box[0].lo>box[3].hi){valid=false;return I(0);}
            std::array<I,3> d{box[4],box[5],box[6]};
            for(int i=0;i<3;i++)if(!intersect(d[i],I(0,(rim_width_upper(box[i].hi)+rim_width_upper(box[i+1].hi)).hi))){
                valid=false;return I(0);
            }
            Trig f=trig(d[0]),g=trig(d[1]),h=trig(d[2]);
            std::array<V,4> p{box[0]*V{f.c,-f.s},V{box[1],0},box[2]*unit(g),box[3]*unit(trig(d[1]+d[2]))};
            std::array<Edge,3> e;
            std::array<Trig,3> trig_d{f,g,h};
            I bound=slope*(6*u-d[0]-d[1]-d[2]),xs=0;
            for(int i=0;i<3;i++){
                if(!edge(box[i],box[i+1],trig_d[i],p[i],p[i+1],e[i])){valid=false;return I(0);}
                bound=bound+mark_upper(e[i].x);
                xs=xs+e[i].x;
            }
            if(bound.hi<cap.lo || xs.lo<=0)return bound;
            std::array<V,3> q,ideal;
            for(int i=0;i<3;i++){
                if(e[i].x.lo<=0)return bound;
                V n=e[i].inward_scaled/e[i].x;
                q[i]=e[i].midpoint+e[i].h*n;
                ideal[i]=q[i]+n;
            }
            I loss=0;
            for(int i=0;i<3;i++)for(int j=i+1;j<3;j++){
                if(norm2(q[i]-q[j]).lo>4){valid=false;return I(0);}
                loss=loss+e[i].x*e[j].x*norm2(ideal[i]-ideal[j]);
            }
            return bound-loss/(2*xs);
        });
}

namespace octagon_joint {

constexpr int trig_bins=8192;

Trig fast_trig(I angle){
    static const auto table=[]{
        std::vector<Trig> values(2*trig_bins+1);
        for(int i=0;i<=2*trig_bins;i++)values[i]=trig_point(real(i)/trig_bins);
        return values;
    }();
    if(angle.lo< -2||angle.hi>2)throw std::domain_error("signed angle outside [-2,2]");
    auto nonnegative=[&](I a){
        int l=static_cast<int>(std::floor(a.lo*trig_bins)),h=static_cast<int>(std::ceil(a.hi*trig_bins));
        I sine(std::min(table[l].s.lo,table[h].s.lo),
               real(l)/trig_bins<=(pi/2).hi&&real(h)/trig_bins>=(pi/2).lo?1:std::max(table[l].s.hi,table[h].s.hi));
        return Trig{sine,I(table[h].c.lo,table[l].c.hi)};
    };
    if(angle.lo>=0)return nonnegative(angle);
    if(angle.hi<=0){
        Trig t=nonnegative(-angle);
        return {-t.s,t.c};
    }
    Trig l=nonnegative(I(0,-angle.lo)),h=nonnegative(I(0,angle.hi));
    return {I(-l.s.hi,h.s.hi),I(std::min(l.c.lo,h.c.lo),1)};
}

I rim_width(I t){
    static const auto lower=[]{
        std::vector<real> values(mesh+1);
        for(int i=0;i<=mesh;i++){
            real x=3.+real(i)/mesh;
            values[i]=x<=min_outer.hi?0:x>=T.hi?M.lo:asin_i(radial_q(I(x))/R).lo;
        }
        return values;
    }();
    int l=std::clamp(static_cast<int>(std::floor(t.lo*mesh))-3*mesh,0,mesh);
    return {lower[l],rim_width_upper(t.hi).hi};
}

I angle_from_cosine(I cosine){
    if(cosine.hi< -1||cosine.lo>1)throw std::domain_error("invalid cosine bounds");
    cosine.lo=std::max(cosine.lo,-1.);
    cosine.hi=std::min(cosine.hi,1.);
    auto f=[](real c){
        I sine=rt(nonneg(1-sq(I(c))));
        I radius=rt(R2+1-2*R*c);
        return asin_mesh(sine/radius);
    };
    I peak=1/R;
    I low=f(cosine.lo),high=f(cosine.hi);
    real upper=cosine.lo<=peak.hi&&cosine.hi>=peak.lo?M.hi:std::max(low.hi,high.hi);
    return {std::min(low.lo,high.lo),upper};
}
real endpoint_upper(I a,I t,I phi,I p){
    I beta=asin_mesh(2/t);
    if(!intersect(phi,I(-beta.hi,beta.hi)))return -inf;
    Trig angle=fast_trig(phi);
    I versine=nonneg(1-angle.c);
    I radial=t-a+a*versine,tangent=a*angle.s;
    I x2=(sq(a-t)+2*a*t*versine)/4;
    if(!intersect(x2,I(0,1)))return -inf;

    // Return the half reward plus phi/2, so the phase terms can cancel
    // across the two ends of an ordinary seam.
    real upper=(rim_width_upper(std::min(T.hi,(a+2).hi))+p/2).hi;
    if(x2.lo<=0)return upper;

    I x=rt(x2),h=rt(nonneg(1-x2)),ratio=h/x;
    I c=(radial-ratio*tangent)/2,s=(tangent+ratio*radial)/2;
    I turn=asin_mesh(tangent/(2*x))+pi/2-asin_mesh(x);
    if(turn.lo>=-2&&turn.hi<=2){
        Trig exact=fast_trig(turn);
        if(!intersect(c,exact.c)||!intersect(s,exact.s))return -inf;
    }
    if(!intersect(c,I(-1,1))||!intersect(s,I(-1,1)))return -inf;

    // Coordinates relative to K's ray. Both W and Y are one unit from K.
    V W{t-c,-s};
    I q2((sq(I(t.lo))+1-2*I(t.lo)*c.hi).lo,(sq(I(t.hi))+1-2*I(t.hi)*c.lo).hi);
    if(!intersect(q2,norm2(W)))return -inf;
    I q=rt(nonneg(q2));
    if(!intersect(q,I(S.lo,std::min({(T+1).hi,(a+1).hi,(t+1).hi}))))return -inf;
    I alpha=asin_mesh(s/q);
    I arc2=4-sq(R-q);
    if(arc2.hi<0)return -inf;
    arc2=nonneg(arc2);
    I gam=2*asin_mesh(rt(nonneg(arc2/(4*R*q))));
    I from_w=(gam+alpha)/2;
    upper=std::min({upper,from_w.hi,(rim_width_upper((q+1).hi)+p/2).hi});

    I axial=(T2/t-t)/2;
    if(!intersect(axial,I(0,1)))return -inf;
    I ordin=rt(nonneg(1-sq(axial)));
    I yx=rt(nonneg(R2-sq(ordin)));
    real best=(p/2).hi;  // The intersection K, or a filler starting after Y.

    // The distance from a midpoint to the third point can be written
    // using just the two distances from the midpoint's endpoints.
    I chord=sq(c+axial)+sq(s-ordin);
    chord.lo=std::max(chord.lo,(2+2*(c*axial-s*ordin)).lo);
    I difference=(gam+alpha-p)/2;
    if((chord+4*R2*sq(fast_trig(difference).s)).lo<=4)
        best=std::max(best,from_w.hi);
    I y_difference=(alpha-p-2*M)/2;
    if((chord+sq(R-q)+4*R*q*sq(fast_trig(y_difference).s)).lo<=4)
        best=std::max(best,(M+p/2).hi);

    // The other circle intersection is W+Y-K. Its arc either starts
    // at Y or ends there, according to the sign of the oriented offset.
    if((s*yx+c*ordin).hi>=0){
        I cosine=(c*yx-s*ordin)/R;
        if(intersect(cosine,I(-1,1)))
            best=std::max(best,(angle_from_cosine(cosine)+p/2).hi);
    }
    return std::min(upper,best);
}
enum Role { regular=0,empty=1,ear=2 };
constexpr int roles=3, total_roles=roles*roles;
using Scores=std::array<real,total_roles>;

struct SeamGeometry {
    I a,b,d,half_sine,half_cosine,outer_radius,outer_phase;
    V inner;
};

bool seam_geometry(I a,I b,I d,SeamGeometry& result){
    Trig h=fast_trig(d/2);
    Edge e;
    if(!edge(a,b,fast_trig(d),a*V{h.c,-h.s},b*unit(h),e))return false;
    I q=e.radius;
    if(!intersect(q,I(S.lo,(R+1).hi)))return false;
    if(h.s.lo>0&&!intersect(q,I(S.lo,(1/h.s).hi)))return false;
    I beta=asin_mesh(1/q);
    if(e.x.lo<=0)throw std::domain_error("degenerate positive-span seam");
    I scale=e.h/e.x;
    I diff=(b-a)/2,sum=(a+b)/2;
    I phase=d/2+asin_mesh(diff*(h.s-scale*h.c)/q);
    if(!intersect(phase,I((d-beta).lo,beta.hi)))return false;
    V inner{sum*(h.c-scale*h.s),diff*(h.s+scale*h.c)};
    I inverse=q*fast_trig(d).c-2*h.c*rt(nonneg(1-sq(q*h.s)));
    inner.x.lo=std::max(inner.x.lo,inverse.lo);
    if(inner.x.lo>inner.x.hi)return false;
    result={a,b,d,h.s,h.c,q,phase,inner};
    return true;
}

bool phase_window(const SeamGeometry& seam,I t,I& phi){
    I q=seam.outer_radius;
    I discr=1-sq(t-q);
    if(discr.hi<0)return false;
    I psi=2*asin_mesh(rt(nonneg(discr/(4*t*q))));
    I reach=asin_mesh(2/t);
    return intersect(phi,seam.outer_phase+I(-psi.hi,psi.hi))&&
           intersect(phi,I(std::max(-reach.hi,(seam.d-reach).lo),std::min(reach.hi,(seam.d+reach).hi)));
}

I fan_upper(real t){
    static const auto table=[]{
        std::vector<real> values(mesh+1);
        for(int i=0;i<=mesh;i++){
            real radius=std::max(3.+real(i)/mesh,min_outer.hi);
            if(radius>=td.lo)values[i]=Fd.hi;
            else{
                I q=radial_q(I(radius));
                values[i]=(fan_price*asin_i(q/R)-radius*q+2*lambda*asin_i(q)).hi;
            }
        }
        return values;
    }();
    int index=std::clamp(static_cast<int>(std::ceil(t*mesh))-3*mesh,0,mesh);
    return I(table[index]);
}

const I marked_peak=1+2*lambda-lambda*pi/2;
const I area_needed=pi*R2+2*pi*lambda-15*marked_peak+rat(123,1000)-7*Fd;
struct SearchBox {I t,phi;};

Scores seam_scores(const SeamGeometry& seam,real resolution,bool ears,I kappa,I area_price,std::uint64_t& visits){
    Scores output;output.fill(-inf);
    Scores guide=output;
    I t(std::max(min_outer.lo,(seam.outer_radius-1).lo),
        std::min(T.hi,(seam.outer_radius+1).hi));
    if(t.lo>t.hi)return output;
    I phi(-1,1);
    if(!phase_window(seam,t,phi))return output;
    std::vector<SearchBox> pending{{t,phi}};

    auto evaluate=[&](I t,I phi,bool sample){
        Scores values;values.fill(-inf);
        I p=rim_width(t),other=seam.d-phi;
        real le=endpoint_upper(seam.a,t,phi,p),re=endpoint_upper(seam.b,t,other,p);
        I cone=asin_mesh(1/t);
        Trig centered=fast_trig(phi-seam.d/2);
        I twice_area=t*((seam.a+seam.b)*seam.half_sine*centered.c
                        +(seam.a-seam.b)*seam.half_cosine*centered.s);
        I area=area_price*(twice_area/2+fan_upper(t.hi));
        std::array<I,roles> phase_price{I(.5),kappa,I(0)};
        for(int i=0;i<(ears?roles:2);i++)for(int j=0;j<(ears?roles:2);j++){
            if(i==empty&&j==empty)continue;
            if((i==regular&&le==-inf)||(j==regular&&re==-inf))continue;
            int empties=int(i==empty)+int(j==empty),ears_here=int(i==ear)+int(j==ear);
            I score=(1+empties*kappa-I(.5)*ears_here)*p+I(.5)*ears_here*cone
                   -phase_price[j]*seam.d-(phase_price[i]-phase_price[j])*phi;
            score=score+area;
            if(i==regular)score=score+le;
            if(j==regular)score=score+re;
            real value=score.hi;
            values[i*roles+j]=value;
            if(sample)guide[i*roles+j]=std::max(guide[i*roles+j],value);
        }
        return values;
    };

    while(!pending.empty()){
        SearchBox box=pending.back();pending.pop_back();
        if(!phase_window(seam,box.t,box.phi))continue;
        ++visits;
        Scores values=evaluate(box.t,box.phi,false);
        real dt=box.t.hi-box.t.lo,dp=box.phi.hi-box.phi.lo;
        bool done=std::max(dt,dp)<=resolution;
        if(!done){
            real mt=box.t.lo+dt/2,mp=box.phi.lo+dp/2;
            I sample_phi=I(mp);
            if(phase_window(seam,I(mt),sample_phi))evaluate(I(mt),sample_phi,true);
            done=true;
            for(int i=0;i<total_roles;i++){
                if(values[i]==-inf||values[i]<=output[i])continue;
                if(guide[i]==-inf||values[i]>up(guide[i]+.008)){done=false;break;}
            }
        }
        if(done){
            for(int i=0;i<total_roles;i++)output[i]=std::max(output[i],values[i]);
            continue;
        }
        SearchBox other=box;
        I& first=dt>=dp?box.t:box.phi;
        I& second=dt>=dp?other.t:other.phi;
        real mid=first.lo+(first.hi-first.lo)/2;
        first.hi=second.lo=mid;
        pending.push_back(box);
        pending.push_back(other);
    }
    return output;
}

struct LocalCell {
    I d,tilt;
    V inner;
    Scores scores;
};

std::vector<I> grid(I range,int steps){
    int start=static_cast<int>(std::floor(range.lo*steps));
    int finish=static_cast<int>(std::floor(range.hi*steps));
    std::vector<I> out;
    for(int i=start;i<=finish;i++){
        I b(real(i)/steps,real(i+1)/steps);
        if(intersect(b,range))out.push_back(b);
    }
    return out;
}

std::vector<std::vector<LocalCell>> prepare(const std::vector<I>& radii,int angle_steps,int inner_steps,bool ears,I kappa,I area_price,int workers){
    I min_gap=2*pi-7*rat(737,1000)-rat(7,4)*(15*M-pi),max_gap=2*asin_i(1/S);
    auto angles=grid(I(min_gap.lo,max_gap.hi),angle_steps);
    int n=static_cast<int>(radii.size());
    std::vector<std::vector<LocalCell>> cells(n*n);
    std::atomic<int> next{0};
    std::uint64_t count=0,visits=0;
    int completed=0;
    std::mutex report;
    auto work=[&]{
        if(std::fegetround()!=FE_TONEAREST)throw std::runtime_error("interval worker rounding mode");
        for(int i=next.fetch_add(1);i<n;i=next.fetch_add(1)){
            std::uint64_t local_count=0,local_visits=0;
            for(int j=i;j<n;j++){
                auto& forward=cells[i*n+j];
                auto& reverse=cells[j*n+i];
                for(I d:angles){
                    SeamGeometry seam;
                    if(!seam_geometry(radii[i],radii[j],d,seam))continue;
                    auto scores=seam_scores(seam,1./inner_steps,ears,kappa,area_price,local_visits);
                    if(std::all_of(scores.begin(),scores.end(),[](real z){return z==-inf;}))continue;
                    ++local_count;
                    I tilt=seam.half_sine*(seam.inner.x-1);
                    forward.push_back({d,tilt,seam.inner,scores});
                    if(i!=j){
                        Scores flipped;
                        for(int a=0;a<roles;a++)for(int b=0;b<roles;b++)flipped[a*roles+b]=scores[b*roles+a];
                        reverse.push_back({d,tilt,V{seam.inner.x,-seam.inner.y},flipped});
                    }else{
                        // Equal radial bins contain both orderings already.
                        for(int a=0;a<roles;a++)for(int b=a+1;b<roles;b++)
                            forward.back().scores[a*roles+b]=forward.back().scores[b*roles+a]=
                                std::max(scores[a*roles+b],scores[b*roles+a]);
                    }
                }
            }
            std::lock_guard<std::mutex> lock(report);
            ++completed;
            count+=local_count;visits+=local_visits;
            if(completed%8==0||completed==n)
                std::cout<<"seam rows "<<completed<<'/'<<n<<" cells "<<count<<" subboxes "<<visits<<'\n'<<std::flush;
        }
    };
    std::vector<std::future<void>> pool;
    for(int i=1;i<workers;i++)pool.push_back(std::async(std::launch::async,work));
    work();
    for(auto& worker:pool)worker.get();
    return cells;
}

using MatrixSet=std::array<GapMatrix,total_roles>;

GapMatrix path(const MatrixSet& mat,const std::array<Role,8>& ring,int first,int count,int n){
    auto seam=[&](int i)->const GapMatrix&{return mat[ring[i%8]*roles+ring[(i+1)%8]];};
    GapMatrix result=seam(first);
    for(int i=1;i<count;i++)result=gap_path_join(result,seam(first+i),n);
    return result;
}

struct OctagonPattern {
    std::array<Role,8> ring{};
    int zero,ear0,ear1;
    bool passed=false;
};

std::vector<OctagonPattern> octagon_patterns(int length){
    std::vector<OctagonPattern> patterns;
    auto add=[&](int z,int ear0,int ear1){
        OctagonPattern p{{},z,ear0,ear1};
        p.ring[z]=empty;
        if(ear0>=0)p.ring[ear0]=ear;
        if(ear1>=0)p.ring[ear1]=ear;
        patterns.push_back(p);
    };
    auto ordinary=length==4?std::vector<int>{0,1,2}:std::vector<int>{0,1,4,5};
    for(int z:ordinary)add(z,-1,-1);
    if(length==3){
        for(auto [ear0,z]:octagon_single_ears)add(z,ear0,-1);
        add(0,3,4);
    }
    return patterns;
}

bool joint_relaxed(const std::vector<I>& radii,const std::vector<std::vector<LocalCell>>& cells,int length,
                   std::vector<OctagonPattern>& patterns,I tilt,I area_price){
    int n=static_cast<int>(radii.size());
    static constexpr std::array<real,13> core_cap{{.375,.5,.625,.75,.875,1.,1.125,1.25,1.5,1.75,2.,2.5,3.}};
    constexpr int unit_bin=5;
    constexpr int caps=static_cast<int>(core_cap.size());
    std::array<real,caps> norm_limit;
    for(int k=0;k<caps;k++)norm_limit[k]=sq(1+I(core_cap[k])).hi;
    struct Profile {I slope;std::vector<std::array<GapMatrix,2>> paths;};
    std::vector<Profile> profiles;
    for(int s=65;s<=225;s+=10){
        Profile p;
        p.slope=rat(s,100);
        std::array<MatrixSet,caps> matrices_by_core;
        for(auto& set:matrices_by_core)for(auto& m:set)m.assign(cells.size(),-inf);
        for(std::size_t i=0;i<cells.size();i++)for(const LocalCell& cell:cells[i]){
            real radius2=norm2(cell.inner).lo;
            auto it=std::lower_bound(norm_limit.begin(),norm_limit.end(),radius2);
            if(it==norm_limit.end())continue;
            auto& m=matrices_by_core[static_cast<std::size_t>(it-norm_limit.begin())];
            I extra=p.slope*cell.d-tilt*cell.tilt;
            for(int role=0;role<total_roles;role++)if(cell.scores[role]!=-inf)
                m[role][i]=std::max(m[role][i],up(cell.scores[role]+extra.hi));
        }
        for(int k=1;k<caps;k++)for(int role=0;role<total_roles;role++)
            for(std::size_t i=0;i<cells.size();i++)
                matrices_by_core[k][role][i]=std::max(matrices_by_core[k][role][i],matrices_by_core[k-1][role][i]);
        p.paths.resize(patterns.size()*caps);
        for(std::size_t j=0;j<patterns.size();j++)if(!patterns[j].passed)for(int k=0;k<caps;k++){
            const auto& ring=patterns[j].ring;
            auto& pp=p.paths[j*caps+k];
            pp[0]=path(matrices_by_core[k],ring,0,length,n);
            if(length==4||k<=unit_bin)pp[1]=path(matrices_by_core[k],ring,length,8-length,n);
        }
        profiles.push_back(std::move(p));
    }
    I bound=2*asin_i(1/S),allow=rat(7,4)*(15*M-pi);
    auto side_cap=[&](int edges){return std::min((edges*bound).hi,(edges*rat(737,1000)+allow).hi);};
    auto spans=grid(I((2*pi-side_cap(8-length)).lo,side_cap(length)),128);
    struct BridgeEntry {
        I span,refund;
        int first,second,cap;
    };
    std::vector<BridgeEntry> bridge;
    for(int i=0;i<n;i++)for(int j=0;j<n;j++){
        if(radii[i].lo>3||radii[j].lo>3)continue;
        for(I span:spans){
            Trig half=gap_bridge_trig(span/2);
            I difference=sq(radii[i]-radii[j])/4,product=radii[i]*radii[j];
            I chord2=difference+product*sq(half.s);
            if(!intersect(chord2,I(0,4)))continue;
            I diameter=2*rt(nonneg(1-sq(nonneg(rt(chord2)-1))));
            I midpoint2=difference+product*sq(half.c);
            // Both cores are within distance two of each bridge endpoint.
            I radius=rt(midpoint2)+rt(nonneg(4-chord2));
            auto cap=std::lower_bound(core_cap.begin(),core_cap.end(),std::min(3.,radius.hi))-core_cap.begin();
            bridge.push_back({span,tilt*half.s*diameter,i,j,static_cast<int>(cap)});
        }
    }
    bool passed=true;
    for(std::size_t j=0;j<patterns.size();j++){
        OctagonPattern& pattern=patterns[j];
        if(pattern.passed)continue;
        I budget=area_price*(area_needed+(int(pattern.ear0>=0)+int(pattern.ear1>=0))*rat(98,1000));
        real best=-inf;
        std::uint64_t pending=0;
        BridgeEntry critical{};
        for(const auto& box:bridge){
            int i0=box.first*n+box.second,i1=box.second*n+box.first;
            int normal=box.cap,primary=std::min(box.cap,unit_bin);
            real first=inf,second=inf,first_primary=inf,second_primary=inf;
            for(const auto& p:profiles){
                const auto& ordinary=p.paths[j*caps+normal];
                const auto& inside=p.paths[j*caps+primary];
                I a=-p.slope*box.span,b=-p.slope*(2*pi-box.span);
                first=std::min(first,(I(ordinary[0][i0])+a).hi);
                second_primary=std::min(second_primary,(I(inside[1][i1])+b).hi);
                if(length==4){
                    second=std::min(second,(I(ordinary[1][i1])+b).hi);
                    first_primary=std::min(first_primary,(I(inside[0][i0])+a).hi);
                }
            }
            real path_upper=up(first+second_primary);
            if(length==4)path_upper=std::max(path_upper,up(first_primary+second));
            real upper=(I(path_upper)+box.refund-budget).hi;
            if(upper>best){best=upper;critical=box;}
            if(upper>=pi.lo)++pending;
        }
        std::cout<<"joint length "<<length<<" zero "<<pattern.zero<<" ears "<<pattern.ear0<<','<<pattern.ear1
                 <<" tilt "<<tilt.lo<<" area "<<area_price.lo<<" score "<<std::setprecision(12)
                 <<best<<" survivors "<<pending<<" worst "<<radii[critical.first].lo<<' '
                 <<radii[critical.second].lo<<' '<<critical.span.lo<<'\n'<<std::flush;
        pattern.passed=!pending;
        passed=passed&&pattern.passed;
    }
    return passed;
}

bool verify(int length){
    const I area_price=rat(1,5);
    auto radii=grid(I((R-3).lo,min_outer.hi),32);
    const int workers=static_cast<int>(std::clamp(std::thread::hardware_concurrency(),1u,8u));
    const bool ears=length==3;
    auto cells=prepare(radii,128,128,ears,I(1),area_price,workers);
    auto patterns=octagon_patterns(length);
    for(int tilt:{240,270,300,330,360,390,420,450,210,180,150}){
        if(joint_relaxed(radii,cells,length,patterns,rat(tilt,1000),area_price))return true;
    }
    return false;
}

} // namespace octagon_joint

namespace nine_joint {

using octagon_joint::fast_trig;
using octagon_joint::rim_width;
using octagon_joint::fan_upper;
using octagon_joint::endpoint_upper;
using octagon_joint::grid;
using octagon_joint::SeamGeometry;
using octagon_joint::phase_window;

constexpr int ring=9,roles=4,edge_roles=roles*roles,cap_roles=edge_roles*roles;
enum Role { regular=0,empty=1,multiple=2,shared=3 };
using Scores=std::array<real,edge_roles>;

struct Pattern {
    int which;
    std::array<Role,ring> layout{};
    bool passed=false;
};

int popcount(int mask){
    int count=0;
    for(;mask;mask&=mask-1)++count;
    return count;
}

std::vector<Pattern> layouts(int which){
    std::vector<Pattern> result;
    for(int g=0;g<ring;g++){
        bool allowed[ring][ring]{};
        for(auto [site,a,b]:nine_joint_cases[which].remaining)if(site==g)allowed[a][b]=true;
        for(int zmask=0;zmask<(1<<ring);zmask++){
            if(zmask&(1<<g))continue;
            int zeros=popcount(zmask);
            if(zeros<2||zeros>7)continue;
            bool possible=true;
            for(int a=0;a<ring;a++)if(zmask&(1<<a))for(int b=a+1;b<ring;b++)if(zmask&(1<<b))
                possible=possible&&allowed[a][b];
            if(!possible)continue;
            int filled=((1<<ring)-1)^zmask^(1<<g);
            for(int doubles=filled;;doubles=(doubles-1)&filled){
                if(popcount(doubles)==zeros-2){
                    Pattern p{which,{}};
                    p.layout[g]=shared;
                    for(int i=0;i<ring;i++){
                        if(zmask&(1<<i))p.layout[i]=empty;
                        if(doubles&(1<<i))p.layout[i]=multiple;
                    }
                    result.push_back(p);
                }
                if(doubles==0)break;
            }
        }
    }
    return result;
}

int tag(Role a,Role b){return int(a)*roles+int(b);}
int triple(Role a,Role b,Role c){return roles*tag(a,b)+int(c);}
int reverse_edge(int id){return tag(Role(id%roles),Role(id/roles));}
int reverse_cap(int id){return triple(Role(id%roles),Role(id/roles%roles),Role(id/edge_roles));}

bool geometry(I a,I b,I d,SeamGeometry& result){
    Trig h=fast_trig(d/2),full=fast_trig(d);
    V A=a*V{h.c,-h.s},B=b*unit(h);
    Edge e;
    if(!edge(a,b,full,A,B,e))return false;
    I q=e.radius;
    if(!intersect(q,I(S.lo,R.hi)))return false;
    if(h.s.lo>0&&!intersect(q,I(S.lo,(1/h.s).hi)))return false;
    I beta=asin_mesh(1/q);
    I phase((d-beta).lo,beta.hi);
    if(phase.lo>phase.hi)return false;
    V inner{
        I(std::max((A.x-1).lo,(B.x-1).lo),std::min((A.x+1).hi,(B.x+1).hi)),
        I(std::max((A.y-1).lo,(B.y-1).lo),std::min((A.y+1).hi,(B.y+1).hi))
    };
    if(e.x.lo>0){
        I scale=e.h/e.x,diff=(b-a)/2,mean=(a+b)/2;
        if(!intersect(phase,d/2+asin_mesh(diff*(h.s-scale*h.c)/q)))return false;
        if(!intersect(inner.x,mean*(h.c-scale*h.s))||
           !intersect(inner.y,diff*(h.s+scale*h.c)))return false;
    }
    I projection=q*full.c-2*h.c*rt(nonneg(1-sq(q*h.s)));
    inner.x.lo=std::max(inner.x.lo,projection.lo);
    if(inner.x.lo>inner.x.hi||inner.y.lo>inner.y.hi)return false;
    result={a,b,d,h.s,h.c,q,phase,inner};
    return true;
}

const I marked_peak=1+2*lambda-lambda*pi/2;
const I area_needed=pi*R2+2*pi*lambda-14*marked_peak+rat(11379,10000)+rat(42,100)-6*Fd;

Scores seam_scores(const SeamGeometry& seam,const std::array<bool,edge_roles>& needed,
                   I kappa,I shared_phase,I area_price,real resolution,std::uint64_t& visited){
    Scores output;output.fill(-inf);
    Scores guide=output;
    I t(std::max(min_outer.lo,(seam.outer_radius-1).lo),std::min(T.hi,(seam.outer_radius+1).hi));
    if(t.lo>t.hi)return output;
    I phase(-1,1);
    if(!phase_window(seam,t,phase))return output;
    using Box=std::array<I,2>;
    std::vector<Box> pending{{t,phase}};
    auto evaluate=[&](I radius,I phi,bool sample){
        Scores values;values.fill(-inf);
        I p=rim_width(radius),other=seam.d-phi;
        real first=endpoint_upper(seam.a,radius,phi,p),last=endpoint_upper(seam.b,radius,other,p);
        I cone=asin_mesh(2/radius);
        Trig centered=fast_trig(phi-seam.d/2);
        I polygon=radius*((seam.a+seam.b)*seam.half_sine*centered.c
                          +(seam.a-seam.b)*seam.half_cosine*centered.s)/2;
        I fan=fan_upper(radius.hi);
        std::array<I,roles> price{I(.5),kappa,I(0),shared_phase};
        for(int id=0;id<edge_roles;id++){
            if(!needed[id])continue;
            int a=id/roles,b=id%roles;
            if((a==regular&&first==-inf)||(b==regular&&last==-inf))continue;
            int blanks=int(a==empty)+int(b==empty),doubles=int(a==multiple)+int(b==multiple);
            I fraction=1-I(.5)*(int(a==shared)+int(b==shared));
            I score=(fraction+blanks*kappa-I(.5)*doubles)*p+I(.5)*doubles*cone
                    -price[b]*seam.d-(price[a]-price[b])*phi+area_price*(polygon+fraction*fan);
            if(a==regular)score=score+first;
            if(b==regular)score=score+last;
            values[id]=score.hi;
            if(sample)guide[id]=std::max(guide[id],values[id]);
        }
        return values;
    };
    while(!pending.empty()){
        Box box=pending.back();pending.pop_back();
        if(!phase_window(seam,box[0],box[1]))continue;
        ++visited;
        Scores score=evaluate(box[0],box[1],false);
        real dt=box[0].hi-box[0].lo,dp=box[1].hi-box[1].lo;
        bool done=std::max(dt,dp)<=resolution;
        if(!done){
            I center(box[1].lo+dp/2);
            I radius(box[0].lo+dt/2);
            if(phase_window(seam,radius,center))evaluate(radius,center,true);
            done=true;
            for(int id=0;id<edge_roles;id++){
                if(score[id]==-inf||score[id]<=output[id])continue;
                if(guide[id]==-inf||score[id]>up(guide[id]+.008)){done=false;break;}
            }
        }
        if(done){
            for(int id=0;id<edge_roles;id++)output[id]=std::max(output[id],score[id]);
        }else{
            int axis=dt>=dp?0:1;
            Box other=box;
            real midpoint=box[axis].lo+(box[axis].hi-box[axis].lo)/2;
            box[axis].hi=other[axis].lo=midpoint;
            pending.push_back(box);
            pending.push_back(other);
        }
    }
    return output;
}

template<std::size_t N>
struct LocalCell {
    I d,tilt;
    real q_norm;
    std::array<real,N> scores;
};

template<std::size_t N>
using Cells=std::vector<std::vector<LocalCell<N>>>;

Cells<edge_roles> make_seams(const std::vector<I>& radii,const std::array<bool,edge_roles>& needed,
                            I kappa,I shared_phase,I area_price,int angle_steps,int inner_steps,int workers){
    auto angles=grid(I(0,(2*asin_i(1/S)).hi),angle_steps);
    int n=static_cast<int>(radii.size());
    Cells<edge_roles> result(n*n);
    std::atomic<int> next{0};
    std::mutex mutex;
    int completed=0;
    std::uint64_t boxes=0,entries=0;
    auto work=[&]{
        if(std::fegetround()!=FE_TONEAREST)throw std::runtime_error("interval worker rounding mode");
        for(int i=next.fetch_add(1);i<n;i=next.fetch_add(1)){
            std::uint64_t visits=0,cells=0;
            for(int j=i;j<n;j++)for(I d:angles){
                SeamGeometry seam;
                if(!geometry(radii[i],radii[j],d,seam))continue;
                Scores scores=seam_scores(seam,needed,kappa,shared_phase,area_price,1./inner_steps,visits);
                if(std::all_of(scores.begin(),scores.end(),[](real s){return s==-inf;}))continue;
                ++cells;
                I tilt=seam.half_sine*(seam.inner.x-1);
                real norm=norm2(seam.inner).lo;
                if(i==j){
                    for(int k=0;k<edge_roles;k++)
                        scores[k]=scores[reverse_edge(k)]=std::max(scores[k],scores[reverse_edge(k)]);
                }
                result[i*n+j].push_back({d,tilt,norm,scores});
                if(i!=j){
                    Scores reflected;
                    for(int k=0;k<edge_roles;k++)reflected[k]=scores[reverse_edge(k)];
                    result[j*n+i].push_back({d,tilt,norm,reflected});
                }
            }
            std::lock_guard<std::mutex> lock(mutex);
            boxes+=visits;entries+=cells;++completed;
            if(completed%8==0||completed==n)
                std::cout<<"nine seam rows "<<completed<<'/'<<n<<" cells "<<entries<<" boxes "<<boxes<<'\n'<<std::flush;
        }
    };
    std::vector<std::future<void>> pool;
    for(int i=1;i<workers;i++)pool.push_back(std::async(std::launch::async,work));
    work();
    for(auto& worker:pool)worker.get();
    return result;
}

Cells<cap_roles> make_caps(const std::vector<I>& radii,const Cells<edge_roles>& seams,
                          const std::array<bool,edge_roles>& need_edge,const std::array<bool,cap_roles>& needed){
    int n=static_cast<int>(radii.size());
    Cells<cap_roles> result(n*n);
    if(std::none_of(needed.begin(),needed.end(),[](bool value){return value;}))return result;

    const std::array<I,10> prices{{0,rat(35,100),rat(65,100),rat(9,10),rat(11,10),
                                    rat(13,10),rat(155,100),rat(18,10),rat(205,100),rat(23,10)}};
    using Matrices=std::array<GapMatrix,edge_roles>;
    std::vector<Matrices> legs;
    for(I price:prices){
        Matrices p;
        for(int k=0;k<edge_roles;k++)if(need_edge[k])p[k].assign(seams.size(),-inf);
        for(std::size_t i=0;i<seams.size();i++)for(const auto& cell:seams[i]){
            I extra=price*cell.d;
            for(int k=0;k<edge_roles;k++)if(need_edge[k]&&cell.scores[k]!=-inf)
                p[k][i]=std::max(p[k][i],up(cell.scores[k]+extra.hi));
        }
        legs.push_back(std::move(p));
    }

    I cap_span=rat(1152,1000)+rat(7,4)*(14*M-pi);
    auto angles=grid(I(0,cap_span.hi),128);
    struct Base {I angle,tilt;real q_norm;int apex;};
    std::vector<int> cap_tags;
    for(int k=0;k<cap_roles;k++)if(needed[k])cap_tags.push_back(k);
    std::vector<std::vector<GapMatrix>> prefix(prices.size(),std::vector<GapMatrix>(cap_tags.size(),GapMatrix(n)));
    for(int i=0;i<n;i++)for(int j=i;j<n;j++){
        I a=radii[i],b=radii[j],mean=(a+b)/2,product=a*b;
        std::vector<Base> bases;
        for(I d:angles){
            Trig half=fast_trig(d/2),full=fast_trig(d);
            I x2=sq(a-b)/4+product*sq(half.s);
            if(!intersect(x2,I(0,1)))continue;
            I x=rt(x2),h=rt(nonneg(1-x2));
            I factor(0,(2*rt(product)).hi);
            real qx=(mean*half.c-1).lo;
            if(x.lo>0){
                if(!intersect(factor,product*full.s/x))continue;
                I tighter=mean*(half.c-(h/x)*half.s);
                qx=std::max(qx,tighter.lo);
            }
            I outward=rt(nonneg(1+product*full.c+h*factor));
            I inward2=nonneg(1+product*full.c-h*factor);
            real upper=up(std::min({outward.hi,(a+1).hi,(b+1).hi})+1);
            auto limit=std::upper_bound(radii.begin(),radii.end(),upper,[](real u,I r){return u<r.lo;});
            if(limit==radii.begin())continue;
            int apex=static_cast<int>(limit-radii.begin())-1;
            bases.push_back({d,half.s*(I(qx)-1),inward2.lo,apex});
        }
        if(bases.empty())continue;
        for(std::size_t p=0;p<prices.size();p++)for(std::size_t r=0;r<cap_tags.size();r++){
            int id=cap_tags[r],left=id/roles,right=id%edge_roles;
            const auto& first=legs[p][left];
            const auto& last=legs[p][right];
            real best=-inf;
            for(int k=0;k<n;k++){
                real sum=first[i*n+k]+last[k*n+j];
                if(sum!=-inf)best=std::max(best,up(sum));
                prefix[p][r][k]=best;
            }
        }
        for(const Base& base:bases){
            std::array<real,cap_roles> scores;scores.fill(-inf);
            std::vector<I> undo;
            for(I price:prices)undo.push_back(-price*base.angle);
            for(std::size_t r=0;r<cap_tags.size();r++){
                real value=inf;
                for(std::size_t p=0;p<prices.size();p++){
                    real left=prefix[p][r][base.apex];
                    if(left==-inf){value=-inf;break;}
                    value=std::min(value,(I(left)+undo[p]).hi);
                }
                scores[cap_tags[r]]=value;
            }
            if(i==j){
                for(int k:cap_tags)scores[k]=scores[reverse_cap(k)]=std::max(scores[k],scores[reverse_cap(k)]);
            }
            result[i*n+j].push_back({base.angle,base.tilt,base.q_norm,scores});
            if(i!=j){
                std::array<real,cap_roles> reflected;reflected.fill(-inf);
                for(int k:cap_tags)reflected[k]=scores[reverse_cap(k)];
                result[j*n+i].push_back({base.angle,base.tilt,base.q_norm,reflected});
            }
        }
    }
    std::cout<<"nine cap matrices ready\n"<<std::flush;
    return result;
}

bool is_cap(const NineJointCase& c,int index){return index==c.cap0||index==c.cap1;}

std::vector<int> path_tags(const Pattern& pattern,int side){
    const NineJointCase& c=nine_joint_cases[pattern.which];
    const auto& r=pattern.layout;
    int start=side?c.length:0,end=side?ring:c.length;
    std::vector<int> result;
    for(int i=start;i<end;i++){
        if(is_cap(c,i)){
            result.push_back(edge_roles+triple(r[i],r[(i+1)%ring],r[(i+2)%ring]));
            ++i;
        }else result.push_back(tag(r[i],r[(i+1)%ring]));
    }
    return result;
}

I span_bounds(const Pattern& pattern){
    const NineJointCase& c=nine_joint_cases[pattern.which];
    const I single=rat(737,1000),allowance=rat(7,4)*(14*M-pi),max_gap=2*asin_i(1/S);
    int g=static_cast<int>(std::find(pattern.layout.begin(),pattern.layout.end(),shared)-pattern.layout.begin());
    int before=(g+ring-1)%ring;
    auto side=[&](int start,int count){
        bool same=before>=start&&before<start+count&&g>=start&&g<start+count;
        I cap=count*single+allowance+int(same)*(rat(1131,1000)-2*single);
        for(int j:{c.cap0,c.cap1})if(j>=start&&j+1<start+count){
            bool touches=same&&(before==j||before==j+1||g==j||g==j+1);
            if(!touches)cap=cap+rat(1152,1000)-2*single;
        }
        return std::min(cap.hi,(count*max_gap).hi);
    };
    return I((2*pi-side(c.length,ring-c.length)).lo,side(0,c.length));
}

constexpr std::array<real,13> core_cap{{.375,.5,.625,.75,.875,1.,1.125,1.25,1.5,1.75,2.,2.5,3.}};
constexpr int caps=static_cast<int>(core_cap.size()),unit_bin=5;
constexpr int all_roles=edge_roles+cap_roles;
using Matrices=std::array<GapMatrix,all_roles>;

struct BridgeCell {int i,j,tag;I span,refund;};

std::vector<BridgeCell> bridges(const std::vector<I>& radii,const Pattern& pattern,I tilt){
    auto spans=grid(span_bounds(pattern),128);
    int n=static_cast<int>(radii.size());
    std::vector<BridgeCell> result;
    for(int i=0;i<n;i++)if(radii[i].lo<=3)for(int j=0;j<n;j++)if(radii[j].lo<=3)for(I span:spans){
        Trig half=gap_bridge_trig(span/2);
        I diff=sq(radii[i]-radii[j])/4,product=radii[i]*radii[j];
        I chord2=diff+product*sq(half.s);
        if(!intersect(chord2,I(0,4)))continue;
        I midpoint2=diff+product*sq(half.c);
        I radius=rt(midpoint2)+rt(nonneg(4-chord2));
        if(nine_joint_cases[pattern.which].length==5&&radius.hi<=1)continue;
        int tag=static_cast<int>(std::lower_bound(core_cap.begin(),core_cap.end(),std::min(3.,radius.hi))-core_cap.begin());
        I g=2*rt(nonneg(1-sq(nonneg(rt(chord2)-1))));
        result.push_back({i,j,tag,span,tilt*g*half.s});
    }
    return result;
}

std::array<Matrices,caps> matrices(const Cells<edge_roles>& seams,const Cells<cap_roles>& caps_cells,
                                  const std::array<bool,all_roles>& needed,I slope,I tilt){
    std::array<real,caps> limit;
    std::array<Matrices,caps> result;
    for(int k=0;k<caps;k++){
        limit[k]=sq(1+I(core_cap[k])).hi;
        for(int id=0;id<all_roles;id++)if(needed[id])result[k][id].assign(seams.size(),-inf);
    }
    auto add=[&](const auto& rows,int offset,int size){
        for(std::size_t i=0;i<rows.size();i++)for(const auto& cell:rows[i]){
            auto it=std::lower_bound(limit.begin(),limit.end(),cell.q_norm);
            if(it==limit.end())continue;
            auto& m=result[static_cast<std::size_t>(it-limit.begin())];
            I extra=slope*cell.d-tilt*cell.tilt;
            for(int id=0;id<size;id++)if(needed[offset+id]&&cell.scores[id]!=-inf)
                m[offset+id][i]=std::max(m[offset+id][i],up(cell.scores[id]+extra.hi));
        }
    };
    add(seams,0,edge_roles);
    add(caps_cells,edge_roles,cap_roles);
    for(int k=1;k<caps;k++)for(int id=0;id<all_roles;id++)if(needed[id])
        for(std::size_t i=0;i<seams.size();i++)result[k][id][i]=std::max(result[k][id][i],result[k-1][id][i]);
    return result;
}

template<class Eval>
real refine_bridge(I a,I b,I span,I tilt,bool outside,int coarse,Eval evaluate){
    Trig half=gap_bridge_trig(span/2);
    I product=a*b,diff=sq(a-b)/4;
    I x2=diff+product*sq(half.s);
    if(!intersect(x2,I(0,4)))return -inf;
    I x=rt(x2);
    if(x.lo<=0)throw std::domain_error("zero bridge chord");
    I mid2=diff+product*sq(half.c);
    I fm=product*half.c*half.s/x,em=(sq(b)-sq(a))/(4*x);
    I fx=(a+b)*half.s/(2*x),ex=(b-a)*half.c/(2*x);
    I limit=2*rt(nonneg(1-sq(nonneg(x-1))));
    std::vector<I> pending{I(0,limit.hi)};
    real worst=-inf;
    while(!pending.empty()){
        I g=pending.back();pending.pop_back();
        I h=rt(nonneg(1-sq(g)/4));
        I d2=sq(x-h);
        if(!intersect(d2,I(0,1)))continue;
        I rho=rt(nonneg(1-d2));
        I co(-1,1);
        if(h.lo>0&&!intersect(co,I(((x2+sq(h)-1)/(2*x*h)).lo,1)))continue;
        I sin_max=rt(nonneg(1-sq(nonneg(co))));
        // In the basis normal/tangential to AB, the bridge vector points
        // in the direction (cos(epsilon),sin(epsilon)).
        I spread=abs_i(em)*sin_max;
        I projection=fm*co+I(-spread.hi,spread.hi);
        I middle=mid2+sq(g)/4;
        I first=rt(nonneg(middle+g*projection))+rho;
        I second=rt(nonneg(middle-g*projection))+rho;
        if(outside&&first.hi<=1)continue;
        auto tag=[&](I radius,int upper){
            int k=static_cast<int>(std::lower_bound(core_cap.begin(),core_cap.end(),std::min(3.,radius.hi))-core_cap.begin());
            return std::min(k,upper);
        };
        I side=abs_i(ex)*sin_max;
        I horizontal=g*(fx*co+I(-side.hi,side.hi));
        I refund=tilt*half.s*I(std::min(horizontal.hi,g.hi));
        real bound=evaluate(tag(first,coarse),tag(second,std::min(unit_bin,coarse)),refund);
        if(bound<pi.lo||g.hi-g.lo<=1./128){
            worst=std::max(worst,bound);
            continue;
        }
        real midpoint=g.lo+(g.hi-g.lo)/2;
        pending.emplace_back(g.lo,midpoint);
        pending.emplace_back(midpoint,g.hi);
    }
    return worst;
}
bool check_case(const std::vector<I>& radii,const Cells<edge_roles>& seams,const Cells<cap_roles>& caps_cells,
                std::vector<Pattern>& patterns,I tilt,I area_price){
    int n=static_cast<int>(radii.size());
    std::array<bool,all_roles> needed{};
    for(const Pattern& pattern:patterns)if(!pattern.passed)for(int side=0;side<2;side++)
        for(int id:path_tags(pattern,side))needed[id]=true;

    struct Profile {
        I slope;
        std::vector<std::array<std::shared_ptr<const GapMatrix>,2>> paths;
    };
    std::vector<Profile> profiles;
    for(int s=55;s<=235;s+=10){
        Profile profile{rat(s,100),{}};
        auto tables=matrices(seams,caps_cells,needed,profile.slope,tilt);
        std::array<std::unordered_map<std::uint64_t,std::shared_ptr<const GapMatrix>>,caps> memo;
        auto join=[&](auto&& self,int cap,std::uint64_t key)->std::shared_ptr<const GapMatrix>{
            auto& cache=memo[cap];
            if(auto it=cache.find(key);it!=cache.end())return it->second;
            std::uint64_t prefix=key/all_roles;
            int tag=static_cast<int>(key%all_roles);
            GapMatrix m=prefix==1?tables[cap][tag]:gap_path_join(*self(self,cap,prefix),tables[cap][tag],n);
            return cache.emplace(key,std::make_shared<const GapMatrix>(std::move(m))).first->second;
        };
        profile.paths.resize(patterns.size()*caps);
        for(std::size_t p=0;p<patterns.size();p++)if(!patterns[p].passed){
            for(int side=0;side<2;side++){
                std::uint64_t key=1;
                for(int id:path_tags(patterns[p],side))key=all_roles*key+id;
                for(int k=0;k<(side?unit_bin+1:caps);k++)
                    profile.paths[p*caps+k][side]=join(join,k,key);
            }
        }
        profiles.push_back(std::move(profile));
    }
    bool passed=true;
    for(std::size_t p=0;p<patterns.size();p++){
        Pattern& pattern=patterns[p];
        if(pattern.passed)continue;
        real worst=-inf;
        std::uint64_t pending=0;
        BridgeCell critical{};
        for(const auto& box:bridges(radii,pattern,tilt)){
            int a=box.i*n+box.j,b=box.j*n+box.i;
            I budget=area_price*(area_needed+rat(7,100)*static_cast<int>(
                std::count(pattern.layout.begin(),pattern.layout.end(),multiple)));
            auto evaluate=[&](int first,int last,I refund){
                real u=inf,v=inf;
                for(const Profile& profile:profiles){
                    u=std::min(u,(I((*profile.paths[p*caps+first][0])[a])-profile.slope*box.span).hi);
                    v=std::min(v,(I((*profile.paths[p*caps+last][1])[b])-profile.slope*(2*pi-box.span)).hi);
                }
                return (I(u)+I(v)+refund-budget).hi;
            };
            real score=evaluate(box.tag,std::min(box.tag,unit_bin),box.refund);
            if(score>=pi.lo&&score<up(pi.hi+.12)){
                real refined=refine_bridge(radii[box.i],radii[box.j],box.span,tilt,
                                           nine_joint_cases[pattern.which].length==5,box.tag,evaluate);
                score=std::min(score,refined);
            }
            if(score>worst){worst=score;critical=box;}
            if(score>=pi.lo)++pending;
        }
        std::cout<<"nine case "<<pattern.which<<" layout ";
        for(Role r:pattern.layout)std::cout<<"rzdg"[r];
        std::cout<<" tilt "<<tilt.lo<<" score "<<std::setprecision(12)<<worst
                 <<" remaining "<<pending<<" worst "<<radii[critical.i].lo<<' '
                 <<radii[critical.j].lo<<' '<<critical.span.lo<<'\n'<<std::flush;
        pattern.passed=!pending;
        passed=passed&&pattern.passed;
    }
    return passed;
}

bool verify(int which=-1){
    if(which < -1 || which>=static_cast<int>(nine_joint_cases.size()))
        throw std::logic_error("invalid nine-edge case");
    std::vector<std::vector<Pattern>> batches;
    std::array<bool,edge_roles> need_edge{};
    std::array<bool,cap_roles> need_cap{};
    const int begin=which<0?0:which;
    const int end=which<0?static_cast<int>(nine_joint_cases.size()):which+1;
    for(int id=begin;id<end;id++){
        batches.push_back(layouts(id));
        for(const auto& p:batches.back())for(int i=0;i<ring;i++){
            int edge=tag(p.layout[i],p.layout[(i+1)%ring]);
            need_edge[edge]=need_edge[reverse_edge(edge)]=true;
            if(is_cap(nine_joint_cases[id],i)){
                int cap=triple(p.layout[i],p.layout[(i+1)%ring],p.layout[(i+2)%ring]);
                need_cap[cap]=need_cap[reverse_cap(cap)]=true;
            }
        }
        std::cout<<"nine case "<<id<<" patterns "<<batches.back().size()<<'\n'<<std::flush;
    }
    const I area_price=rat(1,5);
    const int workers=static_cast<int>(std::clamp(std::thread::hardware_concurrency(),1u,12u));
    auto radii=grid(I((R-3).lo,min_outer.hi),32);
    auto seams=make_seams(radii,need_edge,I(1),rat(2,5),area_price,128,128,workers);
    auto caps_cells=make_caps(radii,seams,need_edge,need_cap);
    bool complete=true;
    for(std::size_t i=0;i<batches.size();i++){
        bool passed=false;
        for(int v:{360,420,480,540,600,660,720,780,300,240,180}){
            if(check_case(radii,seams,caps_cells,batches[i],rat(v,1000),area_price)){passed=true;break;}
        }
        std::cout<<"nine result "<<begin+static_cast<int>(i)<<' '<<passed<<'\n'<<std::flush;
        complete=complete&&passed;
    }
    return complete;
}

} // namespace nine_joint

int main(int argc,char**argv){
    if(std::fegetround()!=FE_TONEAREST)return 3;
    for(real x:{-1.,-0.,0.,1.})
        if(up(x)!=std::nextafter(x,inf)||down(x)!=std::nextafter(x,-inf))return 3;
    try {
        if(argc==2||(argc==3&&(std::string(argv[1])=="octagon-fan-four-bridge-primary"
                             ||std::string(argv[1])=="octagon-fan-four-bridge-secondary"
                             ||std::string(argv[1])=="nine-joint-reduce"
                             ||std::string(argv[1])=="nine-joint"
                             ||std::string(argv[1]).find("nine-one-cap-")==0))
            ||((argc==3||argc==4)&&std::string(argv[1]).find("nine-shared-cap-")==0)){
            std::string mode=argv[1];
            if(mode=="normal")return verify(Case::normal)?0:1;
            if(mode=="normal-double")return verify(Case::normal_double)?0:1;
            if(mode=="cap-one")return verify(Case::cap_one)?0:1;
            if(mode=="cap-two")return verify(Case::cap_two)?0:1;
            if(mode=="mixed-normal")return verify_mixed(false,true)?0:1;
            if(mode=="mixed-cap")return verify_mixed(true,true)?0:1;
            if(mode=="mixed-normal-inactive")return verify_mixed(false,false)?0:1;
            if(mode=="mixed-cap-inactive")return verify_mixed(true,false)?0:1;
            if(mode=="mixed-cap-other-inactive")return verify_mixed(true,true,true)?0:1;
            if(mode=="mixed-cap-both-inactive")return verify_mixed(true,false,true)?0:1;
            if(mode=="ordinary-inactive")return verify_cap_partition(1,1)?0:1;
            if(mode=="priced-normal-inactive")return verify_cap_partition(1,1,false,1)?0:1;
            if(mode=="cap-two-one-inactive")return verify_cap_partition(2,1,false,2)?0:1;
            if(mode=="cap-two-two-inactive")return verify_cap_partition(2,2,false,2)?0:1;
            if(mode=="triangle-cap")return verify_cap_partition(2,0)?0:1;
            if(mode=="triangle-cap-one-inactive")return verify_cap_partition(2,1)?0:1;
            if(mode=="triangle-cap-two-inactive")return verify_cap_partition(2,2)?0:1;
            if(mode=="quadrilateral-cap")return verify_cap_partition(3,0)?0:1;
            if(mode=="quadrilateral-cap-one-inactive")return verify_cap_partition(3,1)?0:1;
            if(mode=="quadrilateral-cap-two-inactive")return verify_cap_partition(3,2)?0:1;
            if(mode=="long-cap-root")return verify_cap_partition(4,0)?0:1;
            if(mode=="quadrilateral-extra")return verify_cap_partition(3,0,true)
                &&verify_cap_partition(3,1,true)&&verify_cap_partition(3,2,true)?0:1;
            if(mode=="reverse-cap")return verify_reverse_cap(0)&&verify_reverse_cap(1)&&verify_reverse_cap(2)?0:1;
            if(mode=="shared-triangle-ordinary" || mode=="shared-triangle-symmetric"){
                for(bool active:{true,false})for(int inactive:{0,1})
                    if(!verify_shared_triangle(mode=="shared-triangle-symmetric",active,inactive))return 1;
                return 0;
            }
            if(mode=="shared-quad-ordinary" || mode=="shared-quad-symmetric" || mode=="shared-quad-inside"){
                RootShared shared=mode=="shared-quad-ordinary"?RootShared::endpoint:
                    mode=="shared-quad-symmetric"?RootShared::symmetric:RootShared::inside;
                for(bool active:{true,false}){
                    for(int inactive:{0,1,2})if(!verify_shared_quad(shared,active,inactive))return 1;
                    if(shared==RootShared::inside)break;
                }
                return 0;
            }
            if(mode=="annular-pair")return verify_annular_pair()?0:1;
            if(mode=="inactive-without-area")return verify_inactive_without_area(0)&&verify_inactive_without_area(1)?0:1;
            if(mode=="joined-normal")return verify_spaced_normal(2)&&verify_spaced_normal(3)?0:1;
            if(mode=="joined-triangle")return verify_spaced_triangle(2)&&verify_spaced_triangle(5)?0:1;
            if(mode=="joined-quad")return verify_spaced_quad(false)&&verify_spaced_quad(true)?0:1;
            if(mode=="ten-ring-normal")return verify_ten_ring(1)?0:1;
            if(mode=="ten-ring-triangle")return verify_ten_ring(2)?0:1;
            if(mode=="outer-angle-normal")return verify_outer_angle_block(1,0)&&verify_outer_angle_block(1,1)
                &&verify_outer_angle_block(1,2)?0:1;
            if(mode=="outer-angle-triangle")return verify_outer_angle_block(2,0)&&verify_outer_angle_block(2,1)
                &&verify_outer_angle_block(2,2)?0:1;
            if(mode=="outer-angle-triangle-none")return verify_outer_angle_block(2,0)?0:1;
            if(mode=="outer-angle-triangle-one")return verify_outer_angle_block(2,1)?0:1;
            if(mode=="outer-angle-triangle-two")return verify_outer_angle_block(2,2)?0:1;
            using PS=PricedSeam;
            if(mode=="outer-angle-shared-normal")return verify_priced_variant(1,PS::half,PS::full,0,0,4960)
                &&verify_priced_variant(1,PS::omit,PS::full,0,0,3150,true)?0:1;
            if(mode=="outer-angle-inactive-normal")return verify_priced_variant(1,PS::omit,PS::full,0,0,5280)
                &&verify_priced_variant(1,PS::inactive_no_area,PS::full,0,0,4480)?0:1;
            if(mode=="outer-angle-inactive-triangle")return verify_priced_inactive_triangles(false)?0:1;
            if(mode=="outer-angle-inactive-reverse")return verify_priced_inactive_triangles(true)?0:1;
            if(mode=="outer-angle-inactive-half-triangle")return verify_priced_inactive_triangles(false,true)?0:1;
            if(mode=="outer-angle-inactive-half-reverse")return verify_priced_inactive_triangles(true,true)?0:1;
            if(mode=="outer-angle-inactive-pair-span")return verify_narrow_inactive_pair()?0:1;
            if(mode=="outer-angle-inactive-phase-normal")return verify_priced_variant(1,PS::inactive_phase,PS::full,0,0,3570)?0:1;
            if(mode=="outer-angle-inactive-phase-triangle")return verify_priced_variant(2,PS::inactive_phase,PS::full,0,0,10900)
                &&verify_priced_variant(2,PS::inactive_phase,PS::half,0,0,9250)?0:1;
            if(mode=="outer-angle-inactive-phase-quad-full")return verify_inactive_phase_quad(0)?0:1;
            if(mode=="outer-angle-inactive-phase-quad-half")return verify_inactive_phase_quad(1)?0:1;
            if(mode=="outer-angle-inactive-phase-quad-omit")return verify_inactive_phase_quad(2)?0:1;
            if(mode=="outer-angle-twin-normal")return verify_twin_short_caps(false)?0:1;
            if(mode=="outer-angle-twin-triangle")return verify_twin_short_caps(true)?0:1;
            if(mode=="outer-angle-shared-triangle")return verify_priced_variant(2,PS::half,PS::full,0,0,12230)
                &&verify_priced_variant(2,PS::half,PS::half,0,0,10550)?0:1;
            if(mode=="outer-angle-reverse-triangle")return verify_priced_variant(2,PS::full,PS::full,1,0,11450)
                &&verify_priced_variant(2,PS::half,PS::full,1,0,10940)&&verify_priced_variant(2,PS::half,PS::full,2,0,10940)
                &&verify_priced_variant(2,PS::half,PS::half,1,0,8970)?0:1;
            if(mode=="outer-angle-one-cross")return verify_priced_variant(1,PS::half,PS::full,0,1,5060)
                &&verify_priced_variant(2,PS::half,PS::full,0,2,11925)?0:1;
            if(mode=="outer-angle-quad")return verify_rim_priced_quad<0,true>(0,0,1999)
                &&verify_rim_priced_quad<0,true>(0,1,2098)&&verify_rim_priced_quad<0,true>(1,1,2202)?0:1;
            if(mode=="outer-angle-neutral-quad")return verify_rim_priced_quad<0,true>(0,2,2067)
                &&verify_rim_priced_quad<0,true>(1,2,2173)&&verify_rim_priced_quad<0,true>(2,2,2151)?0:1;
            if(mode=="outer-angle-chord-normal")return verify_priced_variant(1,PS::full,PS::full,0,0,9130,false,0,chord_ring)
                &&verify_priced_variant(1,PS::half,PS::full,0,0,7104,false,0,chord_ring)
                &&verify_priced_variant(1,PS::omit,PS::full,0,0,5198,true,0,chord_ring)?0:1;
            if(mode=="outer-angle-chord-triangle")return verify_priced_variant(2,PS::full,PS::full,0,0,16880,false,0,chord_ring)
                &&verify_priced_variant(2,PS::half,PS::full,0,0,15324,false,0,chord_ring)
                &&verify_priced_variant(2,PS::half,PS::half,0,0,13508,false,0,chord_ring)?0:1;
            if(mode=="outer-angle-chord-reverse")return verify_priced_variant(2,PS::full,PS::full,1,0,13600,false,0,chord_ring)
                &&verify_priced_variant(2,PS::half,PS::full,1,0,13484,false,0,chord_ring)
                &&verify_priced_variant(2,PS::half,PS::full,2,0,13484,false,0,chord_ring)
                &&verify_priced_variant(2,PS::half,PS::half,1,0,11528,false,0,chord_ring)?0:1;
            if(mode=="outer-angle-chord-quad")return verify_rim_priced_quad<0,true>(0,0,2345,0,chord_ring)
                &&verify_rim_priced_quad<0,true>(0,1,2437,0,chord_ring)
                &&verify_rim_priced_quad<0,true>(1,1,2535,0,chord_ring)
                &&verify_rim_priced_quad<0,true>(0,2,2424,0,chord_ring)
                &&verify_rim_priced_quad<0,true>(1,2,2519,0,chord_ring)
                &&verify_rim_priced_quad<0,true>(2,2,2508,0,chord_ring)?0:1;
            if(mode=="outer-angle-seven-chord")return verify_priced_variant(1,PS::full,PS::full,0,0,8600,false,0,seven_chord_ring)
                &&verify_priced_variant(1,PS::half,PS::full,0,1,6674,false,0,seven_chord_ring,rat(13,10))
                &&verify_rim_priced_quad<0,true>(1,1,2321,rat(13,10),seven_chord_ring)?0:1;
            if(mode=="outer-angle-chord-inactive-normal")return verify_chord_inactive_short(1)?0:1;
            if(mode=="outer-angle-chord-inactive-triangle")return verify_chord_inactive_short(2)?0:1;
            if(mode=="outer-angle-chord-inactive-quad")return verify_chord_inactive_root(0,1555)
                &&verify_chord_inactive_root(1,1732)&&verify_chord_inactive_root(1,2161,rat(5,2))?0:1;
            if(mode=="octagon-shared-span-joined")return verify_octagon_shared_span(false)?0:1;
            if(mode=="octagon-shared-span-flank")return verify_octagon_shared_span(true)?0:1;
            if(mode=="nine-two-pairs-zero-gap")return verify_nine_two_pairs(0)?0:1;
            if(mode=="nine-two-pairs-short-flanks")return verify_nine_two_pairs(1)?0:1;
            if(mode=="nine-two-pairs-middle-single")return verify_nine_two_pairs(2)?0:1;
            if(mode=="cap-span-prices")return verify_cap_span_prices()?0:1;
            if(mode=="nine-cap-with-pair")return verify_nine_cap_with_pair()?0:1;
            if(mode=="octagon-joined-cap")return verify_octagon_joined_cap()?0:1;
            if(mode=="nine-distinct-two-caps")return verify_nine_distinct_two_caps()?0:1;
            if(mode=="nine-distinct-two-caps-zero-ends")return verify_nine_distinct_two_caps_zero_ends()?0:1;
            if(mode=="octagon-one-cap")return verify_octagon_one_cap()?0:1;
            if(mode=="octagon-fan-span-prices")return verify_fan_span_prices()?0:1;
            if(mode=="octagon-long-runs")return verify_octagon_long_runs()?0:1;
            if(mode=="octagon-double-gap-three")return verify_radial_gap_patterns(3,RimPathCase::double_fillers,256,512)?0:1;
            if(mode=="octagon-double-gap-four")return verify_radial_gap_patterns(4,RimPathCase::double_fillers,128,512)?0:1;
            if(mode=="octagon-ear-gap-three")return verify_radial_gap_patterns(3,RimPathCase::ear,256,1024,-1,false)?0:1;
            if(mode=="octagon-ear-pattern-three")return verify_radial_gap_patterns(3,RimPathCase::ear_reduction,256,1024,-1,false)?0:1;
            if(mode=="octagon-ear-gap-four")return verify_radial_gap_patterns(4,RimPathCase::ear,256,1024,-1,false)?0:1;
            if(mode=="octagon-joint-three")return octagon_joint::verify(3)?0:1;
            if(mode=="octagon-joint-four")return octagon_joint::verify(4)?0:1;
            if(mode=="octagon-regular-gap-three")return verify_radial_gap_patterns(3,RimPathCase::regular,128,512)?0:1;
            if(mode=="octagon-regular-gap-four")return verify_radial_gap_patterns(4,RimPathCase::regular,128,512)?0:1;
            if(mode=="nine-four-empty-three")return verify_radial_gap_patterns(3,RimPathCase::unshared_nine,256,1024)?0:1;
            if(mode=="nine-four-empty-four")return verify_radial_gap_patterns(4,RimPathCase::unshared_nine,256,1024)?0:1;
            if(mode=="nine-four-empty-five")return verify_radial_gap_patterns(5,RimPathCase::unshared_nine,128,512)?0:1;
            if(mode=="nine-shared-ordinary-three")return verify_radial_gap_patterns(3,RimPathCase::shared_nine,256,512)?0:1;
            if(mode=="nine-shared-ordinary-four")return verify_radial_gap_patterns(4,RimPathCase::shared_nine,256,512)?0:1;
            if(mode=="nine-shared-ordinary-five")return verify_radial_gap_patterns(5,RimPathCase::shared_nine,256,512)?0:1;
            if(mode=="nine-shared-ordinary-four-bridge")return verify_radial_gap_patterns(4,RimPathCase::shared_bridge_four,256,512)?0:1;
            if(mode=="nine-joint-reduce"&&argc==3)return verify_nine_joint_reduction(std::stoi(argv[2]))?0:1;
            if(mode=="nine-joint")return nine_joint::verify(argc==3?std::stoi(argv[2]):-1)?0:1;
            if(mode=="nine-one-cap-three"||mode=="nine-one-cap-four"||mode=="nine-one-cap-five"){
                if(argc!=3)return 2;
                int length=mode=="nine-one-cap-three"?3:mode=="nine-one-cap-four"?4:5;
                int start=std::stoi(argv[2]);
                if(start<0||start>=8||start==length-1)return 2;
                return verify_radial_gap_patterns(length,RimPathCase::cap_unshared_nine,128,512,start)?0:1;
            }
            if(mode=="nine-shared-cap-three"||mode=="nine-shared-cap-four"||mode=="nine-shared-cap-five"){
                if(argc!=3&&argc!=4)return 2;
                int length=mode=="nine-shared-cap-three"?3:mode=="nine-shared-cap-four"?4:5;
                int start=std::stoi(argv[2]),other=argc==4?std::stoi(argv[3]):-1;
                auto legal=[&](int cap){return cap>=0&&cap<8&&cap!=length-1;};
                if(!legal(start)||(argc==4&&(!legal(other)||std::abs(other-start)<2)))return 2;
                return verify_radial_gap_patterns(length,RimPathCase::cap_shared_nine,128,512,start,true,other)?0:1;
            }
            if(mode=="octagon-inactive-radial-secondary")return verify_radial_gap_patterns(3,RimPathCase::inactive_seam,256,1024,0)?0:1;
            if(mode=="octagon-inactive-radial-primary")return verify_radial_gap_patterns(3,RimPathCase::inactive_seam,256,1024,3)?0:1;
            if(mode=="octagon-inactive-radial-center")return verify_radial_gap_patterns(3,RimPathCase::inactive_seam,256,1024,5)?0:1;
            if(mode=="high-octagon-fan")return verify_high_octagon(rat(1701,400),rat(715,1000))?0:1;
            if(mode=="higher-octagon-fan")return verify_high_octagon(rat(8493,2000),rat(717,1000))?0:1;
            if(mode=="tighter-octagon-fan")return verify_high_octagon(rat(1697,400),rat(718,1000))?0:1;
            if(mode=="high-fourteen-mark-pair"){
                FanHighRadius target(rat(1697,400),rat(718,1000));
                return verify_mark_pair(&target)?0:1;
            }
            if(mode=="octagon-fan-inner-inactive-primary")return verify_octagon_fan_interior_inactive(true)?0:1;
            if(mode=="octagon-fan-inner-inactive-secondary")return verify_octagon_fan_interior_inactive(false)?0:1;
            if(mode=="octagon-fan-three-inner-secondary")return verify_octagon_fan(mode.c_str(),3,1,
                rat(34,100),rat(35,100),rat(8,100),true)?0:1;
            if(mode=="octagon-fan-three-inner-primary")return verify_octagon_fan(mode.c_str(),3,4,
                rat(345,1000),rat(34,100),rat(124,1000),true,rat(149,1000),true)?0:1;
            if(mode=="octagon-fan-three-center-primary")return verify_octagon_fan(mode.c_str(),3,5,
                rat(345,1000),rat(34,100),rat(124,1000),true,rat(149,1000),true,I(0,7),true)?0:1;
            if(mode=="octagon-fan-three-bridge-secondary")return verify_octagon_fan(mode.c_str(),3,0,
                rat(354,1000),rat(347,1000),rat(117,1000),true,rat(116,1000),true,I(0,7),true)?0:1;
            if(mode=="octagon-fan-three-bridge-primary")return verify_octagon_fan(mode.c_str(),3,3,
                rat(362,1000),rat(349,1000),rat(125,1000),true,rat(144,1000),true,I(0,7),true)?0:1;
            if(mode=="octagon-fan-three-center-compressed")return verify_octagon_fan(mode.c_str(),3,5,
                rat(345,1000),rat(34,100),rat(124,1000),true,rat(149,1000),true,I(0,7),false,true)?0:1;
            if(mode=="octagon-fan-three-secondary-compressed")return verify_octagon_fan(mode.c_str(),3,0,
                rat(354,1000),rat(347,1000),rat(117,1000),true,rat(116,1000),true,I(0,7),false,true)?0:1;
            if(mode=="octagon-fan-three-primary-compressed")return verify_octagon_fan(mode.c_str(),3,3,
                rat(362,1000),rat(349,1000),rat(125,1000),true,rat(144,1000),true,I(0,7),false,true)?0:1;
            if(mode=="octagon-fan-four-primary-compressed")return verify_octagon_fan_bridge_four(true,2,true)?0:1;
            if(mode=="octagon-fan-four-bridge-secondary"||mode=="octagon-fan-four-bridge-primary")
                return verify_octagon_fan_bridge_four(mode=="octagon-fan-four-bridge-primary",argc>2?std::stoi(argv[2]):-1)?0:1;
            if(mode=="outer-angle-quad-radius")return verify_rim_priced_quad<0,true>(0,0,1944,rat(4,5))
                &&verify_rim_priced_quad<0,true>(1,0,2033,rat(4,5))?0:1;
            if(mode=="outer-angle-strict-quad")return verify_strict_quad(-1,1,1,rat(207,10),true)
                &&verify_strict_quad(0,1,1,rat(207,10),true)&&verify_strict_quad(1,1,1,rat(207,10),true)
                &&verify_strict_quad(2,1,1,rat(207,10),true)?0:1;
            if(mode=="outer-angle-typed-quad")return verify_typed_quad()?0:1;
            if(mode=="outer-angle-typed-quad-radius")return verify_typed_quad(true)
                &&verify_rim_priced_quad<0,true>(1,1,2128,rat(4,5))?0:1;
            if(mode=="ten-ring-weighted-transfer-quad")return verify_rim_priced_quad<0,true>(1,1,2155,rat(2,5))?0:1;
            if(mode=="ten-ring-weighted-transfer-triangle")return verify_priced_variant(2,PS::half,PS::full,0,1,12280,
                false,0,priced_ring,rat(-2,5))&&verify_priced_variant(2,PS::half,PS::half,0,1,10650,
                false,0,priced_ring,rat(-2,5))?0:1;
            if(mode=="ten-ring-reverse")return verify_reverse_cap(0,ten_ring_prices,rat(1255,100))?0:1;
            if(mode=="ten-ring-quad")return verify_ten_ring(3)?0:1;
            if(mode=="ten-ring-omitted-normal")return verify_ten_ring(1,1)?0:1;
            if(mode=="ten-ring-omitted-triangle")return verify_ten_ring(2,1)&&verify_ten_ring(2,2)?0:1;
            if(mode=="ten-ring-omitted-quad")return verify_ten_ring(3,1)&&verify_ten_ring(3,2)&&verify_ten_ring(3,3)?0:1;
            if(mode=="ten-ring-extra-quad")return verify_ten_ring(3,0,true)&&verify_ten_ring(3,1,true)&&verify_ten_ring(3,2,true)?0:1;
            if(mode=="double-mixed-triangle")return verify_double_mixed_triangle()?0:1;
            if(mode=="ten-ring-shared-normal")return verify_ten_ring_shared_normal()&&verify_ten_ring_shared_middle()?0:1;
            if(mode=="ten-ring-shared-triangle")return verify_ten_ring_shared_triangle(false)
                &&verify_ten_ring_shared_triangle(true)?0:1;
            if(mode=="ten-ring-shared-reverse")return verify_ten_ring_shared_triangle(false,1)
                &&verify_ten_ring_shared_triangle(false,2)&&verify_ten_ring_shared_triangle(true,1)?0:1;
            if(mode=="ten-ring-free-quad")return verify_ten_ring_free_quad()?0:1;
            if(mode=="ten-ring-crossed-quad")return verify_ten_ring_crossed_quad(false)&&verify_ten_ring_crossed_quad(true)?0:1;
            if(mode=="ten-ring-side-quad")return verify_ten_ring_side_quad(0,1,2223)&&verify_ten_ring_side_quad(1,1,2304)
                &&verify_ten_ring_side_quad(0,2,2202)&&verify_ten_ring_side_quad(1,2,2282)
                &&verify_ten_ring_side_quad(2,2,2260)?0:1;
            if(mode=="rim-priced-quad")return verify_rim_priced_quad(0,0,2032)&&verify_rim_priced_quad(0,1,2092)
                &&verify_rim_priced_quad(0,2,2087)&&verify_rim_priced_quad(1,1,2155)
                &&verify_rim_priced_quad(1,2,2157)&&verify_rim_priced_quad(2,2,2169)?0:1;
            if(mode=="tight-unshared-quad")return verify_rim_priced_quad<0>(0,0,2103)?0:1;
            if(mode=="reversed-quad")return verify_reversed_quad(0)&&verify_reversed_quad(1)&&verify_reversed_quad(2)?0:1;
            if(mode=="strict-quad-forward")return verify_strict_quad(-1,1,1,rat(2251,100))?0:1;
            if(mode=="strict-quad-reverse")return verify_strict_quad(0,1,1,rat(2251,100))
                &&verify_strict_quad(1,1,1,rat(2251,100))&&verify_strict_quad(2,1,1,rat(2251,100))?0:1;
            if(mode=="single-active-quad-end")return verify_single_active_quad_end()?0:1;
            if(mode=="fat-cap-two")return verify_fat_cap(FatShared::none)&&verify_fat_cap(FatShared::endpoint)
                &&verify_fat_cap(FatShared::inside)?0:1;
            if(mode=="fat-cap-omitted")return verify_fat_cap(FatShared::none,1)&&verify_fat_cap(FatShared::none,3)?0:1;
            if(mode=="fat-cap-double-end")return verify_fat_cap(FatShared::both_ends)?0:1;
            if(mode=="wide-core-normal")return verify_wide_regular(1,0)&&verify_wide_regular(1,1)?0:1;
            if(mode=="wide-core-triangle")return verify_wide_regular(2,0)&&verify_wide_regular(2,1)
                &&verify_wide_regular(2,2)?0:1;
            if(mode=="wide-core-quad")return verify_wide_regular(3,0)&&verify_wide_regular(3,1)
                &&verify_wide_regular(3,2)?0:1;
            if(mode=="wide-core-fat")return verify_fat_cap(FatShared::none,0,true)&&verify_fat_cap(FatShared::endpoint,0,true)
                &&verify_fat_cap(FatShared::inside,0,true)&&verify_fat_cap(FatShared::both_ends,0,true)?0:1;
            if(mode=="wide-three-normal")return verify_wide_regular(1,0,true)&&verify_wide_regular(1,1,true)?0:1;
            if(mode=="wide-three-triangle")return verify_wide_regular(2,0,true)&&verify_wide_regular(2,1,true)
                &&verify_wide_regular(2,2,true)?0:1;
            if(mode=="wide-three-quad")return verify_wide_regular(3,0,true)&&verify_wide_regular(3,1,true)
                &&verify_wide_regular(3,2,true)?0:1;
            if(mode=="wide-three-fat")return verify_wide_fat_three(0)&&verify_wide_fat_three(1)&&verify_wide_fat_three(3)?0:1;
            if(mode=="wide-three-distinct-regular")return verify_wide_regular(1,0,true,676)
                &&verify_wide_regular(2,0,true,1351)?0:1;
            if(mode=="wide-three-distinct-fat")return verify_wide_fat_three(0,true)?0:1;
            if(mode=="wide-three-omitted-regular")return verify_wide_regular(1,0,true,510,1)
                &&verify_wide_regular(2,0,true,1230,1)&&verify_wide_regular(3,0,true,1950,1)?0:1;
            if(mode=="wide-three-omitted-fat")return verify_wide_fat_three(0,true,1)
                &&verify_wide_fat_three(0,true,2)?0:1;
            if(mode=="wide-three-internal-pair-fat")return verify_wide_fat_three(0,false,0,FatThreePair::active)
                &&verify_wide_fat_three(0,false,0,FatThreePair::inactive)
                &&verify_wide_fat_three(0,false,0,FatThreePair::active_third_inactive)?0:1;
            if(mode=="wide-three-inactive-pair-normal")return verify_wide_inactive_pair_normal()?0:1;
            if(mode=="degree-four-fat-three")return verify_degree_four_fat_three(0)
                &&verify_degree_four_fat_three(1)&&verify_degree_four_fat_three(2)?0:1;
            if(mode=="degree-four-two-caps-internal-pair")return verify_two_cap_fat_pair(false)?0:1;
            if(mode=="degree-four-two-caps-crossed-normal")return verify_two_cap_crossed_normal(false)
                &&verify_two_cap_crossed_normal(true)?0:1;
            if(mode=="degree-four-two-caps-crossed-pair")return verify_two_cap_fat_pair(true)?0:1;
            if(mode=="nine-three-fan-normal")return verify_three_fan_normal(false)&&verify_three_fan_normal(true)?0:1;
            if(mode=="nine-three-fan-block")return verify_three_fan_block()?0:1;
            if(mode=="three-fan-wide-normal")return verify_three_fan_normal(false,true)&&verify_three_fan_normal(true,true)?0:1;
            if(mode=="three-fan-wide-block")return verify_three_fan_block(ThreeFanBlock::wide)?0:1;
            if(mode=="three-fan-wide-cap-end")return verify_three_fan_block(ThreeFanBlock::cap_endpoint)?0:1;
            if(mode=="three-fan-main-cap")return verify_three_fan_cap()?0:1;
            if(mode=="three-fan-inactive-normal")return verify_three_fan_normal(false,true,true)
                &&verify_three_fan_normal(true,true,true)?0:1;
            if(mode=="three-fan-inactive-end")return verify_three_fan_block(ThreeFanBlock::inactive_endpoint)?0:1;
            if(mode=="three-fan-internal-shared")return verify_three_fan_block(ThreeFanBlock::internal_shared)?0:1;
            if(mode=="three-fan-crossed-normal")return verify_three_fan_cross_normal()?0:1;
            if(mode=="three-fan-crossed-block")return verify_three_fan_block(ThreeFanBlock::crossed_endpoint)?0:1;
            if(mode=="three-fan-primary-pair")return verify_three_fan_primary_pair()?0:1;
            if(mode=="degree-four-fat-four-first"||mode=="degree-four-fat-four-second"){
                bool second=mode=="degree-four-fat-four-second";
                for(int shares=0;shares<4;shares++)if(!verify_degree_four_fat_four(shares,second))return 1;
                return 0;
            }
            if(mode=="degree-four-fat-five-first"||mode=="degree-four-fat-five-second"){
                bool second=mode=="degree-four-fat-five-second";
                for(int shortcut=1;shortcut<=3;shortcut++)for(int shares=0;shares<4;shares++)
                    if(!verify_degree_four_fat_four(shares,second,shortcut))return 1;
                return 0;
            }
            if(mode=="mark-pair-fourteen")return verify_mark_pair()?0:1;
            if(mode=="inactive-mark-loss")return verify_inactive_mark_loss()?0:1;
            if(mode=="inactive-weighted-mark-loss")return verify_inactive_mark_loss(1)&&verify_inactive_mark_loss(2)?0:1;
            if(mode=="inactive-joint-star")return verify_inactive_joint_star()?0:1;
            if(mode=="mark-triple-fourteen")return verify_mark_triple()?0:1;
        }
        if(argc!=1)return 3;
        return verify(Case::normal)&&verify(Case::normal_double)
            &&verify(Case::cap_one)&&verify(Case::cap_two)?0:1;
    }catch(const std::exception& e){std::cerr<<e.what()<<'\n';return 2;}
}

