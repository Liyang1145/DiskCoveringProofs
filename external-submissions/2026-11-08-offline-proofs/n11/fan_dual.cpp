// Adaptive interval bounds for the remaining four-plus-five fan.
#include "fan_interval.hpp"
#include <atomic>
#include <condition_variable>
#include <cstdio>
#include <fstream>
#include <mutex>
#include <string_view>
#include <thread>
#include <vector>

namespace fan {
using Inner=std::array<I,3>;  // P=(a,v), Q=(-b,v)
using Site=std::array<I,2>;   // radius, unwrapped polar angle
using Vec=std::array<I,2>;
using Gradient=std::array<I,5>;

I R,R2,FOUR_R2,H0,A0,B0,MAX_OUTER_ARC,RHO_OPTIMUM;
std::array<Vec,9> anchor_centers;
const Int INF=1000*S;

struct Window { I q; std::array<Site,6> long_fan; };

std::vector<Window> read_windows(const char* name) {
    std::ifstream input(name);
    assert(input);
    std::vector<Window> ans;
    Int p0,p1;
    while (input>>p0>>p1) {
        Window w;
        w.q={rat(p0,1000).lo,rat(p1,1000).hi};
        for (auto& site:w.long_fan) {
            Int tl,th,rl,rh;
            assert(input>>tl>>th>>rl>>rh);
            site={I{rl*(S>>40),rh*(S>>40)},I{tl*(S>>40),th*(S>>40)}};
        }
        ans.push_back(w);
    }
    assert(input.eof() && !ans.empty());
    return ans;
}

struct Coefficients {
    std::array<I,9> base, inner;
    std::array<std::array<I,3>,9> slope;
    std::array<I,2> switch_weight;

    explicit Coefficients(const char* file) {
        std::ifstream data(file);
        auto read=[&] {
            I z;
            assert(data>>z.lo>>z.hi);
            assert(z.lo<=z.hi);
            return z;
        };
        R=read(); A0=read(); B0=read();
        I v=read();
        assert(v.lo==0 && v.hi==0);
        R2=sq(R); FOUR_R2=rat(4)*R2; H0=point((ONE-TWO*R).lo);
        RHO_OPTIMUM=root(ONE-R2);
        MAX_OUTER_ARC=acos(RHO_OPTIMUM);
        for (auto& z:anchor_centers) { z[0]=read(); z[1]=read(); }
        for (auto& z:base) z=read();
        inner.fill(ZERO);
        for (int i:{0,1,2,4,6,7,8}) inner[i]=read();
        for (auto& z:switch_weight) z=read();
        for (I z:base) assert(z.lo>0);
        for (I z:inner) assert(z.lo>=0);
        for (I z:switch_weight) assert(z.lo>0);
        Int d[9][3] = {
            {-2670,6500,-546},{-2300,6696,-3671},{601,-532,-4912},
            {537,-2498,-1258},{530,-3570,0},{537,-2498,1258},
            {601,-532,4912},{-2300,6696,3671},{-2670,6500,546}
        };
        for (int i=0;i<9;++i) {
            for (int j=0;j<3;++j) slope[i][j]=rat(d[i][j],100000);
        }
    }

    I outer(int i,const Inner& y) const {
        return base[i]+slope[i][0]*(y[0]-A0)+slope[i][1]*(y[1]-B0)+slope[i][2]*y[2];
    }
};

bool is_p_edge(int edge) { return edge==0 || edge==1 || edge>=7; }

struct Geometry {
    Inner y;
    I offset, separation, height;
    bool height_smooth;
};

Geometry geometry(const Inner& y) {
    I d=(y[0]+y[1])/TWO;
    I h2=R2-sq(d);
    return {y,(y[0]-y[1])/TWO,d,root(nonnegative(h2)),h2.lo>0};
}

bool initial_sites(const Inner& y,const std::vector<Window>& windows,std::array<Site,9>& ans) {
    I q2=sq(y[1])+sq(y[2]), p2=sq(y[0])+sq(y[2]);
    if (p2.lo>sq(rat(62,100)).hi) return false;
    I d=(y[0]+y[1])/TWO;
    if (d.hi<rat(68,1000).lo || d.lo>R.hi) return false;
    // Rational sample points on the central circle inaccessible to exterior disks.
    for (int t=-16;t<=16;++t) {
        I x=H0*rat(256-t*t,256+t*t), v=H0*rat(32*t,256+t*t);
        for (int sign:{-1,1}) {
            I xx=sign==1?x:-x;
            if ((sq(xx-y[0])+sq(v-y[2])).lo>R2.hi &&
                (sq(xx+y[1])+sq(v-y[2])).lo>R2.hi) return false;
        }
    }
    std::array<Site,9> rel{};
    bool possible=false;
    for (const auto& w:windows) {
        I q2w=sq(w.q);
        if (q2w.lo>q2.hi || q2w.hi<q2.lo) continue;
        for (int i=0;i<6;++i) {
            for (int j=0;j<2;++j)
                rel[i][j]=possible?hull(rel[i][j],w.long_fan[i][j]):w.long_fan[i][j];
        }
        possible=true;
    }
    if (!possible) return false;
    I angle=angle_upper_half(-y[1],y[2]);
    for (int i=6;i<9;++i) {
        rel[i][0]={(ONE-R).lo,S};
        rel[i][1]={
            (rel[0][1]+TWO*PI-rat(2*(9-i))*MAX_OUTER_ARC).lo,
            (rel[5][1]+rat(2*(i-5))*MAX_OUTER_ARC).hi
        };
        if (rel[i][1].lo>rel[i][1].hi) return false;
    }
    for (int i=0;i<9;++i) {
        int label=(i+2)%9;
        ans[label]=rel[i];
        ans[label][1]=rel[i][1]+angle;
        if (label<2) ans[label][1]=ans[label][1]-TWO*PI;
    }
    return true;
}

bool reach_radius(Site& z,Vec center,I distance2) {
    I norm2=sq(center[0])+sq(center[1]);
    if (norm2.lo>0) {
        I rho=z[0], norm=root(norm2);
        I co=(sq(rho)+norm2-distance2)/(TWO*rho*norm);
        if (co.lo>S) return false;
        if (co.lo>0 && (z[1].hi-z[1].lo)<PI.lo) {
            I t0=mid(z[1]);
            Trig rot=trig(t0);
            I along=center[0]*rot.c+center[1]*rot.s;
            I across=center[1]*rot.c-center[0]*rot.s;
            if (along.lo>=0) {
                I phase=t0+angle_shift(along,across);
                Int width=acos(co).hi;
                z[1]=intersection(z[1],{phase.lo-width,phase.hi+width});
                if (z[1].lo>z[1].hi) return false;
            }
        }
    }
    Trig t=trig(z[1]);
    I parallel=center[0]*t.c+center[1]*t.s;
    I transverse=center[0]*t.s-center[1]*t.c;
    I h2=distance2-sq(transverse);
    if (h2.hi<0) return false;
    I h=root(nonnegative(h2));
    z[0]=intersection(z[0],{(parallel-h).lo,(parallel+h).hi});
    return z[0].lo<=z[0].hi;
}

Int alpha_upper(I rho) {
    if (rho.hi>=RHO_OPTIMUM.lo && rho.lo<=RHO_OPTIMUM.hi)
        return MAX_OUTER_ARC.hi;
    I edge=rho.hi<RHO_OPTIMUM.lo?point(rho.hi):point(rho.lo);
    return acos((edge+(ONE-R2)/edge)/TWO).hi;
}

bool contract_sites(const Geometry& g,std::array<Site,9>& sites) {
    const Inner& y=g.y;
    for (int repeat=0;repeat<3;++repeat) {
        std::array<Int,9> al;
        for (int i=0;i<9;++i) {
            bool p=is_p_edge(i) || is_p_edge((i+8)%9);
            bool q=!is_p_edge(i) || !is_p_edge((i+8)%9);
            if (p && !reach_radius(sites[i],{y[0],y[2]},FOUR_R2)) return false;
            if (q && !reach_radius(sites[i],{-y[1],y[2]},FOUR_R2)) return false;
            if ((i==2 || i==7) &&
                !reach_radius(sites[i],{g.offset,y[2]+(i==2?g.height:-g.height)},R2))
                return false;
            al[i]=alpha_upper(sites[i][0]);
        }
        Int total=0;
        for (Int width:al) total+=width;
        if (total<PI.lo) return false;
        for (int i=0;i<9;++i) {
            int j=(i+1)%9;
            I shift=i==8?TWO*PI:ZERO;
            I ai=sites[i][1], aj=sites[j][1]+shift;
            Int gap=al[i]+al[j];
            Int needed=std::max<Int>(PI.lo-total+al[i], aj.lo-ai.hi-al[j]);
            if (needed>al[i]) return false;
            if (needed>0) {
                Trig cut=trig(point(needed));
                I delta=R2-sq(cut.s);
                if (delta.hi<0) return false;
                I span=root(nonnegative(delta));
                sites[i][0]=intersection(sites[i][0],{(cut.c-span).lo,(cut.c+span).hi});
                if (sites[i][0].lo>sites[i][0].hi) return false;
            }
            sites[i][1]=intersection(ai,{aj.lo-gap,aj.hi});
            sites[j][1]=intersection(sites[j][1],{ai.lo-shift.hi,ai.hi+gap-shift.lo});
            if (sites[i][1].lo>sites[i][1].hi || sites[j][1].lo>sites[j][1].hi) return false;
        }
    }
    return true;
}

struct Eval {
    I value=ZERO;
    Gradient gradient{};
    bool possible=true, smooth=true;
};

Eval evaluate(int i,const Geometry& g,const Site& site,const Coefficients& c,bool derivatives,
              bool restrict_domain=true,const Vec* tangent=nullptr) {
    const Inner& y=g.y;
    I rho=site[0], theta=site[1];
    Trig angle=trig(theta);
    I cx=rho*angle.c, cy=rho*angle.s;
    int previous=(i+8)%9;
    I in=c.outer(previous,y), out=c.outer(i,y);
    I a=in-out,b=in+out;
    I k=ONE-R2;
    I co=(rho+k/rho)/TWO;
    I alpha=acos(co);
    Eval result;
    result.value=a*theta-b*alpha;
    if (derivatives) {
        for (int j=0;j<3;++j)
            result.gradient[j]=(c.slope[previous][j]-c.slope[i][j])*theta
                -(c.slope[previous][j]+c.slope[i][j])*alpha;
        I sine2=ONE-sq(co);
        if (sine2.lo>rat(1,1000000).hi) {
            result.gradient[3]=b*(ONE-k/sq(rho))/(TWO*root(sine2));
            result.gradient[4]=a;
        } else result.smooth=false;
    }
    for (bool p:{true,false}) {
        bool attached_in=is_p_edge(previous)==p, attached_out=is_p_edge(i)==p;
        if (!attached_in && !attached_out) continue;
        I wi=attached_in?c.inner[previous]:ZERO, wo=attached_out?c.inner[i]:ZERO;
        I aa=wi-wo, bb=wi+wo;
        I fx=p?y[0]:-y[1], fy=y[2];
        I dx=cx-fx,dy=cy-fy;
        I parallel=rho-fx*angle.c-fy*angle.s;
        I across=fx*angle.s-fy*angle.c;
        I d2=intersection(sq(dx)+sq(dy),sq(parallel)+sq(across));
        assert(d2.lo<=d2.hi);
        if (d2.lo>FOUR_R2.hi && restrict_domain) {
            result.possible=false;
            return result;
        }
        if (bb.hi==0) continue;
        I phi=theta+angle_shift(parallel,across);
        I d=root(d2), ds=tangent?(*tangent)[p?0:1]:d;
        I beta=acos(ds/(TWO*R));
        I h2=FOUR_R2-sq(ds);
        result.value=result.value+aa*phi-bb*beta;
        if (tangent) {
            assert(h2.lo>0);
            result.value=result.value+bb*(d-ds)/root(h2);
        }
        if (derivatives) {
            if (d2.lo>rat(1,10000).hi && h2.lo>rat(1,10000).hi && parallel.lo>0) {
                I k1=bb/(d*root(h2)), k2=aa/d2;
                I gx=k1*dx-k2*dy, gy=k1*dy+k2*dx;
                if (p) result.gradient[0]=result.gradient[0]-gx;
                else result.gradient[1]=result.gradient[1]+gx;
                result.gradient[2]=result.gradient[2]-gy;
                result.gradient[3]=result.gradient[3]+gx*angle.c+gy*angle.s;
                result.gradient[4]=result.gradient[4]-gx*cy+gy*cx;
            } else result.smooth=false;
        }
    }
    if (i==2 || i==7) {
        I s=i==2?ONE:-ONE;
        I sx=cx-g.offset, sy=cy-y[2]-s*g.height;
        I d2=sq(sx)+sq(sy);
        if (d2.lo>R2.hi && restrict_domain) {
            result.possible=false;
            return result;
        }
        I weight=c.switch_weight[i==2?0:1];
        result.value=result.value+weight*(d2-R2);
        if (derivatives) {
            if (g.height_smooth && g.height.lo>rat(1,10000).hi) {
                I gx=TWO*weight*sx, gy=TWO*weight*sy;
                I shift=gy*s*g.separation/(TWO*g.height);
                result.gradient[0]=result.gradient[0]-gx/TWO+shift;
                result.gradient[1]=result.gradient[1]+gx/TWO+shift;
                result.gradient[2]=result.gradient[2]-gy;
                result.gradient[3]=result.gradient[3]+gx*angle.c+gy*angle.s;
                result.gradient[4]=result.gradient[4]-gx*cy+gy*cx;
            } else result.smooth=false;
        }
    }
    return result;
}

Site estimate(int i,const Inner& y,const Site& box,const Coefficients& c) {
    double lo[2]={real(box[0].lo),real(box[1].lo)};
    double hi[2]={real(box[0].hi),real(box[1].hi)};
    double r=real(R), a=real(y[0]), b=real(y[1]), v=real(y[2]);
    int j=(i+8)%9;
    double in=real(c.outer(j,y)),out=real(c.outer(i,y));
    struct Disk { double x,y,reach,A,B; bool inner; };
    std::vector<Disk> neighbors;
    for (bool p:{true,false}) {
        bool enter=is_p_edge(j)==p, leave=is_p_edge(i)==p;
        if (!enter && !leave) continue;
        double ii=enter?real(c.inner[j]):0,oo=leave?real(c.inner[i]):0;
        neighbors.push_back({p?a:-b,v,2*r,ii-oo,ii+oo,true});
    }
    if (i==2 || i==7) {
        double h2=r*r-(a+b)*(a+b)/4;
        if (h2<=0) return {mid(box[0]),mid(box[1])};
        neighbors.push_back({(a-b)/2,v+(i==2?1:-1)*std::sqrt(h2),r,
                             0,real(c.switch_weight[i==2?0:1]),false});
    }
    double best=1000, x=(lo[0]+hi[0])/2, t=(lo[1]+hi[1])/2;
    auto test=[&](double theta) {
        theta=std::clamp(theta,lo[1],hi[1]);
        double ct=std::cos(theta), st=std::sin(theta);
        double left=lo[0],right=hi[0];
        for (const auto& d:neighbors) {
            if (!d.inner) continue;
            double along=d.x*ct+d.y*st, across=d.x*st-d.y*ct;
            double height=d.reach*d.reach-across*across;
            if (height<=0) return false;
            double reach=std::sqrt(height);
            left=std::max(left,along-reach);
            right=std::min(right,along+reach);
        }
        if (left>=right) return false;
        auto value=[&](double u) {
            double res=(in-out)*theta-(in+out)*std::acos(std::clamp((1+u*u-r*r)/(2*u),0.,1.));
            for (const auto& d:neighbors) {
                double dx=u*ct-d.x,dy=u*st-d.y;
                double d2=dx*dx+dy*dy;
                if (d.inner) {
                    double psi=std::atan2(d.x*st-d.y*ct,u-d.x*ct-d.y*st);
                    res+=d.A*(theta+psi)-d.B*std::acos(std::clamp(std::sqrt(d2)/d.reach,0.,1.));
                } else res+=d.B*(d2-r*r);
            }
            return res;
        };
        double m0,m1,f0,f1;
        m0=(2*left+right)/3; m1=(left+2*right)/3;
        f0=value(m0); f1=value(m1);
        for (int it=0;it<29;++it) {
            if (f0<f1) right=m1; else left=m0;
            m0=(2*left+right)/3; m1=(left+2*right)/3;
            f0=value(m0); f1=value(m1);
        }
        double u=(left+right)/2,score=value(u);
        if (score<best) { best=score; x=u; t=theta; return true; }
        return false;
    };
    for (int n=0;n<=18;++n) test(lo[1]+(hi[1]-lo[1])*n/18);
    double dt=(hi[1]-lo[1])/18;
    for (int k=0;k<60 && dt>1e-9;++k) {
        double center=t;
        bool left=test(center-dt);
        bool right=test(center+dt);
        if (!left && !right) dt/=2;
    }
    return {point(std::clamp(dyadic(x).lo,box[0].lo,box[0].hi)),
            point(std::clamp(dyadic(t).lo,box[1].lo,box[1].hi))};
}

template<std::size_t N>
std::array<I,N> midpoint(const std::array<I,N>& x) {
    auto result=x;
    for (I& a:result) a=mid(a);
    return result;
}

struct Support {
    Int value;
    Inner slope;
};

I tangent_error(int i,const Geometry& g,const Geometry& anchor,const Site& z,
                const Site& z0,const Coefficients& c,const Vec& support_radius) {
    Inner wy;
    for (int j=0;j<3;++j) wy[j]=point(magnitude(g.y[j]-anchor.y[j]));
    I wr=point(magnitude(z[0]-z0[0])), wt=point(magnitude(z[1]-z0[1]));
    if (wt.hi>=PI.lo/2) return point(INF);
    I linear_displacement=wr+z0[0]*wt;
    I cart_error=wr*wt+z0[0]*sq(wt)/TWO;
    int j=(i+8)%9;
    I co=(z0[0]+(ONE-R2)/z0[0])/TWO;
    I sine=root(ONE-sq(co));
    I radial=(ONE-(ONE-R2)/sq(z0[0]))/(TWO*sine);
    I error=ZERO;
    for (int k=0;k<3;++k) {
        I da=point(magnitude(c.slope[j][k]-c.slope[i][k]));
        I db=point(magnitude(c.slope[j][k]+c.slope[i][k]));
        error=error+wy[k]*(da*wt+db*point(magnitude(radial))*wr);
    }
    Trig t=trig(z0[1]);
    I cx=z0[0]*t.c,cy=z0[0]*t.s;
    for (bool p:{true,false}) {
        I wi=is_p_edge(j)==p?c.inner[j]:ZERO;
        I wo=is_p_edge(i)==p?c.inner[i]:ZERO;
        I a=wi-wo,b=wi+wo;
        if (b.hi==0) continue;
        I dx=cx-(p?anchor.y[0]:-anchor.y[1]),dy=cy-anchor.y[2];
        I d2=sq(dx)+sq(dy),d=root(d2);
        I change=linear_displacement+cart_error+root(sq(wy[p?0:1])+sq(wy[2]));
        I min_d=d-change;
        if (min_d.lo<=rat(1,100).hi) return point(INF);
        I k1=b/(d*root(FOUR_R2-sq(support_radius[p?0:1]))),k2=a/d2;
        I gx=k1*dx-k2*dy,gy=k1*dy+k2*dx;
        error=error+root(sq(gx)+sq(gy))*cart_error
              +point(magnitude(a))*sq(change)/(TWO*sq(min_d));
    }
    if (i==2 || i==7) {
        I weight=c.switch_weight[i==2?0:1], sign=i==2?ONE:-ONE;
        I sx=cx-anchor.offset, sy=cy-anchor.y[2]-sign*anchor.height;
        error=error+TWO*weight*root(sq(sx)+sq(sy))*cart_error;
        if ((sign*sy).lo<0) {
            if (g.height.lo<rat(1,100).hi) return point(INF);
            I disp=(wy[0]+wy[1])/TWO;
            error=error+weight*point(magnitude(sy))*R2*sq(disp)/(sq(g.height)*g.height);
        }
    }
    return error;
}

Vec tangent_radii(const Geometry& g,const Geometry& reference,const Site& z,const Site& zm) {
    Trig tw=trig(z[1]),tm=trig(zm[1]);
    I cx=z[0]*tw.c,cy=z[0]*tw.s;
    I x0=zm[0]*tm.c,y0=zm[0]*tm.s;
    Vec ans;
    for (bool p:{true,false}) {
        I dx=cx-(p?g.y[0]:-g.y[1]),dy=cy-g.y[2];
        I dx0=x0-(p?reference.y[0]:-reference.y[1]),dy0=y0-reference.y[2];
        Int a=root(sq(dx)+sq(dy)).lo,b=root(sq(dx0)+sq(dy0)).lo;
        Int pick=std::min(b,a+(b-a)/3);
        ans[p?0:1]=point(std::min(pick,(TWO*R-rat(1,10000)).lo));
    }
    return ans;
}

bool curvature(int i,const Geometry& g,const Site& z,const Coefficients& c,
               std::array<I,3>& h) {
    I rho=z[0];
    Trig t=trig(z[1]);
    I k=ONE-R2, cosine=(rho+k/rho)/TWO, sin2=ONE-sq(cosine);
    if (sin2.lo<=rat(2,1000).hi) return false;
    I sine=root(sin2), c1=(ONE-k/sq(rho))/TWO, c2=k/(sq(rho)*rho);
    int j=(i+8)%9;
    h={(c.outer(j,g.y)+c.outer(i,g.y))*(c2/sine+cosine*sq(c1)/(sin2*sine)),ZERO,ZERO};
    for (bool p:{true,false}) {
        I wi=is_p_edge(j)==p?c.inner[j]:ZERO;
        I wo=is_p_edge(i)==p?c.inner[i]:ZERO;
        I a=wi-wo,b=wi+wo;
        if (b.hi==0) continue;
        I fx=p?g.y[0]:-g.y[1],fy=g.y[2];
        I parallel=rho-fx*t.c-fy*t.s, perpendicular=fx*t.s-fy*t.c;
        I d2=sq(parallel)+sq(perpendicular), gap=FOUR_R2-d2;
        if (parallel.lo<=0 || d2.lo<=rat(1,1000).hi || gap.lo<=rat(1,1000).hi)
            return false;
        I d=root(d2), u=parallel/d,v=perpendicular/d;
        I p1=b/root(gap),p2=b*d/(gap*root(gap)),angle=a/d2;
        I r0=p1/d;
        I gx=p1*u-a*v/d,gy=p1*v+a*u/d;
        I xx=p2*sq(u)+r0*sq(v)+TWO*angle*u*v;
        I xy=(p2-r0)*u*v-angle*(sq(u)-sq(v));
        I yy=p2*sq(v)+r0*sq(u)-TWO*angle*u*v;
        h[0]=h[0]+xx;
        h[1]=h[1]+rho*xy+gy;
        h[2]=h[2]+sq(rho)*yy-rho*gx;
    }
    if (i==2 || i==7) {
        I w=TWO*c.switch_weight[i==2?0:1];
        I cx=g.offset,cy=g.y[2]+(i==2?g.height:-g.height);
        I gx=w*(rho-cx*t.c-cy*t.s),gy=w*(cx*t.s-cy*t.c);
        h[0]=h[0]+w;
        h[1]=h[1]+gy;
        h[2]=h[2]+sq(rho)*w-rho*gx;
    }
    return true;
}

bool local_patch(int i,const Geometry& g,const Geometry& reference,const Site& whole,
                 const Coefficients& c,const Support& support,const Site& center,Site& patch) {
    if (magnitude(g.y[0]-A0)>rat(2,100).lo || magnitude(g.y[1]-B0)>rat(2,100).lo ||
        g.y[2].hi>rat(2,100).lo) return false;
    for (int j=0;j<2;++j) assert(center[j].lo>=whole[j].lo && center[j].hi<=whole[j].hi);
    Eval wide=evaluate(i,g,center,c,true,false), at=evaluate(i,reference,center,c,true,false);
    if (!wide.smooth || !at.smooth) return false;
    I base=at.value;
    for (int j=0;j<3;++j)
        base=base+(wide.gradient[j]-support.slope[j])*(g.y[j]-reference.y[j]);
    if (base.lo<support.value) return false;
    std::array<I,3> h0;
    if (!curvature(i,reference,center,c,h0) || h0[0].lo<=0) return false;
    I shear=mid(-h0[1]/h0[0]);
    for (int step=0;step<5;++step) {
        I w=rat(8,1000*(Int(1)<<step));
        for (int j=0;j<2;++j)
            patch[j]=intersection(whole[j],center[j]+I{-w.hi,w.hi});
        if (patch[0].lo>patch[0].hi || patch[1].lo>patch[1].hi) return false;
        std::array<I,3> h;
        if (!curvature(i,g,patch,c,h) || h[0].lo<=rat(1,10000).hi) continue;
        I a=point(h[0].lo), e=h[1]+shear*h[0];
        I q=h[2]+TWO*shear*h[1]+sq(shear)*h[0]-TWO*sq(e)/a;
        if (q.lo<=rat(1,1000000).hi) continue;
        I loss=sq(wide.gradient[3])/a+
               sq(wide.gradient[4]+shear*wide.gradient[3])/(TWO*point(q.lo));
        if ((base-loss).lo>=support.value) return true;
    }
    return false;
}

bool prove_site(int i,const Geometry& g,const Geometry& anchor,const Site& site,
                const Coefficients& c,const Support& support,int limit,const Site* center=nullptr) {
    const bool diagnose=limit>=100000;
    std::vector<Site> queue{site};
    Site patch;
    if (center && local_patch(i,g,anchor,site,c,support,*center,patch)) {
        queue.clear();
        for (int j=0;j<2;++j) {
            Site slab=site;
            if (site[j].lo<patch[j].lo) {
                slab[j].hi=patch[j].lo;
                queue.push_back(slab);
            }
            if (patch[j].hi<site[j].hi) {
                slab=site;
                slab[j].lo=patch[j].hi;
                queue.push_back(slab);
            }
        }
    }
    Inner delta;
    I slope_part=ZERO;
    for (int j=0;j<3;++j) {
        delta[j]=g.y[j]-anchor.y[j];
        slope_part=slope_part+support.slope[j]*delta[j];
    }
    while (!queue.empty()) {
        if (--limit<0) {
            if (diagnose) std::fprintf(stderr,"site %d exceeded interval budget\n",i);
            return false;
        }
        Site z=queue.back();
        queue.pop_back();
        Eval wide=evaluate(i,g,z,c,true);
        if (!wide.possible || (wide.value-slope_part).lo>=support.value) continue;
        Site zm=midpoint(z);
        if (wide.smooth) {
            Eval at=evaluate(i,anchor,zm,c,false,false);
            I mean=at.value;
            for (int j=0;j<3;++j)
                mean=mean+(wide.gradient[j]-support.slope[j])*delta[j];
            for (int j=0;j<2;++j) mean=mean+wide.gradient[j+3]*(z[j]-zm[j]);
            if (mean.lo>=support.value) continue;
            if (mean.hi<support.value) return false;
        }
        Vec tangent=tangent_radii(g,anchor,z,zm);
        Eval at=evaluate(i,anchor,zm,c,true,false,&tangent);
        if (at.smooth) {
            I mean=at.value;
            for (int j=0;j<3;++j)
                mean=mean+(at.gradient[j]-support.slope[j])*delta[j];
            for (int j=0;j<2;++j) mean=mean+at.gradient[j+3]*(z[j]-zm[j]);
            if (mean.lo-tangent_error(i,g,anchor,z,zm,c,tangent).hi>=support.value) continue;
        }
        int axis=(z[0].hi-z[0].lo)*2>=z[1].hi-z[1].lo?0:1;
        Int m=middle(z[axis]);
        if (m==z[axis].lo || m==z[axis].hi) {
            if (diagnose) {
                std::fprintf(stderr,"site %d interval could not contract near %.12g %.12g "
                             "(smooth %d %d, center residual %.9g, target loss %.9g)\n",
                             i,real(zm[0]),real(zm[1]),int(wide.smooth),int(at.smooth),
                             real(at.value.lo-support.value),real((wide.value-slope_part).lo-support.value));
            }
            return false;
        }
        Site other=z;
        z[axis].hi=m;
        other[axis].lo=m;
        queue.push_back(z);
        queue.push_back(other);
    }
    return true;
}

bool exclude(const Inner& box,const std::vector<Window>& windows,const Coefficients& reference) {
    std::array<Site,9> sites;
    if (!initial_sites(box,windows,sites)) return true;
    Coefficients coeff=reference;
    for (int j=0;j<9;++j) {
        if (coeff.outer(j,box).lo<=0) {
            for (auto& row:coeff.slope) row.fill(ZERO);
            break;
        }
    }
    Geometry g=geometry(box), anchor=geometry(midpoint(box));
    if (!contract_sites(g,sites)) return true;
    for (int i=0;i<9;++i)
        if (!evaluate(i,g,sites[i],coeff,false).possible) return true;
    I constant=TWO*PI*(coeff.outer(8,anchor.y)+coeff.inner[8]);
    Inner slope;
    for (int j=0;j<3;++j) slope[j]=TWO*PI*coeff.slope[8][j];
    std::array<Support,9> supports;
    std::array<Site,9> anchors;
    for (int i=0;i<9;++i) {
        Site z=estimate(i,anchor.y,sites[i],coeff);
        anchors[i]=z;
        Eval value=evaluate(i,anchor,z,coeff,true,false);
        assert(value.possible);
        supports[i].value=value.value.lo;
        constant=constant+point(value.value.lo);
        for (int j=0;j<3;++j) {
            supports[i].slope[j]=value.smooth?mid(value.gradient[j]):ZERO;
            slope[j]=slope[j]+supports[i].slope[j];
        }
    }
    for (int j=0;j<3;++j) constant=constant+slope[j]*(box[j]-anchor.y[j]);
    if (constant.lo<=0) return false;
    Int budget=constant.lo-1, margin=std::max<Int>(1,constant.lo/18);
    for (int i:{2,7,4,5,0,1,8,3,6}) {
        Int loss=margin;
        for (;;) {
            if (loss>budget) return false;
            Support target=supports[i];
            target.value-=loss;
            int limit=budget<rat(1,10000).hi?10000:800;
            if (prove_site(i,g,anchor,sites[i],coeff,target,limit,&anchors[i])) break;
            if (loss==budget) return false;
            loss=std::min(2*loss,budget);
        }
        budget-=loss;
    }
    return true;
}

bool near_candidate(const Inner& box,I radius) {
    return magnitude(box[0]-A0)<=radius.lo && magnitude(box[1]-B0)<=radius.lo &&
           box[2].hi<=radius.lo;
}

Site polar_anchor(int i) {
    I x=anchor_centers[i][0],y=anchor_centers[i][1];
    I rho=mid(root(sq(x)+sq(y)));
    if (i==0) return {rho,ZERO};
    if (i<5) return {rho,mid(angle_upper_half(x,y))};
    return {rho,mid(TWO*PI-angle_upper_half(x,-y))};
}

bool prove_comparison(int i,const Inner& box,const Site& anchor_site,const Site& slab,
                      const Coefficients& c,int depth) {
    Inner y0=midpoint(box);
    Geometry g=geometry(box), reference=geometry(y0);
    Eval center=evaluate(i,reference,anchor_site,c,true,false);
    Eval wide=evaluate(i,g,anchor_site,c,true,false);
    assert(center.smooth && wide.smooth);
    Support support{0,{}};
    I threshold=center.value;
    for (int j=0;j<3;++j) {
        support.slope[j]=mid(center.gradient[j]);
        threshold=threshold+(wide.gradient[j]-support.slope[j])*(box[j]-y0[j]);
    }
    support.value=threshold.hi+1;
    if (prove_site(i,g,reference,slab,c,support,depth==0?150000:20000)) return true;
    if (depth==0) {
        std::fprintf(stderr,"near parameters %.12g %.12g %.12g; slab %.9g %.9g %.9g %.9g\n",
                     real(y0[0]),real(y0[1]),real(y0[2]),
                     real(slab[0].lo),real(slab[0].hi),real(slab[1].lo),real(slab[1].hi));
        return false;
    }
    int axis=0;
    for (int j=1;j<3;++j)
        if (box[j].hi-box[j].lo>box[axis].hi-box[axis].lo) axis=j;
    Inner first=box, second=box;
    first[axis].hi=second[axis].lo=middle(box[axis]);
    return prove_comparison(i,first,anchor_site,slab,c,depth-1) &&
           prove_comparison(i,second,anchor_site,slab,c,depth-1);
}

void verify_near(const std::vector<Window>& windows,const Coefficients& c) {
    I radius=rat(1,10000), polar=rat(13,10000), spatial=rat(1,500);
    Inner y{A0+I{-radius.hi,radius.hi},B0+I{-radius.hi,radius.hi},I{0,radius.hi}};
    Geometry g=geometry(y);
    std::array<Site,9> sites;
    assert(initial_sites(y,windows,sites) && contract_sites(g,sites));
    for (int i=0;i<9;++i) {
        Site z0=polar_anchor(i);
        Site close{z0[0]+I{-polar.hi,polar.hi},z0[1]+I{-polar.hi,polar.hi}};
        Trig tc=trig(close[1]);
        assert(magnitude(close[0]*tc.c-anchor_centers[i][0])<spatial.lo);
        assert(magnitude(close[0]*tc.s-anchor_centers[i][1])<spatial.lo);
        for (int axis=0;axis<2;++axis) {
            Site slab=sites[i];
            slab[axis].hi=std::min(slab[axis].hi,close[axis].lo);
            if (slab[axis].lo<=slab[axis].hi)
                assert(prove_comparison(i,y,z0,slab,c,12));
            slab=sites[i];
            slab[axis].lo=std::max(slab[axis].lo,close[axis].hi);
            if (slab[axis].lo<=slab[axis].hi)
                assert(prove_comparison(i,y,z0,slab,c,12));
        }
        std::printf("Near candidate, outer site %d certified.\n",i);
        std::fflush(stdout);
    }
}

int widest(const Inner& y) {
    int axis=0;
    for (int j=1;j<3;++j)
        if (y[j].hi-y[j].lo>y[axis].hi-y[axis].lo) axis=j;
    return axis;
}

std::array<Inner,2> split(const Inner& y,int axis) {
    std::array<Inner,2> parts{y,y};
    parts[0][axis].hi=parts[1][axis].lo=middle(y[axis]);
    return parts;
}

} // namespace fan

int main(int argc,char** argv) {
    using namespace fan;
    assert(argc==3 || argc==4);
    auto windows=read_windows(argv[1]);
    Coefficients coefficients(argv[2]);
    verify_near(windows,coefficients);
    if (argc==4 && std::string_view(argv[3])=="near") return 0;
    unsigned jobs=argc==4?std::stoul(argv[3]):std::clamp(std::thread::hardware_concurrency(),1u,8u);
    assert(jobs>=1 && jobs<=64);
    for (const auto& row:windows) assert(row.q.hi<=rat(256,1000).hi);
    const I near=rat(1,10000);
    std::vector<Inner> batches{
        Inner{I{rat(-12,100).lo,rat(62,100).hi},
              I{rat(-256,1000).lo,rat(256,1000).hi},
              I{0,rat(14,100).hi}}
    };
    for (int round=0;round<7;++round) {
        std::vector<Inner> refined;
        for (const Inner& y:batches)
            for (const Inner& part:split(y,widest(y))) refined.push_back(part);
        batches.swap(refined);
    }
    std::atomic<unsigned long long> calls{0}, leaves{0}, near_leaves{0};
    std::mutex lock;
    std::condition_variable ready;
    unsigned active=0;
    bool failed=false;
    auto worker=[&] {
        for (;;) {
            Inner y;
            {
                std::unique_lock<std::mutex> guard(lock);
                ready.wait(guard,[&]{return failed || !batches.empty() || active==0;});
                if (failed || batches.empty()) return;
                y=batches.back();
                batches.pop_back();
                ++active;
            }
            auto c=++calls;
            if (c%1000==0) {
                std::printf("%llu boxes (%llu excluded, %llu near), current %.6f %.6f %.6f.\n",
                            c,leaves.load(),near_leaves.load(),real(y[0]),real(y[1]),real(y[2]));
                std::fflush(stdout);
            }
            int axis=-1;
            if (near_candidate(y,near)) ++near_leaves;
            else if (exclude(y,windows,coefficients)) ++leaves;
            else axis=widest(y);
            {
                std::lock_guard<std::mutex> guard(lock);
                if (axis>=0) {
                    if (y[axis].hi-y[axis].lo<rat(1,10000000).hi) {
                        failed=true;
                        std::fprintf(stderr,"Unclosed box near %.12f %.12f %.12f.\n",
                                     real(y[0]),real(y[1]),real(y[2]));
                    } else {
                        for (const auto& part:split(y,axis)) batches.push_back(part);
                    }
                }
                --active;
            }
            ready.notify_all();
        }
    };
    std::vector<std::thread> threads;
    for (unsigned i=0;i<jobs;++i) threads.emplace_back(worker);
    for (auto& thread:threads) thread.join();
    if (failed) return 1;
    assert(batches.empty() && active==0);
    std::printf("Full 4+5 branch certified: %llu excluded leaves, %llu near leaves.\n",
                leaves.load(),near_leaves.load());
}
