// Fixed-point interval kernels for the two-fan certificate.
#pragma once
#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstdint>

namespace fan {
using Int = std::int64_t;
using Wide = __int128_t;
constexpr Int S = Int(1) << 51;

inline Int checked(Wide q) {
    assert(q > -(Wide(1)<<63) && q < (Wide(1)<<63));
    return Int(q);
}
inline Int floor(Wide a, Wide b) {
    assert(b > 0);
    return checked(a/b - (a%b < 0));
}
inline Int ceil(Wide a, Wide b) { return -floor(-a,b); }

struct I { Int lo, hi; };
inline I point(Int a) { return {a,a}; }
inline I rat(Int a, Int b=1) { return {floor(Wide(a)*S,b),ceil(Wide(a)*S,b)}; }
inline I operator-(I a) { return {-a.hi,-a.lo}; }
inline I operator+(I a, I b) { return {checked(Wide(a.lo)+b.lo),checked(Wide(a.hi)+b.hi)}; }
inline I operator-(I a, I b) { return a+(-b); }
inline I operator*(I a, I b) {
    Wide ab[] = {Wide(a.lo)*b.lo,Wide(a.lo)*b.hi,Wide(a.hi)*b.lo,Wide(a.hi)*b.hi};
    return {floor(*std::min_element(ab,ab+4),S),ceil(*std::max_element(ab,ab+4),S)};
}
inline I operator/(I a, I b) {
    if (b.hi < 0) return (-a)/(-b);
    assert(b.lo > 0);
    return {floor(Wide(a.lo)*S,a.lo<0?b.lo:b.hi),
            ceil(Wide(a.hi)*S,a.hi<0?b.hi:b.lo)};
}
inline I sq(I a) {
    Wide x=Wide(a.lo)*a.lo, y=Wide(a.hi)*a.hi;
    return {a.lo<=0 && a.hi>=0 ? 0 : floor(std::min(x,y),S),ceil(std::max(x,y),S)};
}
inline Int magnitude(I a) { return std::max(std::abs(a.lo),std::abs(a.hi)); }
inline Int middle(I a) { return a.lo+(a.hi-a.lo)/2; }
inline I mid(I a) { return point(middle(a)); }
inline I hull(I a, I b) { return {std::min(a.lo,b.lo),std::max(a.hi,b.hi)}; }
inline I intersection(I a, I b) { return {std::max(a.lo,b.lo),std::min(a.hi,b.hi)}; }
inline I nonnegative(I a) { return {std::max<Int>(0,a.lo),std::max<Int>(0,a.hi)}; }
inline double real(Int a) { return double(a)/S; }
inline double real(I a) { return real(middle(a)); }
inline I dyadic(double a) { return point(Int(a*S)); } // heuristic input, interpreted exactly

inline Int isqrt(Wide a) {
    assert(a>=0 && a<Wide(16*S)*(16*S));
    // Correct the heuristic seed using integer comparisons.
    Int h=Int(std::sqrt(static_cast<long double>(a)));
    while (Wide(h)*h>a) --h;
    while (Wide(h+1)*(h+1)<=a) ++h;
    return h;
}
inline I root(I a) {
    assert(a.lo>=0);
    Int low=isqrt(Wide(a.lo)*S), high=isqrt(Wide(a.hi)*S);
    return {low,high+(Wide(high)*high<Wide(a.hi)*S)};
}

const I PI={rat(3141592653589793238LL,1000000000000000000LL).lo,
            rat(3141592653589793239LL,1000000000000000000LL).hi};
const I ONE=point(S), ZERO=point(0), TWO=point(2*S);

inline I atan_series(I x,int terms,Int tail) {
    I xx=sq(x), ans=ZERO;
    for (int j=terms-1;j>=0;--j) ans=rat(j%2?-1:1,2*j+1)+xx*ans;
    ans=x*ans;
    return {ans.lo-tail,ans.hi+tail};
}
inline I atan_small(I x) {
    assert(magnitude(x)<=S/2);
    // The omitted term is at most (1/2)^47 / 47.
    return atan_series(x,23,rat(1,47*(Int(1)<<47)).hi);
}
inline I atan_unit(Int numerator,Int denominator) {
    assert(0<=numerator && numerator<=denominator && denominator>0);
    static const auto table=[] {
        std::array<I,65> a{};
        for (int k=0;k<=64;++k) {
            I t=rat(k,64);
            a[k]=k<=32 ? atan_small(t) : PI/rat(4)+atan_small((t-ONE)/(t+ONE));
        }
        return a;
    }();
    int index=int(floor(Wide(numerator)*64,denominator));
    I t=point(numerator)/point(denominator), base=rat(index,64);
    I d=(t-base)/(ONE+t*base);
    assert(magnitude(d)<=rat(1,63).hi);
    // (1/63)^9 / 9 < 1/S.
    return table[index]+atan_series(d,4,1);
}
inline I angle_pos_x(Int x,Int y) {
    assert(x>=0);
    if (y<0) return -angle_pos_x(x,-y);
    if (y==0) return ZERO;
    if (y>x) return PI/TWO-atan_unit(x,y);
    return atan_unit(y,x);
}
inline I angle_shift(I x,I y) {
    x=nonnegative(x);
    return {angle_pos_x(y.lo<0?x.lo:x.hi,y.lo).lo,
            angle_pos_x(y.hi>0?x.lo:x.hi,y.hi).hi};
}
inline I angle_upper_half(I x,I y) {
    assert(y.lo>=0);
    if (x.lo>=0) return angle_shift(x,y);
    if (x.hi<=0) return PI-angle_shift(-x,y);
    return {angle_pos_x(x.hi,y.lo).lo,(PI-angle_pos_x(-x.lo,y.lo)).hi};
}
inline I acos_point(Int x) {
    x=std::clamp(x,Int(0),S);
    if (x==S) return ZERO;
    if (x==0) return PI/TWO;
    I y=root(ONE-sq(point(x)));
    return {angle_pos_x(x,y.lo).lo,angle_pos_x(x,y.hi).hi};
}
inline I acos(I x) { return {acos_point(x.hi).lo,acos_point(x.lo).hi}; }

struct Trig { I c,s; };
inline Trig taylor_trig(I x,int terms,Int tail) {
    I xx=-sq(x), a=ONE,b=x,c=a,s=b;
    for (int k=1;k<terms;++k) {
        a=a*(xx/rat((2*k)*(2*k-1)));
        b=b*(xx/rat((2*k)*(2*k+1)));
        c=c+a;
        s=s+b;
    }
    return {{c.lo-tail,c.hi+tail},{s.lo-tail,s.hi+tail}};
}
inline Trig trig(I angle) {
    // Nearest lower table angle in [-4,10], with step 1/32.
    static const auto table=[] {
        std::array<Trig,449> a{};
        for (int i=0;i<int(a.size());++i)
            // All table angles are at most 10 in magnitude. Taylor remainder
            // after the retained terms is at most 10^56/56! < 1/S.
            a[i]=taylor_trig(rat(i-128,32),29,1);
        return a;
    }();
    Int center=middle(angle);
    int index=int(floor(Wide(center)*32,S))+128;
    assert(index>=0 && index<int(table.size()));
    I d=point(center)-rat(index-128,32);
    assert(d.lo>=0 && d.hi<=S/32);
    // Both remainders are less than (1/32)^8 / 8! < 1/S.
    Trig near=taylor_trig(d,4,1);
    const Trig& base=table[index];
    I co=base.c*near.c-base.s*near.s, si=base.s*near.c+base.c*near.s;
    Int width=std::max(center-angle.lo,angle.hi-center);
    I w=point(width), second=sq(w)/TWO;
    Int dc=(point(magnitude(si))*w+second).hi;
    Int ds=(point(magnitude(co))*w+second).hi;
    return {intersection({co.lo-dc,co.hi+dc},{-S,S}),
            intersection({si.lo-ds,si.hi+ds},{-S,S})};
}
} // namespace fan
