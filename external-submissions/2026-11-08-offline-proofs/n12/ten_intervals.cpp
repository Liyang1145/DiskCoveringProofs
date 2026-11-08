#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <vector>

// An exact verifier. All geometry and weights are dyadic or integral.
// sqrt(double) only supplies an initial guess for the checked integer root.
using Int = std::int64_t;
using Wide = __int128_t;
constexpr Int S = Int{1} << 40;
constexpr Int R = 397044643907;
constexpr Int R9 = 397036907462;
constexpr Int D9 = 739421569679;
constexpr int K = 32;

Int div_down(Wide a, Wide b) {
    if (b <= 0) throw std::logic_error("nonpositive divisor");
    Wide q = a / b - (a % b < 0);
    if (q <= std::numeric_limits<Int>::min() || q >= std::numeric_limits<Int>::max()) {
        throw std::overflow_error("fixed-point overflow");
    }
    return Int(q);
}

Int div_up(Wide a, Wide b) {
    return -div_down(-a, b);
}

Wide square(Int a) { return Wide(a) * a; }

Int root_down(Wide x) {
    if (x < 0) throw std::logic_error("negative radicand");
    Int a = Int(std::sqrt(double(x)));
    while (square(a) > x) --a;
    while (square(a + 1) <= x) ++a;
    return a;
}

Int root_up(Wide x) {
    Int a = root_down(x);
    return a + (square(a) != x);
}

struct I { Int lo, hi; };
constexpr I pi{3454217652357, 3454217652358};
constexpr I zero{0, 0};
constexpr I one{S, S};
constexpr I tau{2*pi.lo, 2*pi.hi};

I point(Int a) { return {a, a}; }
I operator+(I a, I b) { return {a.lo+b.lo, a.hi+b.hi}; }
I operator-(I a, I b) { return {a.lo-b.hi, a.hi-b.lo}; }
I operator-(I a) { return {-a.hi, -a.lo}; }
I operator/(I a, Int b) { return {div_down(a.lo, b), div_up(a.hi, b)}; }
I operator*(Int a, I b) { return a >= 0 ? I{a*b.lo, a*b.hi} : I{a*b.hi, a*b.lo}; }

I operator*(I a, I b) {
    if (a.lo >= 0) {
        if (b.lo >= 0) return {div_down(Wide(a.lo)*b.lo, S), div_up(Wide(a.hi)*b.hi, S)};
        if (b.hi <= 0) return -(a * (-b));
        return {div_down(Wide(a.hi)*b.lo, S), div_up(Wide(a.hi)*b.hi, S)};
    }
    if (a.hi <= 0) return -((-a) * b);
    if (b.lo >= 0 || b.hi <= 0) return b * a;
    Wide lower = std::min(Wide(a.lo)*b.hi, Wide(a.hi)*b.lo);
    Wide upper = std::max(Wide(a.lo)*b.lo, Wide(a.hi)*b.hi);
    return {div_down(lower, S), div_up(upper, S)};
}

I operator/(I a, I b) {
    if (b.lo <= 0) throw std::logic_error("interval divisor contains zero");
    return {div_down(Wide(a.lo)*S, a.lo >= 0 ? b.hi : b.lo),
            div_up(Wide(a.hi)*S, a.hi >= 0 ? b.lo : b.hi)};
}

I sqrt(I a) {
    return {root_down(Wide(a.lo)*S), root_up(Wide(a.hi)*S)};
}

I square(I a) {
    Wide h = std::max(square(a.lo), square(a.hi));
    Wide l = a.lo <= 0 && a.hi >= 0 ? 0 : std::min(square(a.lo), square(a.hi));
    return {div_down(l, S), div_up(h, S)};
}

I positive(I a) { return {std::max<Int>(0,a.lo), std::max<Int>(0,a.hi)}; }

I norm_squared(Int x, Int y) {
    Wide n = square(x) + square(y);
    return {div_down(n, S), div_up(n, S)};
}

I norm(Int x, Int y) {
    Wide n = square(x) + square(y);
    Int a = root_down(n);
    return {a, a + (square(a) != n)};
}

// atan on [0, 1/2 + 1/S]. For exact arguments on this interval, the first
// omitted term bounds the error of the alternating series.
I atan_small(I x) {
    static const std::array<I,15> coeff=[] {
        std::array<I,15> value{};
        for (int i=0;i<15;++i) value[i]=one/(2*i+1);
        return value;
    }();
    int n = x.hi<=S/4 ? 9 : (x.hi<=S/3+1 ? 12 : 15);
    I x2 = x*x;
    I p = zero;
    for (int i = n - 1; i >= 0; --i) {
        p = coeff[i] - x2*p;
    }
    I a = x*p;
    // (1/2 + 1/S)^31 / 31 < 17/S, for S = 2^40.
    return {a.lo - 17, a.hi + 17};
}

I atan_ratio(Int n, Int d) {
    if (n == 0) return zero;
    if (n == d) return pi/4;
    if (2*n <= d) return atan_small(point(n)/point(d));
    return pi/4 - atan_small(point(d-n)/point(d+n));
}

I arg_turn(Int x, Int y) {
    Int a = std::abs(x), b = std::abs(y);
    I angle = a >= b ? atan_ratio(b, a) : pi/2 - atan_ratio(a, b);
    if (x < 0) angle = pi - angle;
    if (y < 0) angle = -angle;
    return angle/tau;
}

// 2 asin(sqrt(z)), z=(1-c)/2, with the same binomial series as verify.py.
I acos_nonnegative(Int c) {
    constexpr int N = 17;
    static const auto coefficient = [] {
        std::array<I, N> value{};
        value[0] = one;
        for (int j = 1; j < N; ++j) {
            value[j] = (Int(2*j-1)*(2*j-1)*value[j-1])/(Int(2*j)*(2*j+1));
        }
        return value;
    }();
    I z = (one - point(c))/2;
    int n=N;
    Int tail=0;
    if (z.hi<=S/32) {n=8;tail=4;}
    else if (z.hi<=S/16) {n=10;tail=4;}
    else if (z.hi<=S/8) {n=14;tail=4;}
    else {
        I z2=z*z, z4=z2*z2, z8=z4*z4;
        tail=4*(z8*z8*z).hi;
    }
    I p = coefficient[n-1];
    for (int j = n - 2; j >= 0; --j) p = coefficient[j] + z*p;
    return 2*(sqrt(z)*p) + I{0, tail};
}

I acos_at(Int c) {
    if (c >= S) return zero;
    if (c <= -S) return pi;
    if (c >= 0) return acos_nonnegative(c);
    return pi - acos_nonnegative(-c);
}

// Enclose the lifted angular arc of the circle with the given radius cut by
// a disk of radius r at the indicated relative center (vx,vy).
I upper_arc(Int vx, Int vy, Int radius, Int r) {
    constexpr I full{-S/2, S/2};
    if (vx == 0 && vy == 0) return r >= radius ? full : zero;
    I e = norm(vx, vy);
    if (e.lo > radius+r || e.hi < radius-r) return zero;
    if (e.hi + radius <= r) return full;
    I denominator = 2*(point(radius)*e);
    if (denominator.lo <= 0) return full;
    I c = (norm_squared(vx, vy) + point(radius)*point(radius) - point(r)*point(r)) / denominator;
    if (c.lo >= S) return zero;
    if (c.lo <= -S) return full;
    Int half = (acos_at(c.lo)/tau).hi;
    I mid = arg_turn(vx, vy);
    if (mid.hi-mid.lo+2*half >= S) return full;
    return {mid.lo-half, mid.hi+half};
}

struct Curve {
    Int x, y, radius, sign;
    std::array<Int, K> lo{}, hi{}, w{};
    std::array<Wide, K + 1> prefix{};

    Curve(Int x0, Int y0, Int radius0, Int sign0, Int exposure, const Int *weights)
        : x(x0), y(y0), radius(radius0), sign(sign0) {
        for (int j = 0; j < K; ++j) {
            lo[j] = std::max(-exposure, -S/2 + (S/K)*j);
            hi[j] = std::max(lo[j], std::min(exposure, -S/2 + (S/K)*(j+1)));
            w[j] = weights[j];
            if (w[j] < 0 || w[j] > 50000000) throw std::logic_error("bad weight");
            prefix[j+1] = prefix[j] + Wide(w[j])*(hi[j]-lo[j]);
        }
    }

    Wide through(Int a) const {
        if (a <= -S/2) return 0;
        if (a >= S/2) return prefix[K];
        int j = int((a + S/2)/(S/K));
        Int length = std::max<Int>(0, std::min(a, hi[j]) - lo[j]);
        return prefix[j] + Wide(w[j])*length;
    }

    Wide upper_mass(Int cx, Int cy, Int r) const {
        if (prefix[K] == 0) return 0;
        I arc = upper_arc(sign*(cx-x), sign*(cy-y), radius, r);
        Wide mass = 0;
        for (int turn = -1; turn <= 1; ++turn) {
            mass += through(arc.hi+turn*S) - through(arc.lo+turn*S);
        }
        return std::min(mass, prefix[K]);
    }
};

struct Box { I x, y; };

Wide max_square(I a) { return std::max(square(a.lo), square(a.hi)); }
Wide min_square(I a) {
    return a.lo <= 0 && a.hi >= 0 ? 0 : std::min(square(a.lo), square(a.hi));
}

// Same necessary-condition contraction as the Python reference. Keep its
// pass count, sample order and rounding fixed for the certificate paths.
extern "C" __declspec(dllexport) int contract_nine(Int* bounds) {
    try {
        constexpr Int T=D9-R9;
        constexpr Wide r2=Wide(R9)*R9;
        std::array<I,5> box;
        for (int k=0;k<5;++k) box[k]={bounds[2*k],bounds[2*k+1]};
        auto distance=[&](int k,Int x,Int y) {
            return min_square(box[k]-point(x))+(k==0?square(y):min_square(box[k+1]-point(y)));
        };
        auto narrow=[&](int k,Int x,Int y) {
            if (k==0) {
                Wide gap=r2-square(y);
                if (gap<0) return false;
                Int h=root_down(gap)+1;
                box[0]={std::max(box[0].lo,x-h),std::min(box[0].hi,x+h)};
                return box[0].lo<=box[0].hi;
            }
            Wide gx=r2-min_square(box[k+1]-point(y));
            Wide gy=r2-min_square(box[k]-point(x));
            if (std::min(gx,gy)<0) return false;
            Int hx=root_down(gx)+1, hy=root_down(gy)+1;
            box[k]={std::max(box[k].lo,x-hx),std::min(box[k].hi,x+hx)};
            box[k+1]={std::max(box[k+1].lo,y-hy),std::min(box[k+1].hi,y+hy)};
            return box[k].lo<=box[k].hi && box[k+1].lo<=box[k+1].hi;
        };
        static const auto central=[] {
            constexpr Int T=D9-R9;
            std::vector<std::pair<Int,Int>> points{{T,0},{-T,0},{0,T},{0,-T}};
            for (int j=1;j<10;++j) {
                Int x=div_down(Wide(T-2)*(100-j*j),100+j*j);
                Int y=div_down(Wide(T-2)*(20*j),100+j*j);
                for (int i=0;i<4;++i) {
                    points.push_back({x,y});
                    Int nx=-y; y=x; x=nx;
                }
            }
            return points;
        }();
        for (int pass=0;pass<2;++pass) {
            Int hi=box[0].hi;
            for (int k : {1,3}) {
                Wide d=min_square(box[k])+min_square(box[k+1]);
                if (d>square(hi)) return 0;
                box[0].lo=std::max(box[0].lo,root_down(d));
                for (int j : {k,k+1}) box[j]={std::max(box[j].lo,-hi),std::min(box[j].hi,hi)};
            }
            if (std::any_of(box.begin(),box.end(),[](I a){return a.lo>a.hi;})) return 0;
            if (!narrow(1,-T,0)) return 0;
            for (auto [x,y] : central) {
                int id=-1;
                for (int k : {0,1,3}) {
                    if (distance(k,x,y)<=r2) {
                        if (id>=0) {id=-2;break;}
                        id=k;
                    }
                }
                if (id==-1 || (id>=0 && !narrow(id,x,y))) return 0;
            }
        }
        for (int k=0;k<5;++k) {bounds[2*k]=box[k].lo;bounds[2*k+1]=box[k].hi;}
        return 1;
    } catch (...) {
        return -2;
    }
}

// Return the exposed half-angle in turns, rounded down to our dyadic grid.
extern "C" __declspec(dllexport) Int exposed_half(Int a, Int rho) {
    if (a >= rho) return S/2;
    I cosine = - (point(a)/point(rho));
    return (acos_at(cosine.hi)/tau).lo;
}

// Output status 1 means every possible center was certified. Status 0 and
// negative values carry no certification. When returning 0 we report a
// center for possible additional search constraints.
extern "C" __declspec(dllexport) int check_measure(Int a, Int x, Int y, Int rho,
                                                     const Int *weights, Int limit,
                                                     Int *out) {
    try {
        if (rho < R || a < 0 || x < 0 || y < 0) return -2;
        if (norm(x+a, y).hi + rho >= S) return -2;
        Int exposure = exposed_half(a, rho);
        Curve curves[] = {{0, 0, S, 1, S/2, weights},
                          {x+a, y, rho, 1, exposure, weights+K},
                          {x-a, y, rho, -1, exposure, weights+2*K}};
        Wide total = curves[0].prefix[K] + curves[1].prefix[K] + curves[2].prefix[K];
        if (total <= 0) return -2;
        std::vector<Box> stack{{{-S, S}, {-S, S}}};
        Int checked = 0;
        while (!stack.empty()) {
            Box b = stack.back();
            stack.pop_back();
            if (++checked > limit) { out[2] = checked; return -1; }
            if (max_square(b.x)+max_square(b.y) < square(S-R)) continue;
            if (min_square(b.x)+min_square(b.y) > square(S)) continue;
            Int mx = b.x.lo+(b.x.hi-b.x.lo)/2, my = b.y.lo+(b.y.hi-b.y.lo)/2;
            Int delta = root_up(square(b.x.hi-mx)+square(b.y.hi-my));
            Wide m = 0;
            for (const auto& curve : curves) m += curve.upper_mass(mx, my, R+delta);
            if (10*m < total) continue;
            if (delta <= S/200000) {
                out[0] = mx; out[1] = my; out[2] = checked;
                return 0;
            }
            if (b.x.hi-b.x.lo >= b.y.hi-b.y.lo) {
                stack.push_back({{mx, b.x.hi}, b.y});
                stack.push_back({{b.x.lo, mx}, b.y});
            } else {
                stack.push_back({b.x, {my, b.y.hi}});
                stack.push_back({b.x, {b.y.lo, my}});
            }
        }
        out[2] = checked;
        return 1;
    } catch (...) {
        return -2;
    }
}

std::vector<I> remove_arc(const std::vector<I>& input, I arc) {
    if (arc.lo == arc.hi) return input;
    auto current = input;
    for (int turn = -1; turn <= 1; ++turn) {
        I cut = arc + point(turn*S);
        std::vector<I> next;
        for (auto a : current) {
            if (cut.hi <= a.lo || cut.lo >= a.hi) {
                next.push_back(a);
                continue;
            }
            if (a.lo < cut.lo) next.push_back({a.lo, cut.lo});
            if (cut.hi < a.hi) next.push_back({cut.hi, a.hi});
        }
        current = std::move(next);
    }
    return current;
}

std::vector<I> exposed_mask(const Int *centers, Int rho, int k) {
    std::vector<I> parts{{-S/2, S/2}};
    Int x = centers[2*k], y = centers[2*k+1];
    for (int j = 0; j < 3; ++j) {
        Int dx = centers[2*j]-x, dy = centers[2*j+1]-y;
        // Coincident circles have the same exterior, so either copy can
        // serve as a witness wherever both are exposed.
        if (dx == 0 && dy == 0) continue;
        parts = remove_arc(parts, upper_arc(dx, dy, rho, rho));
    }
    if (x == 0 && y == 0) {
        if (rho >= S) parts.clear();
        return parts;
    }
    I d = norm(x, y);
    if (d.hi+rho <= S) return parts;
    I denom = 2*(d*point(rho));
    if (denom.lo <= 0) return {};
    I c = (one-norm_squared(x,y)-point(rho)*point(rho))/denom;
    Int half = (acos_at(c.lo)/tau).hi;
    I mid = arg_turn(x, y);
    return remove_arc(parts, {mid.lo-half, mid.hi+half});
}

constexpr std::array<int,7> test_radii{360,400,450,520,590,660,750};

Int test_radius(int i) { return div_down(Wide(test_radii[i])*S,1000); }

std::vector<I> concentric_mask(const Int* centers, Int rho, Int radius) {
    std::vector<I> parts{{-S/2,S/2}};
    for (int i=0;i<3;++i) parts=remove_arc(parts,upper_arc(centers[2*i],centers[2*i+1],radius,rho));
    return parts;
}

struct Segment { Int left, right, weight; Wide prefix; };

struct MaskedCurve {
    Int x, y, rho;
    int slot=-1;
    std::vector<Segment> segments;
    Wide total = 0;

    MaskedCurve(Int x, Int y, Int rho, const std::vector<I>& mask, const Int* w)
        : x(x), y(y), rho(rho) {
        if (x==0 && y==0) {
            if (rho==S) slot=0;
            for (int j=0;j<int(test_radii.size());++j) if (rho==test_radius(j)) slot=j+1;
        }
        for (auto part : mask) {
            for (int i = 0; i < K; ++i) {
                if (w[i] < 0 || w[i] > 50000000) throw std::logic_error("bad weight");
                if (!w[i]) continue;
                Int l = std::max(part.lo, -S/2 + i*(S/K));
                Int h = std::min(part.hi, -S/2 + (i+1)*(S/K));
                if (l >= h) continue;
                segments.push_back({l, h, w[i], total});
                total += Wide(w[i]) * (h-l);
            }
        }
    }

    Wide through(Int t) const {
        if (segments.empty() || t <= segments.front().left) return 0;
        if (t >= segments.back().right) return total;
        auto iter = std::upper_bound(segments.begin(), segments.end(), t,
                                    [](Int a, const Segment& b) { return a < b.left; });
        const auto& seg = *--iter;
        return seg.prefix + Wide(seg.weight) * (std::min(seg.right, t)-seg.left);
    }

    Wide arc_mass(I arc) const {
        if (arc.hi-arc.lo >= S) return total;
        Wide mass = 0;
        for (int turn = -1; turn <= 1; ++turn) {
            mass += through(arc.hi+turn*S)-through(arc.lo+turn*S);
        }
        return std::min(mass, total);
    }

};

extern "C" __declspec(dllexport) int get_masks(const Int* centers, Int rho, Int* out) {
    try {
        if (rho < R9 || rho >= S) return -2;
        for (int j = 0; j < 3; ++j) {
            auto mask = exposed_mask(centers, rho, j);
            if (mask.size() > 5) return -2;
            out[11*j] = Int(mask.size());
            for (int k = 0; k < int(mask.size()); ++k) {
                out[11*j+2*k+1] = mask[k].lo;
                out[11*j+2*k+2] = mask[k].hi;
            }
        }
        return 1;
    } catch (...) {
        return -2;
    }
}

extern "C" __declspec(dllexport) int get_extra_masks(const Int* centers, Int rho, Int* out) {
    try {
        if (rho<R9 || rho>=S) return -2;
        for (int i=0;i<int(test_radii.size());++i) {
            Int r=test_radius(i);
            auto mask=concentric_mask(centers,rho,r);
            if (mask.size()>5) return -2;
            out[12*i]=r;
            out[12*i+1]=Int(mask.size());
            for (int j=0;j<int(mask.size());++j) {
                out[12*i+2*j+2]=mask[j].lo;
                out[12*i+2*j+3]=mask[j].hi;
            }
        }
        return 1;
    } catch (...) {
        return -2;
    }
}

// Floating-point matrix for the optional search. Replay never calls it.
extern "C" __declspec(dllexport) void search_matrix(const double* samples, int n,
    const double* circles, const double* masks, int count, int bins, double r, double* result) {
    constexpr double two_pi=6.2831853071795864769;
    for (int row=0;row<n;++row) {
        for (int j=0;j<count;++j) {
            double x=samples[2*row]-circles[3*j], y=samples[2*row+1]-circles[3*j+1];
            double t=circles[3*j+2], d2=x*x+y*y, d=std::sqrt(d2);
            if (d>t+r || d<t-r) continue;
            double mid=0, half=.5;
            if (d>0 && d+t>r) {
                double c=(d2+t*t-r*r)/(2*d*t);
                if (c>=1) continue;
                half=std::acos(std::max(-1.,c))/two_pi;
                mid=std::atan2(y,x)/two_pi;
            }
            double* out=result+(row*count+j)*bins;
            for (int m=0;m<5;++m) {
                double a=masks[j*10+2*m], b=masks[j*10+2*m+1];
                if (b<=a) continue;
                for (int k=-1;k<=1;++k) {
                    double lo=std::max(a,mid-half+k), hi=std::min(b,mid+half+k);
                    if (hi<=lo) continue;
                    int first=std::clamp(int((lo+.5)*bins),0,bins-1);
                    int last=std::clamp(int((hi+.5)*bins),0,bins-1);
                    for (int i=first;i<=last;++i) {
                        out[i]+=std::max(0.,std::min(hi,(i+1.)/bins-.5)-std::max(lo,double(i)/bins-.5));
                    }
                }
            }
        }
    }
}

int verify_nine(const Int* centers, Int rho, const Int* weights, Int limit, Int* out, bool extra) {
    try {
        if (rho < R9 || rho >= S) return -2;
        std::vector<MaskedCurve> curves;
        curves.emplace_back(0, 0, S, std::vector<I>{{-S/2, S/2}}, weights);
        for (int k = 0; k < 3; ++k) {
            curves.emplace_back(centers[2*k], centers[2*k+1], rho,
                                exposed_mask(centers, rho, k), weights+K*(k+1));
        }
        if (extra) {
            for (int j=0;j<int(test_radii.size());++j) {
                Int r=test_radius(j);
                const Int* w=weights+K*(4+j);
                if (std::all_of(w,w+K,[](Int v){return v==0;})) continue;
                curves.emplace_back(0,0,r,concentric_mask(centers,rho,r),w);
            }
        }
        Wide total = 0;
        for (const auto& curve : curves) total += curve.total;
        if (total <= 0) return -2;
        // The axis-aligned outer box tree is deterministic. Origin-centered
        // test arcs in a box depend only on its path and on the test radius.
        // Cache their exact enclosures, never mass integrals or decisions.
        struct CachedArc {I arc{};bool ready=false;};
        struct WorkBox {Box b;int index;};
        constexpr int cache_size=1<<16;
        static thread_local std::vector<std::array<CachedArc,8>> cache(cache_size);
        std::vector<WorkBox> stack{{{{-S,S},{-S,S}},1}};
        Int checked = 0;
        while (!stack.empty()) {
            auto [b,index]=stack.back();
            stack.pop_back();
            if (++checked > limit) { out[2] = checked; return -1; }
            if (max_square(b.x)+max_square(b.y) < square(D9)) continue;
            if (min_square(b.x)+min_square(b.y) > square(S)) continue;
            Int mx = b.x.lo+(b.x.hi-b.x.lo)/2, my = b.y.lo+(b.y.hi-b.y.lo)/2;
            Int delta = root_up(square(b.x.hi-mx)+square(b.y.hi-my));
            Wide m = 0;
            for (const auto& curve : curves) {
                if (!curve.total) continue;
                I arc;
                if (curve.slot>=0 && index<cache_size) {
                    auto& entry=cache[index][curve.slot];
                    if (!entry.ready) {
                        entry.arc=upper_arc(mx,my,curve.rho,R9+delta);
                        entry.ready=true;
                    }
                    arc=entry.arc;
                } else arc=upper_arc(mx-curve.x,my-curve.y,curve.rho,R9+delta);
                m+=curve.arc_mass(arc);
                if (9*m>=total) break;
            }
            if (9*m < total) continue;
            if (delta <= S/500000) {
                out[0] = mx; out[1] = my; out[2] = checked;
                return 0;
            }
            int child=std::min(2*index,cache_size);
            if (b.x.hi-b.x.lo >= b.y.hi-b.y.lo) {
                stack.push_back({{{mx, b.x.hi}, b.y},child+1});
                stack.push_back({{{b.x.lo, mx}, b.y},child});
            } else {
                stack.push_back({{b.x, {my, b.y.hi}},child+1});
                stack.push_back({{b.x, {b.y.lo, my}},child});
            }
        }
        out[2] = checked;
        return 1;
    } catch (...) {
        return -2;
    }
}

extern "C" __declspec(dllexport) int check_nine(const Int* centers, Int rho,
                                                const Int* weights, Int limit, Int* out) {
    return verify_nine(centers,rho,weights,limit,out,false);
}

extern "C" __declspec(dllexport) int check_nine_extra(const Int* centers, Int rho,
                                                      const Int* weights, Int limit, Int* out) {
    return verify_nine(centers,rho,weights,limit,out,true);
}

extern "C" __declspec(dllexport) int check_nine_polar(const Int* centers, Int rho,
    const Int* weights, Int limit, Int* out, int extra) {
    try {
        if (rho<R9 || rho>=S) return -2;
        std::vector<MaskedCurve> curves;
        curves.emplace_back(0,0,S,std::vector<I>{{-S/2,S/2}},weights);
        for (int j=0;j<3;++j) curves.emplace_back(centers[2*j],centers[2*j+1],rho,
                                                exposed_mask(centers,rho,j),weights+K*(j+1));
        if (extra) for (int j=0;j<int(test_radii.size());++j) {
            const Int* w=weights+K*(4+j);
            if (std::all_of(w,w+K,[](Int v){return v==0;})) continue;
            Int t=test_radius(j);
            curves.emplace_back(0,0,t,concentric_mask(centers,rho,t),w);
        }
        Wide total=0;
        for (const auto& c:curves) total+=c.total;
        if (total<=0) return -2;
        struct Entry {I arc{};bool ready=false;};
        struct Polar {I d,a;int quadrant,index;};
        constexpr int cache_size=1<<16;
        static thread_local std::vector<std::array<Entry,8>> cache(cache_size);
        std::vector<Polar> stack;
        for (int j=0;j<4;++j) stack.push_back({{D9,S},{0,S},j,4+j});
        Int checked=0;
        while (!stack.empty()) {
            auto b=stack.back();stack.pop_back();
            if (++checked>limit) {out[2]=checked;return -1;}
            Int hm=b.d.lo+(b.d.hi-b.d.lo)/2, am=b.a.lo+(b.a.hi-b.a.lo)/2;
            I a=point(am), d=point(hm), p=square(a), q=one+p;
            I cx=d*(one-p)/q, cy=2*(d*a)/q;
            for (int rot=0;rot<b.quadrant;++rot) {I tmp=-cy;cy=cx;cx=tmp;}
            Int x=cx.lo+(cx.hi-cx.lo)/2, y=cy.lo+(cy.hi-cy.lo)/2;
            I chord=2*point(b.a.hi-am)/sqrt((one+square(point(b.a.lo)))*q);
            I delta=sqrt(square(point(b.d.hi-hm))+point(b.d.hi)*d*square(chord));
            Int inflate=delta.hi+(cx.hi-x)+(cy.hi-y);
            Wide mass=0;
            for (const auto& curve:curves) {
                if (!curve.total) continue;
                I arc;
                if (curve.slot>=0) {
                    auto calculate=[&] {
                        I t=point(curve.rho), k=square(t)-square(point(R9));
                        I cosine;
                        if (k.lo>0) {
                            I crit=sqrt(k);
                            if (b.d.lo>crit.hi) cosine=(point(b.d.lo)+k/point(b.d.lo))/(2*t);
                            else if (b.d.hi<crit.lo) cosine=(point(b.d.hi)+k/point(b.d.hi))/(2*t);
                            else cosine=crit/t;
                        } else if (k.hi<=0) cosine=(point(b.d.lo)+k/point(b.d.lo))/(2*t);
                        else cosine=(b.d+k/b.d)/(2*t);
                        if (cosine.lo>=S) return zero;
                        Int half=(acos_at(cosine.lo)/tau).hi;
                        Int offset=(b.quadrant<2?b.quadrant:b.quadrant-4)*(S/4);
                        I left=atan_ratio(b.a.lo,S)/pi, right=atan_ratio(b.a.hi,S)/pi;
                        return I{left.lo+offset-half,right.hi+offset+half};
                    };
                    if (b.index<cache_size) {
                        auto& e=cache[b.index][curve.slot];
                        if (!e.ready) {e.arc=calculate();e.ready=true;}
                        arc=e.arc;
                    } else arc=calculate();
                } else arc=upper_arc(x-curve.x,y-curve.y,curve.rho,R9+inflate);
                mass+=curve.arc_mass(arc);
                if (9*mass>=total) break;
            }
            if (9*mass<total) continue;
            if (inflate<=S/500000) {out[0]=x;out[1]=y;out[2]=checked;return 0;}
            int child=std::min(2*b.index,cache_size);
            if (b.d.hi-b.d.lo>=2*(b.a.hi-b.a.lo)) {
                stack.push_back({{hm,b.d.hi},b.a,b.quadrant,child+1});
                stack.push_back({{b.d.lo,hm},b.a,b.quadrant,child});
            } else {
                stack.push_back({b.d,{am,b.a.hi},b.quadrant,child+1});
                stack.push_back({b.d,{b.a.lo,am},b.quadrant,child});
            }
        }
        out[2]=checked;
        return 1;
    } catch (...) {
        return -2;
    }
}

struct Witness { Int x, y, cost; I shadow; };

constexpr std::array<int, 30> witness_radii{
    312, 316, 320, 324, 328, 332, 336, 340, 344, 348,
    352, 356, 360, 364, 368, 372, 376, 380, 384, 388,
    392, 396, 400, 404, 408, 412, 416, 420, 425, 430};

I boundary_cap(I d, I radius) {
    I c = (one + d*d - radius*radius)/(2*d);
    return {acos_at(c.hi).lo, acos_at(c.lo).hi};
}

Int maximum_cap() {
    return acos_at(sqrt(one-point(R9)*point(R9)).lo).hi;
}

const auto& witnesses() {
    static auto data = [] {
        constexpr int N = 20;
        std::array<std::array<Witness, witness_radii.size()>, 4*N> result{};
        for (int k = 0; k < 4; ++k) {
            for (int j = 0; j < N; ++j) {
                Int x = N*N-j*j, y = 2*N*j, den = 1000*(N*N+j*j);
                for (int rot = 0; rot < k; ++rot) {
                    Int new_x = -y;
                    y = x;
                    x = new_x;
                }
                for (int i = 0; i < int(witness_radii.size()); ++i) {
                    Int rho = witness_radii[i];
                    Int vx = div_down(Wide(S)*rho*x, den);
                    Int vy = div_down(Wide(S)*rho*y, den);
                    I t = norm(vx, vy), d = point(D9), r = point(R9);
                    I c = (t*t+d*d-r*r)/(2*(t*d));
                    Int half = (acos_at(c.lo)/tau).hi;
                    I mid = arg_turn(vx, vy);
                    Int cap = boundary_cap(point(t.hi+R9), r).hi;
                    result[N*k+j][i] = {vx, vy, std::max<Int>(0, maximum_cap()-cap),
                                         {mid.lo-half, mid.hi+half}};
                }
            }
        }
        return result;
    }();
    return data;
}

int witnesses_with_matching(const Int* centers, Int rho, Int pair_loss) {
    try {
        if (rho < R9 || rho >= S) return -2;
        Int allowance = 9*maximum_cap()-pi.lo;
        std::vector<Witness> chosen;
        for (const auto& ray : witnesses()) {
            for (const auto& w : ray) {
                bool outside = true;
                for (int i = 0; i < 3; ++i) {
                    if (square(w.x-centers[2*i])+square(w.y-centers[2*i+1]) <= square(rho)) {
                        outside = false;
                        break;
                    }
                }
                if (outside) {
                    if (w.cost > allowance) return 1;
                    chosen.push_back(w);
                    break;
                }
            }
        }
        if (8*pair_loss>allowance) return 1;
        using WeightedArc = std::pair<I, Int>;
        std::vector<WeightedArc> arcs;
        std::vector<std::array<Int,9>> score;
        for (const auto& anchor : chosen) {
            arcs.clear();
            for (const auto& w : chosen) {
                I a = w.shadow;
                while (a.lo <= anchor.shadow.hi) a = a+point(S);
                while (a.lo > anchor.shadow.hi+S) a = a-point(S);
                if (a.hi < anchor.shadow.lo+S) arcs.push_back({a, w.cost});
            }
            std::sort(arcs.begin(), arcs.end(), [](auto a, auto b) { return a.first.hi < b.first.hi; });
            score.clear();
            score.push_back({anchor.cost,-S,-S,-S,-S,-S,-S,-S,-S});
            if (anchor.cost+8*pair_loss>allowance) return 1;
            for (const auto& [arc, cost] : arcs) {
                auto iter = std::lower_bound(arcs.begin(), arcs.end(), arc.lo,
                                             [](auto a, Int p) { return a.first.hi < p; });
                auto best=score.back();
                const auto& prior=score[iter-arcs.begin()];
                for (int k=1;k<9;++k) {
                    if (prior[k-1]<0) continue;
                    best[k]=std::max(best[k],prior[k-1]+cost);
                    int matching=std::max(0,4-k);
                    if (best[k]+2*matching*pair_loss>allowance) return 1;
                }
                if (prior[8]>=0) return 1;  // Ten different outer disks required.
                score.push_back(best);
            }
        }
        return 0;
    } catch (...) {
        return -2;
    }
}

extern "C" __declspec(dllexport) int witness_obstruction(const Int* centers, Int rho) {
    return witnesses_with_matching(centers,rho,0);
}

extern "C" __declspec(dllexport) int matching_obstruction(const Int* centers, Int rho, Int max_s) {
    try {
        I r=point(R9), t=r+point(max_s);
        Int loss=0;
        if (t.lo>R9 && t.hi<(one-2*square(r)).lo) {
            I cosine=(one+t)/(2*sqrt(t+square(r)));
            loss=std::max<Int>(0,maximum_cap()-acos_at(cosine.lo).hi);
        }
        if (!loss) return 0;
        return witnesses_with_matching(centers,rho,loss);
    } catch (...) {
        return -2;
    }
}

struct V {
    I x, y;
    V operator+(V b) const { return {x+b.x,y+b.y}; }
    V operator-(V b) const { return {x-b.x,y-b.y}; }
    V operator/(Int d) const { return {x/d,y/d}; }
    V operator*(I q) const { return {x*q,y*q}; }
    V clockwise() const { return {y,-x}; }
};

I dot(V a,V b) { return a.x*b.x+a.y*b.y; }
I cross(V a,V b) { return a.x*b.y-a.y*b.x; }
I norm_square(V a) { return square(a.x)+square(a.y); }
I norm(V a) { return sqrt(norm_square(a)); }

I acos(I c);
I acos_derivative(I c);
Int asin_upper(I x);

I midpoint(I v) {return point(v.lo+(v.hi-v.lo)/2);}
V midpoint(V v) {return {midpoint(v.x),midpoint(v.y)};}

I intersect(I a,I b) {
    I out{std::max(a.lo,b.lo),std::min(a.hi,b.hi)};
    if (out.lo>out.hi) throw std::logic_error("inconsistent enclosure");
    return out;
}

I bearing(V a) {
    V m=midpoint(a);
    Int delta=norm(a-m).hi;
    Int d=norm(m).lo;
    if (delta>=d) return {-S,S};
    Int widen=(point(asin_upper(point(delta)/point(d)))/tau).hi;
    return arg_turn(m.x.lo,m.y.lo)+I{-widen,widen};
}

Int angle_lower(V a, V b) {
    I diff=bearing(a)-bearing(b);
    Int best=S;
    for (int k=-2;k<=2;++k) {
        I d=diff-point(k*S);
        best=std::min(best,std::max<Int>(0,std::max(d.lo,-d.hi)));
    }
    return (point(best)*tau).lo;
}

Int angle_upper(V a,V b) {
    I diff=bearing(a)-bearing(b);
    Int best=S/2;
    for (int k=-2;k<=2;++k) {
        I d=diff-point(k*S);
        best=std::min(best,std::max(std::abs(d.lo),std::abs(d.hi)));
    }
    return (point(best)*tau).hi;
}

struct TipEnclosure {
    V value,center;
    I radius;
    std::array<V,5> local;
};

TipEnclosure tight_tip(V a,V b,I rad) {
    V e=b-a;
    I ell2=norm_square(e);
    I h2=square(rad)-ell2/4;
    if (h2.lo<=0 || ell2.lo<=0) throw std::logic_error("no certified outward intersection");
    I ell=sqrt(ell2), h=sqrt(h2);
    V n=e.clockwise();
    V tip=(a+b)/2+n*(h/ell);
    V a0=midpoint(a), b0=midpoint(b), e0=b0-a0;
    I r0=midpoint(rad), q0=norm_square(e0);
    V tip0=(a0+b0)/2+e0.clockwise()*(sqrt(square(r0)-q0/4)/sqrt(q0));
    I k=one/(4*(h*ell))+h/(ell2*ell), g=h/ell;
    I m00=-k*n.x*e.x, m01=g-k*n.x*e.y, m10=-g-k*n.y*e.x, m11=-k*n.y*e.y;
    I half=one/2;
    V da=a-a0, db=b-b0;
    I dr=rad-r0;
    V ax{half-m00,-m10}, ay{-m01,half-m11};
    V bx{half+m00,m10}, by{m01,half+m11};
    V rr=n*(rad/(h*ell));
    V tight=tip0+ax*da.x+ay*da.y+bx*db.x+by*db.y+rr*dr;
    tip={intersect(tip.x,tight.x),intersect(tip.y,tight.y)};
    I t=norm(tip);
    if (t.lo<=0) return {tip,tip0,t,{ax,ay,bx,by,rr}};
    I tt=norm(tip0)+(dot(tip,ax)*da.x+dot(tip,ay)*da.y+dot(tip,bx)*db.x+
                   dot(tip,by)*db.y+dot(tip,rr)*dr)/t;
    return {tip,tip0,intersect(t,tt),{ax,ay,bx,by,rr}};
}

struct VJet {
    V value,center;
    std::array<V,6> partial{};
};

I angle_enclosure(const VJet& a,const VJet& b,const std::array<I,6>& delta) {
    I crude{angle_lower(a.value,b.value),angle_upper(a.value,b.value)};
    I da=norm_square(a.value),db=norm_square(b.value);
    if (da.lo<=0 || db.lo<=0) return crude;
    I center=(bearing(b.center)-bearing(a.center))*tau;
    if (center.hi<0) center=center+tau;
    if (center.lo<=0 || center.hi>=pi.lo) return crude;
    I bound=center;
    for (int j=0;j<6;++j) {
        I diff=cross(b.value,b.partial[j])/db-cross(a.value,a.partial[j])/da;
        bound=bound+diff*delta[j];
    }
    return intersect(crude,bound);
}

Int lower_radius_for_cap(Int required) {
    Int lo=D9, hi=sqrt(one-square(point(R9))).lo;
    while (hi-lo > S/65536) {
        Int mid = (lo+hi)/2;
        if (boundary_cap(point(mid),point(R9)).hi < required) lo = mid;
        else hi = mid;
    }
    return lo;
}

Int asin_upper(I x) {
    return acos_at(sqrt(positive(one-square(x))).lo).hi;
}

Int reach_bound(Int dmin, Int tmax, Int fallback) {
    I d=point(dmin), r=point(R9), t=point(tmax);
    if (tmax<=R9 || dmin>=tmax+R9 || (square(d)-square(r)-square(t)).lo<=0) return fallback;
    auto jet=[&](Int x,I& v,I& slope) {
        I q=point(x), q2=square(q);
        I c=(one+q2-square(r))/(2*q);
        I z=(square(t)+q2-square(r))/(2*(q*t));
        if (c.hi>=S || z.hi>=S) return false;
        v=acos(c)+acos(z);
        slope=acos_derivative(c)*(q2-one+square(r))/(2*q2)+
              acos_derivative(z)*(q2-square(t)+square(r))/(2*(t*q2));
        return true;
    };
    I v,slope;
    if (!jet(dmin,v,slope)) return fallback;
    if (slope.hi<=0) return std::min(fallback,v.hi);
    Int lo=dmin,hi=tmax+R9;
    Int cap=std::min(fallback,(v+slope*I{0,hi-lo}).hi);
    for (int n=0;n<7;++n) {
        Int mid=lo+(hi-lo)/2;
        if (mid==lo || !jet(mid,v,slope)) break;
        cap=std::min(cap,(v+slope*I{lo-mid,hi-mid}).hi);
        if (slope.lo>0) lo=mid;
        else if (slope.hi<0) hi=mid;
        else break;
    }
    return cap;
}

Int high_cap(I a);

// 1 certifies the three-pair reduction throughout the inner box; 2 means
// the unit boundary budget alone rules it out. 0 makes no claim.
int nine_shape_impl(const Int* bounds,bool correlate,bool general_counts) {
    try {
        I rad{R9-1,R9};
        I r = point(R9);
        Int peak = maximum_cap();
        V inner[]{{{bounds[0],bounds[1]},zero},
                  {{bounds[2],bounds[3]},{bounds[4],bounds[5]}},
                  {{bounds[6],bounds[7]},{bounds[8],bounds[9]}}};
        V tip[3];
        I length[3];
        constexpr int x_index[]={0,1,3},y_index[]={-1,2,4};
        std::array<I,6> delta{};
        for (int k=0;k<5;++k) {
            I b{bounds[2*k],bounds[2*k+1]};
            delta[k]=b-midpoint(b);
        }
        delta[5]=rad-midpoint(rad);
        VJet ij[3],tj[3];
        for (int j=0;j<3;++j) {
            ij[j].value=inner[j];ij[j].center=midpoint(inner[j]);
            ij[j].partial[x_index[j]]={one,zero};
            if (y_index[j]>=0) ij[j].partial[y_index[j]]={zero,one};
        }
        Int cap[3], shift[3], reach[3], low[3];
        I beta_mid[3];
        std::array<I,6> beta_gradient[3]{};
        bool beta_smooth[3]{};
        for (int j=0;j<3;++j) {
            int k=(j+1)%3;
            V a=inner[j], b=inner[k];
            if (cross(a,b).lo <= 0) return 0;
            auto p=tight_tip(a,b,rad);
            tip[j]=p.value;
            tj[j].value=p.value;tj[j].center=p.center;
            tj[j].partial[x_index[j]]=p.local[0];
            if (y_index[j]>=0) tj[j].partial[y_index[j]]=p.local[1];
            tj[j].partial[x_index[k]]=p.local[2];
            if (y_index[k]>=0) tj[j].partial[y_index[k]]=p.local[3];
            tj[j].partial[5]=p.local[4];
            if (cross(a,tip[j]).lo<=0 || cross(tip[j],b).lo<=0) return 0;
            length[j]=p.radius;
            if (length[j].hi >= S || length[j].lo <= 0) return 0;
            if (norm_square(tip[j]-inner[(j+2)%3]).lo <= square(rad).hi) return 0;
            if (length[j].hi+R9 < D9) return 2;
            Int end=length[j].hi+R9;
            cap[j]=end < sqrt(one-square(r)).lo ? boundary_cap(point(end),r).hi : peak;
            if (correlate && end<sqrt(one-square(r)).lo && R9+length[j].lo>S-R9) {
                I d=r+length[j],d2=square(d);
                I co=(one+d2-square(r))/(2*d);
                if (co.hi<S && co.lo>-S) {
                    I slope=acos_derivative(co)*(d2-one+square(r))/(2*d2);
                    beta_mid[j]=boundary_cap(r+norm(p.center),r);
                    for (int m=0;m<6;++m) {
                        beta_gradient[j][m]=slope*dot(tip[j],tj[j].partial[m])/length[j];
                    }
                    beta_smooth[j]=true;
                }
            }
        }
        for (int j=0;j<3;++j) {
            V a=tip[j], b=tip[(j+1)%3];
            I h2=square(r)-norm_square(a-b)/4;
            if (h2.hi>=0 && (norm((a+b)/2)+sqrt(positive(h2))).hi >= D9) return 0;
        }
        auto total_cap=[&](int skip) {
            Int crude=0;
            I mid=zero;
            bool smooth=true;
            std::array<I,6> gradient{};
            for (int j=0;j<3;++j) {
                if (j==skip) continue;
                crude+=cap[j];
                if (!beta_smooth[j]) {smooth=false;continue;}
                mid=mid+beta_mid[j];
                for (int k=0;k<6;++k) gradient[k]=gradient[k]+beta_gradient[j][k];
            }
            if (!smooth) return crude;
            for (int k=0;k<6;++k) mid=mid+gradient[k]*delta[k];
            return std::min(crude,mid.hi);
        };
        Int sum=total_cap(-1);
        Int allowance=6*peak+sum-pi.lo;
        if (allowance < 0) return 2;
        for (int j=0;j<3;++j) {
            Int lower=lower_radius_for_cap(pi.lo-6*peak-total_cap(j));
            low[j]=lower;
            if (length[j].hi >= lower) return 0;
            I d=point(lower), t=length[j];
            I c=(square(d)+square(t)-square(r))/(2*(d*t));
            shift[j]=acos_at(c.lo).hi;
            reach[j]=reach_bound(lower,t.hi,shift[j]+cap[j]);
        }
        bool counts[3][7]{};
        for (int j=0;j<3;++j) {
            int k=(j+1)%3;
            if (cross(tip[j],tip[k]).lo <= 0) return 0;
            Int bound=reach[j]+reach[k];
            Int tm=std::max(length[j].hi,length[k].hi);
            if ((square(point(std::min(low[j],low[k])))-square(r)-square(point(tm))).lo>0) {
                Int avg=lower_radius_for_cap(div_down(pi.lo-6*peak-cap[(j+2)%3],2));
                bound=std::min(bound,2*reach_bound(avg,tm,bound));
            }
            I angle=correlate ? angle_enclosure(tj[j],tj[k],delta) :
                                 I{angle_lower(tip[j],tip[k]),angle_upper(tip[j],tip[k])};
            Int angle_lo=angle.lo;
            if (angle_lo<=std::min(bound,shift[j]+shift[k])) return 0;
            Int angle_hi=angle.hi;
            for (int n=0;n<=6;++n) {
                counts[j][n]=angle_lo<=bound+2*n*peak &&
                             angle_hi>=2*pi.lo-bound-2*cap[(j+2)%3]-2*(6-n)*peak;
            }
        }
        Int high=lower_radius_for_cap(peak-allowance);
        Int gap=std::max<Int>(0,2*pi.lo-10*peak-2*sum);
        Int gamma=asin_upper(r/point(high));
        Int extra=std::min(2*peak+std::max<Int>(0,2*gamma-gap),peak+gamma);
        auto pair_local=[&](int j,int n,int pair) {
            if (!j) return true;
            int prev=(j+2)%3, next=(j+1)%3;
            I s=norm(inner[j]);
            Int threshold=std::max(high-R9,R9-1+s.lo);
            if (threshold<=R9) return false;
            Int inner_shadow=asin_upper(r/point(threshold));
            Int left=correlate?angle_enclosure(tj[prev],ij[j],delta).lo:angle_lower(tip[prev],inner[j]);
            Int right=correlate?angle_enclosure(ij[j],tj[j],delta).lo:angle_lower(inner[j],tip[j]);
            Int b=std::max<Int>(0, extra+std::max(
                reach[prev]-left+2*pair*peak,reach[j]-right+2*(n-pair-2)*peak));
            for (int k : {prev,next}) {
                if (norm(inner[k]).hi<=s.lo) continue;
                if (angle_lower(inner[j],inner[k])<=b+inner_shadow) return false;
            }
            return true;
        };
        if (!general_counts) {
            bool any=false;
            for (int a=0;a<=6;++a) for (int b=0;b<=6-a;++b) {
                int c=6-a-b;
                if (!counts[0][a] || !counts[1][b] || !counts[2][c]) continue;
                if (a!=2 || b!=2 || c!=2) return 0;
                any=true;
            }
            if (!any) return 2;
            return pair_local(1,2,0) && pair_local(2,2,0) ? 1 : 0;
        }

        Int biggest=high_cap(inner[0].x);
        Int upper[3][7];
        bool sharp=pair_local(1,2,0) && pair_local(2,2,0);
        for (int j=0;j<3;++j) {
            int before=(j+2)%3;
            Int local=high_cap(norm(inner[j]));
            for (int n=0;n<=6;++n) {
                if (!counts[before][n]) continue;
                Int dp[7]{0,peak};
                for (int z=2;z<=n;++z) {
                    Int cap_pair=pair_local(j,n,z-2)?local:biggest;
                    dp[z]=std::min(dp[z-1]+peak,dp[z-2]+2*cap_pair);
                }
                upper[j][n]=dp[n];
            }
        }
        bool use_sharp=false;
        for (int a=0;a<=6;++a) for (int b=0;b<=6-a;++b) {
            int c=6-a-b;
            if (!counts[0][a] || !counts[1][b] || !counts[2][c]) continue;
            if (sum+upper[0][c]+upper[1][a]+upper[2][b]<pi.lo) continue;
            if (a!=2 || b!=2 || c!=2 || !sharp) return 0;
            use_sharp=true;
        }
        return use_sharp ? 1 : 2;
    } catch (...) {
        return 0;
    }
}

extern "C" __declspec(dllexport) int nine_shape(const Int* bounds) {
    int simple=nine_shape_impl(bounds,false,false);
    return simple ? simple : nine_shape_impl(bounds,true,true);
}

constexpr I rstar{R9-1,R9};
constexpr I slope{-151041251349,-151041251348};
constexpr I local_a{305113000000,306763000000};
constexpr I local_c{-551955000000,-547557000000};

I acos(I c) { return {acos_at(c.hi).lo, acos_at(c.lo).hi}; }
I acos_derivative(I c) { return -one/sqrt(one-square(c)); }

Int high_cap(I a) {
    I rr = point(R9);
    I max_t=one-2*square(rr);
    I t=rr+point(a.hi);
    if (t.hi >= max_t.lo) return maximum_cap();
    return acos((one+t)/(2*sqrt(t+square(rr)))).hi;
}

struct Triple { I a,b,c; };

// Bounds f minus its tangent. ell=0 is relaxed using |T| <= r+min(a,b).
// Boxes with no pairwise intersection or no potential low disk are excluded.
I tangent_upper(Triple box) {
    auto [a,b,c]=box;
    I theta=acos(c);
    I linear=pi/3+slope*(theta-2*pi/3);
    Int peak=maximum_cap();
    I cheap=I{0,high_cap(a)+high_cap(b)+peak}-linear;
    if (cheap.hi<0) return cheap;
    I ab=a*b;
    I ell2=square(a-b)+2*(ab*(one-c));
    I h2=square(rstar)-ell2/4;
    if (h2.hi<0) return point(-S);
    Int d=2*R9+std::min(a.hi,b.hi);
    if (ell2.lo>S/1048576) {
        I z=square(rstar)+ab*c+2*(sqrt(positive(h2))*ab*sqrt(positive(one-square(c)))/sqrt(ell2));
        d=std::min(d,R9+sqrt(positive(z)).hi);
    }
    if (d<D9) return point(-S);
    Int lo_cap = d<sqrt(one-square(point(R9))).lo ? boundary_cap(point(d),point(R9)).hi : peak;
    return I{0,high_cap(a)+high_cap(b)+lo_cap}-linear;
}

// Value and two directional derivatives. The derivative direction can be
// a coordinate, or a sum of two coordinates for recovering the Hessian.
struct J {
    I v, p, q;
    J(I x, I p=zero, I q=zero) : v(x),p(p),q(q) {}
};
J operator+(J a,J b) { return {a.v+b.v,a.p+b.p,a.q+b.q}; }
J operator-(J a,J b) { return {a.v-b.v,a.p-b.p,a.q-b.q}; }
J operator*(J a,J b) {
    return {a.v*b.v,a.p*b.v+a.v*b.p,a.q*b.v+2*(a.p*b.p)+a.v*b.q};
}
J operator*(Int a,J b) { return {a*b.v,a*b.p,a*b.q}; }
J operator/(J a,Int b) { return {a.v/b,a.p/b,a.q/b}; }
J operator/(J a,J b) {
    if (b.v.lo <= S/256) throw std::logic_error("small jet divisor");
    I v=a.v/b.v;
    I p=(a.p-v*b.p)/b.v;
    return {v,p,(a.q-2*(p*b.p)-v*b.q)/b.v};
}
J sqrt(J a) {
    if (a.v.lo <= S/65536) throw std::logic_error("small jet radicand");
    I v=sqrt(a.v), p=a.p/(2*v);
    return {v,p,(a.q-2*square(p))/(2*v)};
}
J acos(J c) {
    I z=one-square(c.v);
    if (z.lo<=S/65536) throw std::logic_error("small acos radicand");
    I d=-one/sqrt(z);
    return {acos(c.v),d*c.p,d*(c.q+c.v*square(c.p)/z)};
}

J jet_function(J a,J b,J c) {
    J r=rstar;
    J ab=a*b;
    J ell=sqrt((a-b)*(a-b)+2*(ab*(J(one)-c)));
    J h=sqrt(r*r-ell*ell/4);
    J d=r+sqrt(r*r+ab*c+2*(h*ab*sqrt(J(one)-c*c)/ell));
    if (d.v.hi>=sqrt(one-square(rstar)).lo) throw std::logic_error("low cap saturated");
    J beta=acos((J(one)+d*d-r*r)/(2*d));
    auto high=[&](J a) {
        J t=r+a;
        if (t.v.hi>=(one-2*square(rstar)).lo) throw std::logic_error("high cap saturated");
        return acos((J(one)+t)/(2*sqrt(t+r*r)));
    };
    return high(a)+high(b)+beta;
}

I mean_value_upper(Triple box) {
    auto [a,b,c]=box;
    if (a.lo < S/6 || b.lo < S/6 || a.hi>S*3/8 || b.hi>S*3/8 ||
        c.lo<-S*15/16 || c.hi>-S/64 || a.hi-a.lo>S/24 || b.hi-b.lo>S/24 || c.hi-c.lo>S/12) {
        return one;
    }
    try {
        I pa=jet_function(J(a,one),J(b),J(c)).p;
        I pb=jet_function(J(a),J(b,one),J(c)).p;
        I pc=jet_function(J(a),J(b),J(c,one)).p-slope*acos_derivative(c);
        auto mid=[](I x) {return point(x.lo+(x.hi-x.lo)/2);};
        Triple m{mid(a),mid(b),mid(c)};
        I at_mid=jet_function(J(m.a),J(m.b),J(m.c)).v-(pi/3+slope*(acos(m.c)-2*pi/3));
        return at_mid+pa*(a-m.a)+pb*(b-m.b)+pc*(c-m.c);
    } catch (...) {
        return one;
    }
}

bool negative_hessian(Triple box) {
    try {
        auto [a,b,c]=box;
        I sine=sqrt(one-square(c));
        auto second=[&](int i,int j,int k) {
            return jet_function(J(a,i*one),J(b,j*one),J(c,-k*sine,-k*k*c)).q;
        };
        I aa=second(1,0,0), bb=second(0,1,0), cc=second(0,0,1);
        I ab=(second(1,1,0)-aa-bb)/2;
        I ac=(second(1,0,1)-aa-cc)/2;
        I bc=(second(0,1,1)-bb-cc)/2;
        I m=aa*bb-square(ab);
        I d=aa*(bb*cc-square(bc))-ab*(ab*cc-ac*bc)+ac*(ab*bc-bb*ac);
        return aa.hi<0 && m.lo>0 && d.hi<0;
    } catch (...) {
        return false;
    }
}

bool in(I a,I b) {return b.lo<=a.lo && a.hi<=b.hi;}

std::pair<Triple,Triple> split_triple(Triple t) {
    Triple left=t, right=t;
    I Triple::* member=&Triple::a;
    Int width=t.a.hi-t.a.lo;
    if (t.b.hi-t.b.lo>width) { member=&Triple::b; width=t.b.hi-t.b.lo; }
    if ((t.c.hi-t.c.lo)/3>width) member=&Triple::c;
    I q=t.*member;
    Int m=q.lo+(q.hi-q.lo)/2;
    if (m==q.lo) throw std::logic_error("cannot split");
    (left.*member).hi=m;
    (right.*member).lo=m;
    return {left,right};
}

extern "C" __declspec(dllexport) int check_tangent(Int limit,Int* out) {
    try {
        std::vector<Triple> work{{local_a,local_a,local_c}};
        Int local=0, checked=0;
        while (!work.empty()) {
            auto box=work.back();work.pop_back();
            if (++checked>limit) {out[0]=local;return -1;}
            if (negative_hessian(box)) {++local;continue;}
            auto [p,q]=split_triple(box);
            work.push_back(p);work.push_back(q);
        }
        Int outside=0, inside=0;
        work.push_back({{0,S-R9+1},{0,S-R9+1},{-S,S}});
        while (!work.empty()) {
            auto box=work.back();work.pop_back();
            if (++checked>limit) {out[0]=local;out[1]=outside;out[2]=inside;return -1;}
            if (box.a.lo>box.b.hi) continue;
            if (in(box.a,local_a) && in(box.b,local_a) && in(box.c,local_c)) {++inside;continue;}
            if (tangent_upper(box).hi<0 || mean_value_upper(box).hi<0) {++outside;continue;}
            auto [p,q]=split_triple(box);
            work.push_back(p);work.push_back(q);
        }
        out[0]=local;out[1]=outside;out[2]=inside;
        return 1;
    } catch (...) {
        return -2;
    }
}
