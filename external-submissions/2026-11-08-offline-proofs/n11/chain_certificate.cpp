// Exact interval reachability for a chain adjacent to one interior disk.
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <string_view>
#include <utility>
#include <vector>

using Int = std::int64_t;
using Wide = __int128_t;
constexpr Int S = Int(1) << 40;

Int floor_div(Wide a, Wide b) {
    assert(b > 0);
    return static_cast<Int>(a / b - (a % b < 0));
}

Int ceil_div(Wide a, Wide b) { return -floor_div(-a, b); }

struct Interval { Int lo, hi; };

Interval frac(Int a, Int b = 1) {
    return {floor_div(Wide(a)*S, b), ceil_div(Wide(a)*S, b)};
}

Interval operator+(Interval a, Interval b) { return {a.lo+b.lo, a.hi+b.hi}; }
Interval operator-(Interval a, Interval b) { return {a.lo-b.hi, a.hi-b.lo}; }

Interval operator*(Interval a, Interval b) {
    Wide ab[] = {Wide(a.lo)*b.lo, Wide(a.lo)*b.hi, Wide(a.hi)*b.lo, Wide(a.hi)*b.hi};
    return {floor_div(*std::min_element(ab, ab+4), S), ceil_div(*std::max_element(ab, ab+4), S)};
}

Interval operator/(Interval a, Interval b) {
    assert(b.lo > 0);
    return a * Interval{floor_div(Wide(S)*S, b.hi), ceil_div(Wide(S)*S, b.lo)};
}

Interval sq(Interval a) {
    Wide x = Wide(a.lo)*a.lo, y = Wide(a.hi)*a.hi;
    Wide lo = a.lo <= 0 && a.hi >= 0 ? 0 : std::min(x, y);
    return {floor_div(lo, S), ceil_div(std::max(x, y), S)};
}

Int isqrt(Wide n) {
    // Binary integer square root for this certificate's fixed scale.
    Int lo = 0, hi = 16*S;
    assert(Wide(hi)*hi > n);
    while (lo+1 < hi) {
        Int mid = (lo+hi)/2;
        if (Wide(mid)*mid <= n) lo = mid;
        else hi = mid;
    }
    return lo;
}

Interval root(Interval a) {
    assert(a.lo >= 0);
    Int lo = isqrt(Wide(a.lo)*S), hi = isqrt(Wide(a.hi)*S);
    return {lo, hi + (Wide(hi)*hi < Wide(a.hi)*S)};
}

Interval clamp_unit(Interval a) { return {std::max(-S, a.lo), std::min(S, a.hi)}; }

Interval trig(Interval angle, int sine) {
    Int mid = (angle.lo+angle.hi)/2;
    Interval x{mid, mid};
    assert(x.lo > -10*S && x.hi < 10*S);
    Interval x2 = sq(x);
    Interval term = sine ? x : frac(1);
    Interval sum = term;
    for (int k = 1; k <= 23; ++k) {
        term = frac(-1) * term * x2 / frac((2*k+sine)*(2*k+sine-1));
        sum = sum + term;
    }
    // Taylor remainder < 10^47 / 47!, and sine and cosine are 1-Lipschitz.
    Int err = frac(1, 1000000000).hi + std::max(mid-angle.lo, angle.hi-mid);
    return clamp_unit({sum.lo-err, sum.hi+err});
}

Interval atan_small(Interval x) {
    assert(x.lo >= -S/2 && x.hi <= S/2);
    Interval y = sq(x);
    Interval sum = frac(0);
    for (int k = 11; k >= 0; --k) sum = frac(k%2 ? -1 : 1, 2*k+1) + y*sum;
    Interval value = x*sum;
    Int err = frac(1, 25*(Int(1) << 25)).hi;
    return {value.lo-err, value.hi+err};
}

Interval arc_at(Int cosine) {
    cosine = std::clamp(cosine, Int(0), S);
    Interval c{cosine, cosine};
    Interval z = (frac(1)-c)*frac(1, 2);
    Interval x = root(z);
    static const auto a = [] {
        std::vector<Interval> c(12);
        c[0] = frac(1);
        for (int k = 0; k < 11; ++k)
            c[k+1] = c[k]*frac((2*k+1)*(2*k+1), 2*(k+1)*(2*k+3));
        return c;
    }();
    Interval sum = frac(0);
    for (int k = 11; k >= 0; --k) sum = a[k]+z*sum;
    Interval z4 = sq(sq(z));
    Interval tail = frac(2)*x*sq(z4)*z4;
    Interval main = frac(2)*x*sum;
    return {main.lo, main.hi+2*tail.hi};
}

struct AngularCell { Interval theta, sine, cosine; };
struct RadialCell { Interval rho, alpha; };
struct Node {
    int left, right, inner_left, inner_right, start;
    int chord_end_min, chord_start_max, left_max;
    bool ordinary;
};
constexpr int INF = 100000000;
constexpr int TICKS = 20000, OFFSET = 140000, LIMIT = 400000;

int down(Int angle) { return int(floor_div(Wide(angle)*TICKS, S)) + OFFSET; }
int up(Int angle) { return int(ceil_div(Wide(angle)*TICKS, S)) + OFFSET; }

const Interval pi{frac(31415926535LL, 10000000000LL).lo,
                  frac(31415926536LL, 10000000000LL).hi};
constexpr int TABLE = 1 << 16;

Interval atan_unit(Int numerator, Int denominator) {
    assert(numerator >= 0 && numerator <= denominator && denominator > 0);
    static const auto table = [] {
        std::vector<Interval> values(TABLE+1);
        for (int j = 0; j <= TABLE; ++j) {
            Interval x = frac(j, TABLE);
            values[j] = 2*j <= TABLE ? atan_small(x)
                : pi/frac(4) + atan_small((x-frac(1))/(x+frac(1)));
        }
        return values;
    }();
    Int index_low = floor_div(Wide(numerator)*TABLE, denominator);
    Int index_high = ceil_div(Wide(numerator)*TABLE, denominator);
    return {table[index_low].lo, table[index_high].hi};
}

Interval arg(Int dx, Int dy) {
    assert(dx >= 0);
    if (dy < 0) {
        Interval z = arg(dx, -dy);
        return {-z.hi, -z.lo};
    }
    if (dy == 0) return frac(0);
    if (dy > dx) return pi/frac(2) - atan_unit(dx, dy);
    return atan_unit(dy, dx);
}

Interval angular_shift(Interval dx, Interval dy) {
    dx.lo = std::max(Int(0), dx.lo);
    return {arg(dy.lo < 0 ? dx.lo : dx.hi, dy.lo).lo,
            arg(dy.hi > 0 ? dx.lo : dx.hi, dy.hi).hi};
}

class Sweep {
    const std::vector<Node>& nodes;
    std::vector<int> left, right, tree;
    bool chord;

    int lo(int i) const { return chord ? nodes[i].chord_end_min : nodes[i].left; }
    int hi(int i) const { return chord ? nodes[i].chord_start_max : nodes[i].right; }

public:
    Sweep(const std::vector<Node>& nodes, bool chord)
        : nodes(nodes), left(nodes.size()), right(nodes.size()), tree(LIMIT+1), chord(chord) {
        for (int i = 0; i < int(nodes.size()); ++i) left[i] = right[i] = i;
        std::sort(left.begin(), left.end(), [&](int i, int j) { return lo(i) > lo(j); });
        std::sort(right.begin(), right.end(), [&](int i, int j) { return hi(i) > hi(j); });
    }

    void advance(const std::vector<int>& start, std::vector<int>& next) {
        std::fill(tree.begin(), tree.end(), INF);
        unsigned j = 0;
        for (int i : left) {
            while (j < right.size() && hi(right[j]) >= lo(i)) {
                int index = right[j++];
                for (int k = LIMIT-nodes[index].inner_right; k <= LIMIT; k += k&-k)
                    tree[k] = std::min(tree[k], start[index]);
            }
            next[i] = INF;
            for (int k = LIMIT-nodes[i].inner_left; k > 0; k -= k&-k)
                next[i] = std::min(next[i], tree[k]);
        }
    }
};

struct Result {
    int normal[9] = {};
    int with_chord[8] = {};
    int ordinary_five = 0;
    int prefix_five = 0;
    std::vector<std::pair<int, int>> refine;
};

struct SiteWindow {
    Interval theta{100*S, -100*S};
    Interval rho{100*S, -100*S};
};

void extend(Interval& hull, Interval value) {
    hull.lo = std::min(hull.lo, value.lo);
    hull.hi = std::max(hull.hi, value.hi);
}

std::vector<SiteWindow> long_fan_windows(const std::vector<Node>& nodes,
                                        const std::vector<SiteWindow>& cells,
                                        Sweep& forward, Int need) {
    auto reverse_nodes = nodes;
    for (Node& node : reverse_nodes) {
        const int left = LIMIT-node.right;
        const int inner_left = LIMIT-node.inner_right;
        node.right = LIMIT-node.left;
        node.inner_right = LIMIT-node.inner_left;
        node.left = left;
        node.inner_left = inner_left;
        assert(0 < node.inner_left && node.inner_right < LIMIT);
    }
    Sweep backward(reverse_nodes, false);
    std::size_t count = nodes.size();
    std::vector<std::vector<int>> start(6, std::vector<int>(count));
    std::vector<std::vector<int>> end(6, std::vector<int>(count));
    for (std::size_t i = 0; i < count; ++i) {
        start[0][i] = nodes[i].start;
        end[5][i] = reverse_nodes[i].left;
    }
    for (int step = 1; step <= 5; ++step) {
        forward.advance(start[step-1], start[step]);
        backward.advance(end[6-step], end[5-step]);
    }
    std::vector<SiteWindow> answer(6);
    for (int layer = 0; layer <= 5; ++layer) {
        for (std::size_t i = 0; i < count; ++i) {
            int span = LIMIT-end[layer][i]-start[layer][i];
            if (Wide(span)*S < Wide(need)*TICKS) continue;
            extend(answer[layer].theta, cells[i].theta);
            extend(answer[layer].rho, cells[i].rho);
        }
    }
    return answer;
}

Result bound(Interval r, int rho_start, int p_limit, int p_step, int rho_step,
             int theta_denominator, int last_step, bool check_chord,
             int p_begin = 0, Int lower_need = 0, bool windows = false) {
    Interval two_r = frac(2)*r;
    Interval radial_optimum = root(frac(1)-sq(r));
    Int alpha_max = arc_at(radial_optimum.lo).hi;
    Int gamma_max = arc_at(root(frac(1)-sq(two_r)).lo).hi;
    Int min_ordinary = pi.lo-gamma_max-5*alpha_max;
    std::vector<AngularCell> angular;
    for (int j = -315*theta_denominator/100; j < 955*theta_denominator/100; ++j) {
        Interval theta{frac(j, theta_denominator).lo, frac(j+1, theta_denominator).hi};
        angular.push_back({theta, trig(theta, 1), trig(theta, 0)});
    }
    std::vector<RadialCell> radial;
    for (int j = rho_start; j < 1000; j += rho_step) {
        Interval rho{frac(j, 1000).lo, frac(std::min(j+rho_step, 1000), 1000).hi};
        auto alpha = [&](Int end) {
            Interval x{end, end};
            Interval c = frac(1) - (sq(r)-sq(frac(1)-x))/(frac(2)*x);
            return Interval{arc_at(c.hi).lo, arc_at(c.lo).hi};
        };
        Interval low = alpha(rho.lo), high = alpha(rho.hi);
        Int upper = rho.hi < radial_optimum.lo ? high.hi
                  : rho.lo > radial_optimum.hi ? low.hi : alpha_max;
        radial.push_back({rho, {std::min(low.lo, high.lo), std::min(upper, alpha_max)}});
    }
    Result result;
    Int max_dist_squared = sq(two_r).hi;
    static const auto beta_upper = [] {
        std::vector<Int> values(TABLE+1);
        for (int j = 0; j <= TABLE; ++j)
            values[j] = arc_at(root(frac(j, TABLE)).lo).hi;
        return values;
    }();
    for (int p0 = p_begin; p0 < p_limit; p0 += p_step) {
        int p1 = std::min(p0+p_step, p_limit);
        Interval p{frac(p0, 1000).lo, frac(p1, 1000).hi};
        std::vector<Node> nodes;
        std::vector<SiteWindow> cells;
        for (const auto& a : angular) {
            for (const auto& b : radial) {
                // Lower-bound the distance by monotonicity in rho and cos(theta)
                // and exact minimization of the resulting quadratic in p.
                Interval rho_min{b.rho.lo, b.rho.lo}, cos_max{a.cosine.hi, a.cosine.hi};
                Interval d2 = b.rho.lo >= p.hi
                    ? sq(p-rho_min*cos_max) + sq(rho_min)*(frac(1)-sq(cos_max))
                    : sq(b.rho-p) + frac(2)*b.rho*p*(frac(1)-a.cosine);
                if (d2.lo > max_dist_squared) continue;
                Int beta = beta_upper[floor_div(Wide(d2.lo)*TABLE, max_dist_squared)];
                Interval phi = a.theta + angular_shift(b.rho-p*a.cosine, p*a.sine);
                int l = down(a.theta.lo-b.alpha.hi);
                int u = up(a.theta.hi+b.alpha.hi);
                int l2 = down(phi.lo-beta), u2 = up(phi.hi+beta);
                assert(l2 > 0 && u2 < LIMIT);
                int start = a.theta.lo <= pi.hi && a.theta.hi >= -pi.hi ? l : INF;
                nodes.push_back({l, u, l2, u2, start, down(a.theta.lo+b.alpha.lo),
                                 up(a.theta.hi-b.alpha.lo+2*gamma_max), up(a.theta.hi-b.alpha.lo),
                                 b.alpha.hi >= min_ordinary});
                if (windows) cells.push_back({a.theta, b.rho});
            }
        }
        Sweep ordinary_link(nodes, false);
        if (windows) {
            const auto hull = long_fan_windows(nodes, cells, ordinary_link, 2*pi.lo-6*alpha_max);
            if (hull[0].theta.lo <= hull[0].theta.hi) {
                std::printf("%d %d", p0, p1);
                for (const auto& site : hull)
                    std::printf(" %lld %lld %lld %lld",
                                static_cast<long long>(site.theta.lo),
                                static_cast<long long>(site.theta.hi),
                                static_cast<long long>(site.rho.lo),
                                static_cast<long long>(site.rho.hi));
                std::puts("");
            }
            continue;
        }
        const std::size_t n = nodes.size();
        if (!check_chord || p0 < 187) {
            std::vector<int> start(n), next(n);
            for (std::size_t i = 0; i < n; ++i) start[i] = nodes[i].start;
            for (int step = 1; step <= last_step; ++step) {
                ordinary_link.advance(start, next);
                start.swap(next);
                int span = 0;
                for (std::size_t i = 0; i < n; ++i)
                    span = std::max(span, nodes[i].right-start[i]);
                result.normal[step] = std::max(result.normal[step], span);
                if (lower_need != 0 && step == last_step && Wide(span)*S >= Wide(lower_need)*TICKS) {
                    if (!result.refine.empty() && result.refine.back().second == p0)
                        result.refine.back().second = p1;
                    else result.refine.emplace_back(p0, p1);
                }
            }
        }
        if (check_chord) {
            Sweep chord_link(nodes, true);
            // Before the chord, the last node is either ordinary or can be
            // the first endpoint of the chord. After the chord it is either
            // the second endpoint of the chord or an ordinary node.
            std::vector<int> before(n), ready(n), just_crossed(n, INF), after(n, INF), merged(n);
            for (std::size_t i = 0; i < n; ++i) {
                ready[i] = nodes[i].start;
                before[i] = nodes[i].ordinary ? ready[i] : INF;
            }
            for (int step = 1; step <= 7; ++step) {
                for (std::size_t i = 0; i < n; ++i) merged[i] = std::min(just_crossed[i], after[i]);
                ordinary_link.advance(merged, after);
                chord_link.advance(ready, just_crossed);
                ordinary_link.advance(before, ready);
                for (std::size_t i = 0; i < n; ++i) {
                    if (!nodes[i].ordinary) after[i] = INF;
                    before[i] = nodes[i].ordinary ? ready[i] : INF;
                    int first = std::min(just_crossed[i], after[i]);
                    result.with_chord[step] = std::max(result.with_chord[step], nodes[i].right-first);
                    if (step == 5 && p0 < 282) {
                        result.ordinary_five = std::max(result.ordinary_five, nodes[i].right-before[i]);
                        result.prefix_five = std::max(result.prefix_five, nodes[i].left_max-ready[i]);
                    }
                }
            }
        }
    }
    return result;
}

void verify(const char* label, int links, int got, Int need) {
    std::printf("%s %d links: span at most %d/%d radians.\n", label, links, got, TICKS);
    std::fflush(stdout);
    assert(Wide(got)*S < Wide(need)*TICKS);
}

int main(int argc, char** argv) {
    bool lower = argc == 2 && std::string_view(argv[1]) == "lower";
    bool windows = argc == 2 && std::string_view(argv[1]) == "windows";
    assert(argc == 1 || lower || windows);
    if (windows) {
        bound(frac(19, 50), 620, 282, 4, 4, 100, 5, false, 0, 0, true);
        return 0;
    }
    if (lower) {
        Interval r = frac(378, 1000);
        Int alpha = arc_at(root(frac(1)-sq(r)).lo).hi;
        Int need = 2*pi.lo-6*alpha;
        Result result = bound(r, 622, 282, 2, 2, 250, 5, false, 0, need);
        if (result.refine.empty()) verify("Universal lower bound", 5, result.normal[5], need);
        for (const auto& segment : result.refine) {
            std::printf("Refining p in [%d, %d]/1000.\n", segment.first, segment.second);
            std::fflush(stdout);
            Result fine = bound(r, 622, segment.second, 1, 1, 1000, 5, false, segment.first);
            verify("Refined universal lower bound", 5, fine.normal[5], need);
        }
        return 0;
    }
    Interval r = frac(19, 50);
    Int alpha = arc_at(root(frac(1)-sq(r)).lo).hi;
    Int gamma = arc_at(root(frac(1)-sq(frac(2)*r)).lo).hi;
    Result result = bound(r, 620, 620, 4, 5, 100, 8, true);
    for (int step = 6; step <= 8; ++step)
        verify("Ordinary chain", step, result.normal[step], 2*pi.lo-2*(8-step)*alpha);
    for (int step = 4; step <= 7; ++step)
        verify("Chain with one diagonal", step, result.with_chord[step], 2*pi.lo-2*(7-step)*alpha);
    verify("All six vertices outside diagonal block", 5, result.ordinary_five, 2*pi.lo-6*alpha);
    verify("Last vertex shared with diagonal block", 5, result.prefix_five, 2*pi.lo-2*gamma-2*alpha);
}
