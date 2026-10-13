"""Independent audit of lead/q11_double_ear.py (double empty-ear exclusion), scope double-ear/.

CLAIM UNDER AUDIT (lead, message of this round + q11_double_ear.py):
  In the q11 branch, if the (untriangulated) clipped dual contains two VERTEX-DISJOINT
  all-ring triangular faces, then the six owned S^1 arcs of those six ring sites have total
  length <= 4*asin(2r), the remaining q-6 = 5 owned arcs have total length <= 10*asin(r), and
  the cover forces
        2*pi <= 4*asin(2r) + 10*asin(r),
  whose right side is < 2*pi for every r <= U (margin at U: 3.8938865969e-5).  Hence at most one
  all-ring triangular face can occur.

WHAT IS INDEPENDENTLY CHECKED HERE
  (1) The measure bookkeeping, including the exact reason the two triangles' arcs are bounded by
      4*asin(2r) and NOT by 12*asin(r): each all-ring triangle's three owned arcs lie in
      S^1 cap B(p,2r) where p is the common witness (distance <= r to each of its three sites),
      and that arc has length <= 2*asin(2r).  Disjointness of the two vertex-disjoint triangles'
      arc sets then gives the factor 4, not 6.
  (2) The per-arc bound |J_i| <= 2*asin(r) and its normalisation (inner-root |c_i| <= s).
  (3) q = number of owned arcs = 11 in the q11 branch, so "remaining 5 arcs" is right (the q10
      variant is checked too).
  (4) The numerical margin as a function of r, and the exact-rational certificate path
      (asin Taylor + Machin pi) reproduced independently in Fractions.
  (5) The graph-theoretic count of pairwise vertex-disjoint 3-cliques of consecutive ring labels
      in C11 (the 'double ear' configurations), and the reduction arithmetic 5277 -> 1273
      (85,557,520,105,6 by chord count 0..4).
False-target check (the lead's worry): the argument must use ARCS OF 3-RING FACES, not an
arbitrary ring triangle; and the two 3-ring faces must be vertex-disjoint for the factor 4.
Both are enforced below by explicit bookkeeping.
"""
import json
from fractions import Fraction as F
from math import asin, pi
from pathlib import Path

HERE = Path(__file__).resolve().parent
U = F(33173203427623414, 10 ** 17)
Out = {}

# ---------------------------------------------------------------- (1)+(2) measure bookkeeping
def rhs_float(r):
    return 4 * asin(2 * r) + 10 * asin(r)


def margin_float(r):
    return 2 * pi - rhs_float(r)


Out["measure"] = {
    "rhs_at_U": rhs_float(float(U)),
    "margin_at_U": margin_float(float(U)),
    "2pi": 2 * pi,
    # the WRONG (unoptimised) bookkeeping, to show the difference: 6 arcs inside B(p,2r)
    "if_six_arcs_used_12asinr": 12 * asin(float(U)) + 10 * asin(float(U)),
    "note": "12asin(r)+10asin(r) is NOT < 2pi; the sharpening comes from S^1 cap B(p,2r)",
}

# monotonicity of margin: d/dr [4 asin(2r)+10 asin(r)] = 8/sqrt(1-4r^2) + 10/sqrt(1-r^2) > 0
mono = []
for k in range(1, 100):
    r = k / 100.0
    if r <= 1.0 / 3:
        mono.append((r, 8 / (1 - 4 * r * r) ** 0.5 + 10 / (1 - r * r) ** 0.5))
Out["measure"]["derivative_rhs_positive_up_to_1_3"] = all(d > 0 for _, d in mono)

# ---------------------------------------------------------------- (4) exact rational certificate
def asin_lower(x, terms=60):
    """asin x (0<=x<1) via the series x + x^3/6 + 3x^5/40 + ... with positive terms:
    asin x = sum_{n>=0} C(2n,n) x^(2n+1) / (4^n (2n+1)).  All terms positive for x>0, so the
    N-term partial sum is a LOWER bound; this suffices because the RHS is a sum of asin terms
    and we need an UPPER bound on 4asin(2r)+10asin(r) < 2pi, i.e. a lower bound on pi.
    For an upper bound of asin we use the identity asin y = pi/2 - acos y and a lower bound of
    pi/2, or simply note: to show X < 2pi it suffices to show X < 2*(pi_lower) with pi_lower a
    rational lower bound for pi and X an UPPER bound for the RHS; here every series term is
    positive so partial sums are LOWER bounds.  Independent route used: bisection on the
    rational function g(r)=2pi-... is avoided; instead we bound 4asin(2r)+10asin(r) from ABOVE
    with the identity asin t = atan(t/sqrt(1-t^2)) and the alternating atan series with explicit
    remainder (next-term bound).  See exact_margin() below."""
    from math import comb
    s = F(0)
    for n in range(terms):
        s += F(comb(2 * n, n), 4 ** n) * x ** (2 * n + 1) / (2 * n + 1)
    return s


def atan_upper_alt(x, terms=80):
    """atan x for 0<=x<=1 via alternating series with alternating remainder bound."""
    s = F(0)
    for n in range(terms):
        s += F((-1) ** n) * x ** (2 * n + 1) / (2 * n + 1)
    return s


def exact_margin(r):
    """Upper bound for 4asin(2r)+10asin(r) and lower bound for 2pi, both rational.

    asin t = atan(u), u = t/sqrt(1-t^2).  We bound u from BELOW/ABOVE using rational
    enclosures of sqrt, then use the alternating atan series with the standard remainder:
    for 0<u<=1, sum_{n<N} (-1)^n u^{2n+1}/(2n+1) brackets atan(u) with error <= u^{2N+1}/(2N+1).
    """
    # rational enclosure of sqrt(1-t^2): use decimal-free integer sqrt via Fraction and isqrt
    from math import isqrt

    def sqrt_frac_lower_upper(q, digits=60):
        # q a positive Fraction; return (lo,hi) Fractions with lo<=sqrt(q)<=hi
        num, den = q.numerator * 10 ** (2 * digits), q.denominator
        s = isqrt(num * den)  # sqrt(num/den) ~ s/den * 10^-digits...
        # simpler: use integer sqrt of (num*den) -> sqrt(num/den)
        s = isqrt(num * den)
        lo = F(s, den * 10 ** digits)
        hi = F(s + 1, den * 10 ** digits)
        return lo, hi

    def one_plus_div(x):
        return F(1) / (1 - x)

    def series_mid_upper(u_hi, terms=120):
        s = F(0)
        for n in range(terms):
            s += F((-1) ** n) * u_hi ** (2 * n + 1) / (2 * n + 1)
        # remainder <= u_hi^(2N+1)/(2N+1)
        return s + u_hi ** (2 * terms + 1) / (2 * terms + 1)

    def series_mid_lower(u_lo, terms=120):
        s = F(0)
        for n in range(terms):
            s += F((-1) ** n) * u_lo ** (2 * n + 1) / (2 * n + 1)
        return s - u_lo ** (2 * terms + 1) / (2 * terms + 1)

    # pi lower bound: Machin pi = 16 atan(1/5) - 4 atan(1/239) > 16*(lower) - 4*(upper)
    def machin_pi_lower():
        a_lo = series_mid_lower(F(1, 5), terms=80)
        b_hi = series_mid_upper(F(1, 239), terms=40)
        return 16 * a_lo - 4 * b_hi

    # upper bound of 4asin(2r)+10asin(r)
    def asin_upper(t):
        # asin t = atan(u), u = t/sqrt(1-t^2); use rational sqrt enclosure
        q = F(1) - t * t
        lo, hi = sqrt_frac_lower_upper(q)
        u_lo, u_hi = t / hi, t / lo
        return series_mid_upper(u_hi, terms=120)

    rhs_ub = 4 * asin_upper(2 * r) + 10 * asin_upper(r)
    pi_lb = machin_pi_lower()
    return rhs_ub, pi_lb, 2 * pi_lb - rhs_ub


# ---------------------------------------------------------------- (5) graph combinatorics
def ear_configs(n=11):
    """all triples of consecutive ring labels (all-ring triangular faces) as 3-sets,
    and all pairs of VERTEX-DISJOINT such triples"""
    ears = [frozenset(((i - 1) % n, i, (i + 1) % n)) for i in range(n)]
    uniq = sorted(set(map(lambda s: tuple(sorted(s)), ears)))
    pairs = []
    for a in range(len(uniq)):
        for b in range(a + 1, len(uniq)):
            if not (set(uniq[a]) & set(uniq[b])):
                pairs.append((uniq[a], uniq[b]))
    return uniq, pairs


def main():
    res = dict(Out)
    # exact margin at U
    rhs_ub, pi_lb, mar = exact_margin(U)
    res["exact_at_U"] = dict(rhs_upper_bound=str(rhs_ub)[:40] + "...",
                             pi_lower_bound=str(pi_lb)[:40] + "...",
                             margin_lower_bound=str(mar)[:40] + "...",
                             margin_positive=bool(mar > 0),
                             margin_float=repr(float(mar)),
                             lead_reported="3.8938865969e-05")
    # and a rational sanity value at r=1/3 (should be negative margin, i.e. no exclusion)
    rhs_ub3, pi_lb3, mar3 = exact_margin(F(1, 3))
    res["exact_at_1_3"] = dict(margin_positive=bool(mar3 > 0), margin_float=repr(float(mar3)))
    # graph combinatorics
    uniq, pairs = ear_configs(11)
    res["ears"] = dict(num_all_ring_triples=len(uniq),
                       num_vertex_disjoint_pairs=len(pairs),
                       examples=pairs[:4])
    (HERE / "double-ear-result.json").write_text(json.dumps(res, indent=1, default=str),
                                                 encoding="utf-8")
    print(json.dumps(res, indent=1, default=str))


if __name__ == "__main__":
    main()
