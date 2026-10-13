"""Independent checks of the wrapper domain and the three prune predicates.

Deterministic and exact-rational where possible; no sampling is used as
evidence (the few float evaluations are only sanity prints).

Setting (k=10 branch, radius U): h1=(x-s,y), h2=(x+s,y), s=d/2>0, x,y>=0,
a=1-2U, e0=3U-1. Legal triples additionally satisfy
  (L1) both hubs strictly inactive: (x+s)^2+y^2 < (1-U)^2 (implies h1),
  (L2) core covered: max over K=B(0,a) of min_j |X-h_j| <= U, which by the
       audited exact criterion implies y <= e0, x <= s+e0, s <= U.
Wrapper root box: s in [1/20, U], x in [0, 1-U-1/20], y in [0, e0].

Prune predicates implemented in lead/hubline_domain.py:
 (P1) normlower([xl+sl,xh+sh],[yl,yh]) > (1-U)^2
 (P2) exists exact rational core-circle point (a c, a t) with
      min_j lowerbound |(a c,a t)-h_j|^2 > U^2
 (P3) if xh < a: interval lower bound of s^2+(y+sqrt(a^2-x^2))^2 > U^2
"""
from fractions import Fraction as F
import math

U = F("0.361102963744508672616920293904")
a = 1 - 2 * U
e0 = 3 * U - 1
print("U=%s\na=%s  e0=%s" % (U, a, e0))
print("1-U-1/20 = %s ; a = %s ; U = %s ; e0 = %s"
      % (1 - U - F(1, 20), a, U, e0))

# ---- 1. exact-rational identities behind the wrapper
checks = [
    ("x-bound face equals 1-U-1/20", (1 - U - F(1, 20)) == (F(19, 20) - U)),
    ("e0 = 3U-1", e0 == 3 * U - 1),
    ("a = 1-2U", a == 1 - 2 * U),
    ("a < 1-U-1/20", a < 1 - U - F(1, 20)),
]
for name, ok in checks:
    print("identity: %-34s %s" % (name, ok))

# ---- 2. the s=U face contains no legal k=10 triple (exact)
# Legal triples with s=U require (from the audited criterion) x=a, y=0, giving
# h1=(-e0,0), h2=(1-U,0); then |h2| = 1-U exactly, so h2 is boundary-active.
s = U
x = a
y = F(0)
h2norm = x + s
print("s=U face: only candidate (x,y)=(a,0); |h2| = %s  (1-U = %s) equal=%s"
      % (h2norm, 1 - U, h2norm == 1 - U))
print("  -> h2 touches S^1, so it is not strictly inactive: excluded by (L1)")

# ---- 3. legality implies the wrapper contains the triple
def wrapper_contains(s, x, y):
    return (F(1, 20) <= s <= U) and (0 <= x <= 1 - U - F(1, 20)) \
           and (0 <= y <= e0)


def legal_implies_bounds(s, x, y):
    """using only (L1) and the audited necessary bounds x<=s+e0, y<=e0, s<=U."""
    if s < F(1, 20):
        return "outside wrapper (near-merge region s<=1/20)"
    if x + s > 1 - U:
        return "illegal: violates inactivity"
    if y > e0:
        return "illegal: violates y<=e0"
    if s > U:
        return "illegal: s<=U is necessary"
    return "inside wrapper" if wrapper_contains(s, x, y) else "MISS"


# deterministic corner/edge cases (exact rationals, no sampling)
cases = [
    ("s=1/20 seam", F(1, 20), F(0), F(0)),
    ("s=U face", U, a, F(0)),
    ("x at face", F(1, 5), 1 - U - F(1, 20), F(0)),
    ("y at e0 face", F(1, 5), F(0), e0),
    ("just above e0 (illegal)", F(1, 5), F(0), e0 + F(1, 1000000)),
    ("x+s>1-U (illegal)", F(1, 5), 1 - U - F(1, 5) + F(1, 1000000), F(0)),
    ("s>U (illegal)", U + F(1, 1000000), a, F(0)),
]
for name, sv, xv, yv in cases:
    print("case %-24s -> %s" % (name, legal_implies_bounds(sv, xv, yv)))

# ---- 4. prune predicates: exact interval arithmetic on rational boxes
def isnorm_sq(iv):
    lo, hi = iv
    if lo <= 0 <= hi:
        return (F(0), max(lo * lo, hi * hi))
    return (min(lo * lo, hi * hi), max(lo * lo, hi * hi))


def normlower(ix, iy):
    return isnorm_sq(ix)[0] + isnorm_sq(iy)[0]


def P1(B):
    (sl, sh), (xl, xh), (yl, yh) = B
    return normlower((xl + sl, xh + sh), (yl, yh)) > (1 - U) ** 2


def P2(B, units):
    (sl, sh), (xl, xh), (yl, yh) = B
    h1x = (xl - sh, xh - sl)
    h2x = (xl + sl, xh + sh)
    for c, t in units:
        cx, cy = a * c, a * t
        d1 = normlower((h1x[0] - cx, h1x[1] - cx), (yl - cy, yh - cy))
        d2 = normlower((h2x[0] - cx, h2x[1] - cx), (yl - cy, yh - cy))
        if min(d1, d2) > U * U:
            return True
    return False


def P3(B, lo_sqrt, hi_sqrt):
    """P3 with outward sqrt bounds of sqrt(a^2-x^2) on [xl,xh]."""
    (sl, sh), (xl, xh), (yl, yh) = B
    if not (xh < a):
        return False
    q = (lo_sqrt, hi_sqrt)
    yq = (yl + q[0], yh + q[1])
    return isnorm_sq((sl, sh))[0] + isnorm_sq(yq)[0] > U * U


def sqrt_bounds(xl, xh):
    """outward rational bounds for sqrt(a^2-x^2) on x in [xl,xh] c [0,a]."""
    def rsqrt(v, up):
        if v <= 0:
            return F(0)
        # integer sqrt with directed rounding (v is an exact Fraction)
        num, den = v.numerator, v.denominator
        n = math.isqrt(num * den)
        lo = F(n, den)                     # <= sqrt(v)
        hi = F(n + 1, den)                 # >= sqrt(v)
        return hi if up else lo
    top = a * a - xl * xl              # largest value of a^2-x^2
    bot = a * a - xh * xh              # smallest value
    return (rsqrt(max(bot, F(0)), False), rsqrt(max(top, F(0)), True))


# exact rational unit vectors on the core circle
UNITS = [(F(1), F(0)), (F(0), F(1)), (F(-1), F(0)), (F(0), F(-1)),
         (F(3, 5), F(4, 5)), (F(4, 5), F(-3, 5)), (F(-5, 13), F(12, 13)),
         (F(12, 13), F(5, 13))]

# boxes: legal-ish and deliberately illegal, exact rational endpoints
boxes = [
    ("legal-ish centred box", ((F(1, 5), F(1, 5)), (F(0), F(1, 5)), (F(0), e0))),
    ("far hub box (P1 expected)", ((F(1, 5), F(3, 10)), (F(1, 2), F(3, 5)), (F(0), e0))),
    ("straddles x=a (P3 must not fire)", ((F(1, 5), F(1, 4)), (F(1, 4), F(3, 10)), (F(0), e0))),
    ("x<a, endpoints violated (P3 expected)", ((F(3, 10), F(2, 5)), (F(0), F(1, 10)), (F(1, 10), F(3, 10)))),
]
for name, B in boxes:
    p1 = P1(B)
    p2 = P2(B, UNITS)
    q = sqrt_bounds(B[1][0], B[1][1])
    p3 = P3(B, *q)
    print("box %-38s P1=%s P2=%s P3=%s" % (name, p1, p2, p3))
print("note: P2/P3 fire only on exact-rational, case-guarded conditions; "
      "P3 is only evaluated when xh<a (conservative).")
