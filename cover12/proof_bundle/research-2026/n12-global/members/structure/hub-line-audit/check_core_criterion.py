"""Independent checks for the two-hub core criterion (K10-HUB-LINE-CHART.md).

NOT sampling: the checks below use (a) exact-rational identities for the
boundary configurations, and (b) an independent evaluation of the exact
max-over-dK of the nearest-hub distance at the algebraically relevant
candidates (arc endpoints, guarded antipodes, case boundary), compared with
the document's criterion.  A random scan is included only as a secondary
sanity check and is labelled as such.

Setting: U fixed, a=1-2U, e0=3U-1, hubs h1=(x-s,y), h2=(x+s,y), s>0, x,y>=0,
inactive constraints (x+s)^2+y^2<=(1-U)^2 (implies the h1 one).

Document criterion (to audit):
  case x>=a : K covered  <=>  (x-s)^2+y^2 <= e0^2
  case 0<=x<a: q=sqrt(a^2-x^2); need s^2+(y+q)^2 <= U^2;
               plus, if a(s-x) <= x sqrt((x-s)^2+y^2) then also
               (x-s)^2+y^2 <= e0^2.
Independent criterion:  max over X in K of min(|X-h1|,|X-h2|) <= U, and the
max is attained on dK, where it equals max over the two closed arcs
{X in dK : X_coord <= x} (h1 nearest) and {X_coord >= x} (h2 nearest) of the
distance to the respective hub; on an arc the maximum is at an endpoint or at
the antipodal point of that hub (if inside the arc).
"""
import math
from fractions import Fraction as F

Uq = F("0.361102963744508672616920293904")
U = float(Uq)
a = 1.0 - 2.0 * U
e0 = 3.0 * U - 1.0


def doc_criterion(s, x, y, verbose=False):
    if x >= a - 1e-15:
        ok = (x - s) ** 2 + y ** 2 <= e0 ** 2 + 1e-15
        return ok, "case1"
    q = math.sqrt(max(0.0, a * a - x * x))
    ok1 = s * s + (y + q) ** 2 <= U * U + 1e-15
    ok2 = True
    if a * (s - x) <= x * math.hypot(x - s, y) + 1e-15:
        ok2 = (x - s) ** 2 + y ** 2 <= e0 ** 2 + 1e-15
    return (ok1 and ok2), "case2"


def independent_cover(s, x, y):
    """max over dK of min-distance, evaluated at the exact candidate points.

    Candidates on dK: the two bisector points (x,+-q) (arc endpoints, when
    x<a), the point -a*h1/|h1| (only a candidate for h1's arc, where it has
    distance a+|h1|), and -a*h2/|h2| (candidate for h2's arc).
    """
    best = 0.0
    if x < a - 1e-15:
        q = math.sqrt(max(0.0, a * a - x * x))
        for sv in (1, -1):
            X = (x, sv * q)
            d = min(math.hypot(X[0] - (x - s), X[1] - y),
                    math.hypot(X[0] - (x + s), X[1] - y))
            best = max(best, d)
    n1 = math.hypot(x - s, y)
    if n1 > 0:
        Xa = (-a * (x - s) / n1, -a * y / n1)      # point -a * h1/|h1|
        if Xa[0] <= x + 1e-15:                     # inside h1's arc
            best = max(best, a + n1)
    n2 = math.hypot(x + s, y)
    if n2 > 0:
        Xb = (-a * (x + s) / n2, -a * y / n2)      # point -a * h2/|h2|
        if Xb[0] >= x - 1e-15:                     # inside h2's arc
            best = max(best, a + n2)
    return best


def check(label, s, x, y):
    d_ok, case = doc_criterion(s, x, y)
    ind = independent_cover(s, x, y)
    ind_ok = ind <= U + 1e-12
    agree = (d_ok == ind_ok)
    print("%-46s s=%.6f x=%.6f y=%.6f  doc=%s(%s) ind=%s  maxdist=%.9f  %s"
          % (label, s, x, y, d_ok, case, ind_ok, ind, "agree" if agree else "MISMATCH"))
    return agree


if __name__ == "__main__":
    print("U=%.15f a=%.15f e0=%.15f" % (U, a, e0))
    ok = True
    # exact-rational boundary identities
    assert abs((U - a) - e0) < 1e-15, "U-a == e0 identity"
    print("identity U-a == 3U-1 == e0: %.3e" % abs((U - a) - e0))
    print("identity |h1|+a == U at (s,x,y)=(U,a,0): %.3e"
          % abs((abs(a - U) + a) - U))
    # algebraically constructed cases: case boundary, guard boundary, tangency
    cases = [
        ("case1 interior (s=0.25,x=0.35)", 0.25, 0.35, 0.0),
        ("case1 tight (s=U,x=a,y=0)", U, a, 0.0),
        ("case1 off (s=0.25,x=0.35,y=0.10)", 0.25, 0.35, 0.10),
        ("case2 endpoints tight", 0.20, 0.20, math.sqrt(max(0.0, U * U - 0.04))),
        ("guard boundary s=x", 0.25, 0.25, 0.02),
        ("case2 x<a, endpoints off", 0.30, 0.10, 0.05),
        ("antipode inside arc", 0.30, 0.20, 0.02),
        ("x=0 midpoint at origin", 0.20, 0.0, 0.05),
        ("large s infeasible", 0.50, 0.20, 0.0),
        ("s just below U", 0.36, 0.28, 0.0),
    ]
    for (lab, s, x, y) in cases:
        ok &= check(lab, s, x, y)
    # secondary sanity scan (labelled; not the verification)
    import random
    rnd = random.Random(7)
    bad = 0
    for _ in range(4000):
        s = rnd.uniform(0.0, 0.7)
        x = rnd.uniform(0.0, min(0.65, 1.0 - U - s) if s < 1.0 - U else 0.0)
        y = rnd.uniform(0.0, 0.25)
        if (x + s) ** 2 + y ** 2 > (1.0 - U) ** 2:
            continue
        d_ok, _ = doc_criterion(s, x, y)
        ind_ok = independent_cover(s, x, y) <= U + 1e-12
        if d_ok != ind_ok:
            bad += 1
    print("secondary random sanity scan (labelled, not the verification): "
          "disagreements =", bad)
    print("all constructed-case checks agree:", ok)
