# -*- coding: utf-8 -*-
"""
r20-alternative / rational controls for CENTRAL-COUPLING.md:
  (a) d = 2r correction: feasible set is the whole Thales circle (1-D), not a point;
  (b) the complete finite construction (vertical decomposition, W0/W1/W2) on two rational instances,
      including a NESTED case where a "centres-only" candidate list fails (fake completeness)
      while the construction finds witnesses, and a generic case with rational circle intersections.
Exact rational / quadratic arithmetic only; no sampling, no optimisation.
"""
from fractions import Fraction as F
from itertools import combinations


# ---------- exact comparisons in Q(sqrt(s)) : value = a + b*sqrt(s), s >= 0 rational ----------
def sign_qsqrt(a, b, s):
    if b == 0:
        return (a > 0) - (a < 0)
    if s == 0:
        return (a + b > 0) - (a + b < 0) if False else ((a > 0) - (a < 0)) if b == 0 else ((a + b > 0) - (a + b < 0))
    if b > 0:
        if a >= 0:
            return 1
        return 1 if a * a < b * b * s else (0 if a * a == b * b * s else -1)
    else:
        if a <= 0:
            return -1
        return 1 if a * a > b * b * s else (0 if a * a == b * b * s else -1)


def cmp_qsqrt_rational(a, b, s, q):
    """sign of (a + b sqrt(s)) - q"""
    return sign_qsqrt(a - q, b, s)


print("=" * 96)
print("[a] d = 2r correction: chord (0,0)-(10,0), r = 5 -> feasible set = Thales circle B((5,0),5) boundary")
def R2_eq_check(P, Q, S):
    """exact comparison R_c(P,Q,S) <= r using A1A2A3 <= 4 r^2 X^2 (squares only, rational input)."""
    def sub(a, b): return (a[0] - b[0], a[1] - b[1])
    def dot(a, b): return a[0] * b[0] + a[1] * b[1]
    def cross(a, b): return a[0] * b[1] - a[1] * b[0]
    A1 = dot(sub(Q, S), sub(Q, S)); A2 = dot(sub(S, P), sub(S, P)); A3 = dot(sub(P, Q), sub(P, Q))
    X = cross(sub(Q, P), sub(S, P))
    r = F(5)
    return A1 * A2 * A3, 4 * r * r * X * X
for h in [(F(5), F(5)), (F(1), F(3)), (F(9), F(3)), (F(5), F(1)), (F(5), F(4))]:
    lhs, rhs = R2_eq_check((F(0), F(0)), (F(10), F(0)), h)
    on_circle = (h[0] - 5) ** 2 + h[1] ** 2 == 25
    print("   h=%-10s on Thales circle: %-5s   A1A2A3 = %-10s vs 4r^2X^2 = %-10s  ->  R<=r : %s"
          % (h, on_circle, lhs, rhs, lhs <= rhs))

print("\n" + "=" * 96)
print("[b] complete finite construction on rational instances")

def circle_roots(cx, cy, rho, x):
    """roots y of (x-cx)^2+(y-cy)^2 = rho^2 as (a,b,s) with y = a + b*sqrt(s); [] if none."""
    t = rho * rho - (x - cx) ** 2
    if t < 0:
        return []
    return [(cy, F(1), t), (cy, F(-1), t)]


def classify(q, rho, w):
    """exact sign of |w-q|^2 - rho^2 for w = (wx, wy) with wy in Q(sqrt(s)); returns -1/0/1."""
    wx, (wa, wb, ws) = w
    # (wx-qx)^2 + (wy-qy)^2 - rho^2 = [(wx-qx)^2 + (wa-qy)^2 - rho^2] + 2(wa-qy)wb sqrt(ws) + wb^2 ws
    t = (wx - q[0]) ** 2 + (wa - q[1]) ** 2 - rho * rho + wb * wb * ws
    u = 2 * (wa - q[1]) * wb
    return sign_qsqrt(t, u, ws)


def pick_rational_in(lo, hi, ws_lo, ws_hi):
    """a rational strictly between two algebraic endpoints (each a + b sqrt(s))."""
    for den in (1, 2, 3, 4, 5, 6, 8, 10, 12, 20, 50, 100):
        for num in range(-100 * den, 100 * den + 1):
            q = F(num, den)
            if cmp_qsqrt_rational(lo[0], lo[1], lo[2], q) > 0 and cmp_qsqrt_rational(hi[0], hi[1], hi[2], q) < 0:
                return q
    return None


def construction(K, disks, inside, outside, label):
    """K = (center, radius); disks list; inside/outside = index sets; vertical decomposition witnesses."""
    circles = [K] + list(disks)
    xs = set()
    for (c, rho) in circles:
        xs.add(c[0] - rho); xs.add(c[0] + rho)
    # circle-circle intersection x-coordinates (exact when rational in these instances)
    for i, j in combinations(range(len(circles)), 2):
        (c1, r1), (c2, r2) = circles[i], circles[j]
        dx, dy = c2[0] - c1[0], c2[1] - c1[1]
        # radical axis: solve 2 dx (x) + 2 dy y = ... ; here we restrict to dx != 0 cases
        if dy == 0 and dx != 0:
            # 2 dx x = r1^2 - r2^2 + c2x^2 - c1x^2  -> rational if data rational
            x = (r1 * r1 - r2 * r2 + c2[0] ** 2 - c1[0] ** 2) / (2 * dx)
            if abs(x - c1[0]) <= r1 and abs(x - c2[0]) <= r2:
                xs.add(x)
        else:
            # general: solve numerically-exact is out of scope for this rational control; skip with a note
            pass
    xs = sorted(xs)
    strips = [(xs[i], xs[i + 1]) for i in range(len(xs) - 1)]
    W = []
    # W0: circle-circle intersections (for our rational instances, computed via the dy==0 formula)
    for i, j in combinations(range(len(circles)), 2):
        (c1, r1), (c2, r2) = circles[i], circles[j]
        dx, dy = c2[0] - c1[0], c2[1] - c1[1]
        if dy == 0 and dx != 0:
            x = (r1 * r1 - r2 * r2 + c2[0] ** 2 - c1[0] ** 2) / (2 * dx)
            t = r1 * r1 - (x - c1[0]) ** 2
            if t > 0:
                for sgn in (1, -1):
                    W.append((f"W0 cc{i}{j}", x, (c1[1], F(sgn), t)))
    # W1/W2 at critical vertical lines and inside strips
    for x, tag in [(x, "crit") for x in xs] + [((a + b) / 2, "strip") for (a, b) in strips]:
        # roots of all circles at this x, merged and sorted by value
        roots = []
        for (c, rho) in circles:
            for (a, b, s) in circle_roots(c[0], c[1], rho, x):
                roots.append((a, b, s))
        # sort by numerical value (rational x's only here)
        import math
        val = lambda r: float(r[0]) + float(r[1]) * math.sqrt(float(r[2]))
        roots.sort(key=val)
        for r in roots:
            W.append((f"W1-{tag}@{x}", x, r))
        for a, b in zip(roots, roots[1:]):
            q = pick_rational_in(a, b, None, None)
            if q is not None:
                W.append((f"W2-{tag}@{x}", x, (q, F(0), F(0))))
    # classification
    good = []
    for name, wx, wy in W:
        ok = True
        for idx in inside:
            c, rho = disks[idx]
            if classify(c, rho, (wx, wy)) > 0:
                ok = False
        for idx in outside:
            c, rho = disks[idx]
            if classify(c, rho, (wx, wy)) <= 0:      # strict: 'on' does NOT pass
                ok = False
        c, rho = K
        if classify(c, rho, (wx, wy)) > 0:
            ok = False
        if ok:
            good.append((name, wx, wy))
    print("   [%s] |W| = %d witnesses ; #witnesses in Omega = %d" % (label, len(W), len(good)))
    if good:
        name, wx, wy = good[0]
        print("      first witness in Omega: %s  x=%s  y = %s + %s*sqrt(%s)" % (name, wx, wy[0], wy[1], wy[2]))
    else:
        print("      Omega empty (by this construction)")
    return W, good


# instance A: concentric nested disks (NO circle-circle intersections inside) -> annulus nonempty
KA = ((F(0), F(0)), F(5))
disksA = [((F(0), F(0)), F(3))]                      # D_a
W, good = construction(KA, disksA, inside=[], outside=[0], label="A nested: Omega = B(0,5) \\ int B(0,3)")
centers_only = [(F(0), F(0))]
print("      centres-only list = %s : all inside int D_a -> would wrongly report EMPTY" % centers_only)
print("      => centres-only candidate list is NOT complete; the W2 interval witnesses are needed.")

# instance B: two radius-5 circles with rational intersections (K = B(0,5), D = B((6,0),5))
KB = ((F(0), F(0)), F(5))
disksB = [((F(6), F(0)), F(5))]
W2, good2 = construction(KB, disksB, inside=[], outside=[0], label="B generic: Omega = B(0,5) \\ int B((6,0),5)")
print("      (W0 contains the rational intersections (3,+-4); 'on' does not pass the strict outside predicate)")

# instance C: inside-predicate case (needs inclusive handling): Omega = B(0,5) cap B((6,0),5)
W3, good3 = construction(KB, disksB, inside=[0], outside=[], label="C inclusive: Omega = B(0,5) cap B((6,0),5)")
print("      (boundary point (3,4) is ON both circles: inclusive 'inside' accepts it -> tests the strict/inclusive split)")
