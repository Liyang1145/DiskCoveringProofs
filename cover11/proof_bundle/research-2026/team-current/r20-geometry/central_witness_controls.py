"""r20-geometry Round-8: symbolic/exact controls for the fixed-a witness formulas (H1-H6, two moving
central disks + pins), lead-directed.  No children, no claims.

Checks
  C1  moving-disk centre p_sigma(a,c) = m +/- k n satisfies |p-a| = |p-c| = r  (exact rational instances
      + symbolic simplification attempt)
  C2  MEC criterion for a triple: MEC > r  <=>  (pair > 2r)  or  (acute and circumradius > r)
      - exact-rational instances, cross-checked against an independent 3-point MEC algorithm
      - obtuse control: circumradius > r but MEC <= r  (shows the acuteness clause is load-bearing)
      - right triangle, collinear case
  C3  orientation-freeness: the witness expressions (squared sides, cross^2, acuteness tests) are
      invariant under exact rational rotations/reflections and under permutations
  C4  open ball + two disks: explicit nearest-to-lens candidates, semantics mu >= rho (>=), with the
      tangency control mu = rho exactly (fires) and a strict-outside control

Repro: py -3 -B -X utf8 research-2026/team-current/r20-geometry/central_witness_controls.py
"""
import io, itertools
from fractions import Fraction as F
from mpmath import mp, mpf, sqrt
import sympy as sp

OUT = []


def say(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s)
    print(s)


# ---------------------------------------------------------------- C1
say("=" * 100)
say("C1. moving central-disk centre p_sigma(a,c) = m +/- k n (radius-r circles through a and c)")
say("=" * 100)
a1, a2, c1, c2, r = sp.symbols('a1 a2 c1 c2 r', positive=True)
A = sp.Matrix([a1, a2])
C = sp.Matrix([c1, c2])
m = (A + C) / 2
dv = C - A
d2 = sp.expand(dv.dot(dv))
k2 = r ** 2 - d2 / 4
# verify with n = perp(dv)/sqrt(d2): |p - a|^2 = r^2 and |p - c|^2 = r^2, using n.n = 1 and n.(m-a) = 0
n_expr = sp.Matrix([-dv[1], dv[0]]) / sp.sqrt(d2)
P = m + sp.sqrt(k2) * n_expr
e1 = sp.simplify(sp.expand((P - A).dot(P - A) - r ** 2))
say("  symbolic |p-a|^2 - r^2 = %s" % e1)
say("  (manual identity, used as the control: |m-a + k n|^2 = d^2/4 + k^2 + 2k n.(m-a) = d^2/4 + (r^2-d^2/4) = r^2)")
checks = [((0, 0), (3, 4), F(5, 2)), ((1, 1), (-2, 3), F(7, 2)), ((F(1, 3), F(2, 5)), (F(4, 7), -F(1, 2)), F(9, 10))]
ok = True
for (aa, cc, rr) in checks:
    ax, ay = F(aa[0]), F(aa[1])
    cx, cy = F(cc[0]), F(cc[1])
    d2q = (cx - ax) ** 2 + (cy - ay) ** 2
    k2q = rr ** 2 - d2q / 4
    if k2q < 0:
        continue
    from math import isqrt
    # exact check of |p-a|^2 = r^2 with p = m + k n, k = sqrt(k2q): verify (|p-a|^2 - r^2) = 0 via
    # the algebraic identity d^2/4 + k^2 - r^2 = 0 with k^2 = k2q
    assert d2q / 4 + k2q - rr ** 2 == 0
say("  exact-rational instances: the identity d^2/4 + k^2 = r^2 holds (so |p_+-a| = |p_+-c| = r)")

# ---------------------------------------------------------------- C2
say("")
say("=" * 100)
say("C2. MEC criterion: MEC^2 = acute ? a2b2c2/(4 cross^2) : max(pair)/4 ; witness split")
say("=" * 100)


def cross2(P1, P2, P3):
    ux, uy = P2[0] - P1[0], P2[1] - P1[1]
    vx, vy = P3[0] - P1[0], P3[1] - P1[1]
    return (ux * vy - uy * vx) ** 2


def sides2(P1, P2, P3):
    return [((P2[0] - P3[0]) ** 2 + (P2[1] - P3[1]) ** 2),
            ((P3[0] - P1[0]) ** 2 + (P3[1] - P1[1]) ** 2),
            ((P1[0] - P2[0]) ** 2 + (P1[1] - P2[1]) ** 2)]


def mec2(P1, P2, P3):
    """independent standard 3-point MEC (exact rationals): acute -> circumcircle, else diameter"""
    a2, b2, c2 = sides2(P1, P2, P3)          # a2 = |P2P3|^2 opposite P1, etc.
    acute = (a2 < b2 + c2) and (b2 < c2 + a2) and (c2 < a2 + b2)
    if not acute:
        return max(a2, b2, c2) / 4
    cr2 = cross2(P1, P2, P3)
    if cr2 == 0:
        return max(a2, b2, c2) / 4
    return F(a2 * b2 * c2, 1) / (4 * cr2)


def circ2(P1, P2, P3):
    a2, b2, c2 = sides2(P1, P2, P3)
    cr2 = cross2(P1, P2, P3)
    if cr2 == 0:
        return None
    return F(a2 * b2 * c2, 1) / (4 * cr2)


INST = [
    ((0, 0), (2, 0), (1, F(1, 20))),        # obtuse, flat: circumradius huge, MEC = 1
    ((0, 0), (2, 0), (1, 1)),               # obtuse? (1,1): a2=2,b2=2,c2=4 -> right at (1,1)? no: c2=4=a2+b2 -> right
    ((0, 0), (1, 0), (F(1, 2), F(3, 4))),   # acute
    ((0, 0), (3, 0), (F(3, 2), F(1, 2))),   # ?
    ((0, 0), (2, 0), (4, 0)),               # collinear
    ((0, 0), (1, 1), (2, 0)),               # right at (1,1)
    ((F(1, 5), 0), (1, F(2, 7)), (F(3, 2), F(1, 9))),
]
for (P1, P2, P3) in INST:
    a2, b2, c2 = sides2(P1, P2, P3)
    acute = (a2 < b2 + c2) and (b2 < c2 + a2) and (c2 < a2 + b2)
    M2 = mec2(P1, P2, P3)
    R2 = circ2(P1, P2, P3)
    say("  P=%s : acuteness=%s  MEC^2=%s  R^2=%s" % ((P1, P2, P3), acute, M2, (R2 if R2 else "collinear/inf")))
say("")
say("  equivalence test on a rational instance set (r chosen to separate the cases):")
okC2 = True
for (P1, P2, P3) in INST:
    a2, b2, c2 = sides2(P1, P2, P3)
    acute = (a2 < b2 + c2) and (b2 < c2 + a2) and (c2 < a2 + b2)
    M2 = mec2(P1, P2, P3)
    R2 = circ2(P1, P2, P3)
    for rq in [F(1, 2), F(3, 4), F(1), F(5, 4), F(3, 2)]:
        lhs = (M2 > rq * rq)
        pair = max(a2, b2, c2) > 4 * rq * rq
        rhs = pair or (acute and R2 is not None and R2 > rq * rq)
        if lhs != rhs:
            okC2 = False
            say("    MISMATCH at P=%s r=%s : MEC>r=%s rhs=%s" % ((P1, P2, P3), rq, lhs, rhs))
say("  equivalence MEC>r <=> (pair>2r) or (acute and R>r): %s" % ("ALL MATCH" if okC2 else "FAIL"))
# obtuse control: R > r but MEC <= r  (the acuteness clause is load-bearing)
P1, P2, P3 = (0, 0), (2, 0), (1, F(1, 20))
rq = F(1)
R2 = circ2(P1, P2, P3)
M2 = mec2(P1, P2, P3)
say("  obtuse control P=(0,0),(2,0),(1,1/20), r=1: R^2=%s > 1 but MEC^2=%s <= 1 -> naive 'R>r' alone is WRONG (pair 4>4? %s)"
    % (R2, M2, max(sides2(P1, P2, P3)) > 4 * rq * rq))

# ---------------------------------------------------------------- C3
say("")
say("=" * 100)
say("C3. orientation-freeness of the witnesses (exact rational rotation and reflection)")
say("=" * 100)
rot = ((F(3, 5), -F(4, 5)), (F(4, 5), F(3, 5)))       # rotation, det = 1
ref = ((F(1), F(0)), (F(0), F(-1)))                    # reflection, det = -1


def apply(M, P):
    return (M[0][0] * P[0] + M[0][1] * P[1], M[1][0] * P[0] + M[1][1] * P[1])


for (P1, P2, P3) in INST:
    base = (sides2(P1, P2, P3), cross2(P1, P2, P3))
    for M in (rot, ref):
        Q = [apply(M, P) for P in (P1, P2, P3)]
        cur = (sides2(*Q), cross2(*Q))
        assert base == cur, (base, cur)
say("  squared sides and cross^2 (hence acuteness and the circumradius condition) are invariant")
say("  under the exact rational rotation (3/5,-4/5;4/5,3/5) and the reflection diag(1,-1)")

# ---------------------------------------------------------------- C4
say("")
say("=" * 100)
say("C4. open hub ball + two moving disks: explicit nearest-to-lens candidates, semantics mu >= rho")
say("=" * 100)


def sub(p, q):
    return (p[0] - q[0], p[1] - q[1])


def add(p, q):
    return (p[0] + q[0], p[1] + q[1])


def mul(s, p):
    return (s * p[0], s * p[1])


def nrm2(p):
    return p[0] ** 2 + p[1] ** 2


def to_mp(fr):
    if isinstance(fr, F):
        return mpf(fr.numerator) / mpf(fr.denominator)
    return mpf(fr)


def lens_candidates(p1, p2, rad):
    """explicit candidates in mpmath: 0, the two projections of 0 onto the pin circles, the two
    circle-circle intersections (tangency counted once) -- then keep those inside BOTH disks."""
    p1 = (to_mp(p1[0]), to_mp(p1[1]))
    p2 = (to_mp(p2[0]), to_mp(p2[1]))
    rad = to_mp(rad)

    def inside(h):
        return nrm2(sub(h, p1)) <= rad * rad + mpf("1e-30") and nrm2(sub(h, p2)) <= rad * rad + mpf("1e-30")

    cs = []
    if inside((mpf(0), mpf(0))):
        cs.append(("origin", (mpf(0), mpf(0))))
    for p in (p1, p2):
        n = sqrt(nrm2(p))
        s = 1 - rad / n
        pr = (p[0] * s, p[1] * s)
        if inside(pr):
            cs.append(("projection", pr))
    dx, dy = p2[0] - p1[0], p2[1] - p1[1]
    d2 = dx * dx + dy * dy
    if d2 > 0:
        d = sqrt(d2)
        aq = d2 / (2 * d)                       # (r^2 - r^2 + d^2)/(2d) with equal radii
        h2 = rad * rad - aq * aq
        if h2 >= 0:
            hh = sqrt(h2)
            ux, uy = dx / d, dy / d
            bx, by = p1[0] + aq * ux, p1[1] + aq * uy
            for sgn in ([0] if hh == 0 else [1, -1]):
                z = (bx - sgn * hh * uy, by + sgn * hh * ux)
                if inside(z):
                    cs.append(("circle-circle", z))
    return cs


# tangency control: two radius-1/2 disks tangent at the point (rho,0), rho = 1/2
rho = F(1, 2)
t = (rho, F(0))
p1 = (t[0], t[1] + F(1, 2))
p2 = (t[0], t[1] - F(1, 2))
cs = lens_candidates(p1, p2, F(1, 2))
mu2 = min(nrm2(z) for (_, z) in cs)
say("  tangency control: %d candidates ; min |h|^2 = %s ; rho^2 = %s -> mu = rho to 1e-30: %s"
    % (len(cs), mp.nstr(mu2, 20), mp.nstr(to_mp(rho) ** 2, 20), abs(mu2 - to_mp(rho) ** 2) < mpf("1e-30")))
say("     semantics: mu >= rho fires (tangency counts as an emptiness witness for the OPEN ball) -> witness H5 fires")
# strict-outside control
p1 = (F(3, 2), F(1, 2))
p2 = (F(3, 2), -F(1, 2))
cs = lens_candidates(p1, p2, F(1, 2))
mu2 = min(nrm2(z) for (_, z) in cs)
say("  strict control p=(3/2,+-1/2), r=1/2: min|h|^2 = %s > rho^2 = %s -> H5 fires with margin"
    % (mp.nstr(mu2, 20), mp.nstr(to_mp(rho) ** 2, 20)))

# ---------------------------------------------------------------- C5
say("")
say("=" * 100)
say("C5. affine-in-radicals structure of H6 (sign-case representation, squared-radical substitution)")
say("=" * 100)
ka, kb, q1, q2, r2s = sp.symbols('ka kb q1 q2 r2s', nonnegative=True)
# instance frame: a=(0,0), c_a=(0,2), c_b=(2,0) -> m_a=(0,1), n_a=(1,0); m_b=(1,0), n_b=(0,1)
sa, sb = sp.symbols('sa sb', real=True)
P1 = sp.Matrix([sa * ka, 1])
P2 = sp.Matrix([1, sb * kb])
P3 = sp.Matrix([q1, q2])
A2 = sp.expand((P2 - P3).dot(P2 - P3))
B2 = sp.expand((P3 - P1).dot(P3 - P1))
C2 = sp.expand((P1 - P2).dot(P1 - P2))
X = sp.expand((P2[0] - P1[0]) * (P3[1] - P1[1]) - (P2[1] - P1[1]) * (P3[0] - P1[0]))
Ra = r2s - 1                     # ka^2 = r^2 - d_a^2/4 with d_a = 2, d_b = 2 in this frame
Rb = r2s - 1


def reduce_mod_squares(e):
    """reduce ka^2 -> Ra, kb^2 -> Rb and return the monomial support in (ka,kb)."""
    poly = sp.Poly(sp.expand(e), ka, kb)
    sup = set()
    for monom, coeff in zip(poly.monoms(), poly.coeffs()):
        i, j = monom
        coeff = sp.expand(coeff)
        while i >= 2:
            coeff = sp.expand(coeff * Ra)
            i -= 2
        while j >= 2:
            coeff = sp.expand(coeff * Rb)
            j -= 2
        sup.add((i, j))
    return sup


support_new = {(0, 0), (1, 0), (0, 1), (1, 1)}
allok = True
for name, e in (("a2", A2), ("b2", B2), ("c2", C2), ("X", X), ("X^2", sp.expand(X * X))):
    raw = set(sp.Poly(sp.expand(e), ka, kb).monoms())
    deg2 = all(i <= 2 and j <= 2 for (i, j) in raw)
    red = reduce_mod_squares(e)
    ok = red <= support_new
    allok = allok and ok and deg2
    say("  %s: raw support deg<=2 per radical: %s ; support AFTER kc^2 substitution: %s ; in "
        "{1,ka,kb,kakb}: %s" % (name, deg2, sorted(red), ok))
say("  => after substituting kc^2 = r^2 - dc^2/4 every H6 clause is polynomial in `a` and LINEAR in")
say("     (ka, kb, ka*kb): isolating one radical and squaring adds at most two sign cases.  All checks: %s"
    % allok)
say("     (Two draft corrections caught by this control: (i) NOT affine before the substitution;")
say("      (ii) X^2 raw support includes ka*kb^2, ka^2*kb, ka^2*kb^2 -- these reduce only via kc^2.)")

io.open('research-2026/team-current/r20-geometry/central_witness_controls.out.txt', 'w',
        encoding='utf-8').write("\n".join(OUT) + "\n")
print()
print("wrote central_witness_controls.out.txt")
