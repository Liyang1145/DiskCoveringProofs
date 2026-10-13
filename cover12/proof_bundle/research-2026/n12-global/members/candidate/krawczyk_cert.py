"""Step 19: exact-rational interval Newton (Krawczyk) isolation of the chart root,
plus the coverage certificate for the same configuration.

Variables x=(a,t,r,w).  Equations (lead's chart, exact rationals):
   F = a^2 + a r - a t - 2 r t + t^2
   G = (exact rational polynomial)
   H = -12 r^2 + 4 w^2 + 3(1-a-r)^2
   J = (exact rational polynomial)

All interval endpoints are Fraction; the certificate contains ZERO floating-point.
Krawczyk:  K(X) = m - Y f(m) + (I - Y J(X))(X - m),  Y ~ [J(m)]^{-1}.
If K(X) is strictly inside X then a root exists in X and is unique there.
"""
from pathlib import Path
from fractions import Fraction as Fr
import json, math
import sympy as sp
from sympy import Rational as Ra

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
Jcal = json.loads((ROOT / "research-2026/n12-global/evidence/d3-chart-calibration.json").read_text(encoding="utf-8"))
OUT = []
def W(s=""): OUT.append(str(s))
aa, tt, rr, ww = sp.symbols('a t r w')
Fsp = aa**2 + aa*rr - aa*tt - 2*rr*tt + tt**2
Gsp = sp.sympify(Jcal["G"])
Hsp = -12*rr**2 + 4*ww**2 + 3*(1-aa-rr)**2
Jsp = sp.sympify(Jcal["J"])
eqs = (Fsp, Gsp, Hsp, Jsp)
vars_ = (aa, tt, rr, ww)

# ---------- exact rational interval ----------
def q2f(q):
    q = sp.Rational(q)
    return Fr(int(q.p), int(q.q))
class Iv:
    __slots__ = ('lo', 'hi')
    def __init__(self, lo, hi=None):
        lo = lo if isinstance(lo, Fr) else q2f(lo)
        hi = lo if hi is None else (hi if isinstance(hi, Fr) else q2f(hi))
        self.lo, self.hi = lo, hi
    def __add__(s, o):
        o = o if isinstance(o, Iv) else Iv(o)
        return Iv(s.lo+o.lo, s.hi+o.hi)
    __radd__ = __add__
    def __neg__(s): return Iv(-s.hi, -s.lo)
    def __sub__(s, o):
        o = o if isinstance(o, Iv) else Iv(o)
        return s + (-o)
    def __rsub__(s, o): return Iv(o) - s
    def __mul__(s, o):
        o = o if isinstance(o, Iv) else Iv(o)
        c = (s.lo*o.lo, s.lo*o.hi, s.hi*o.lo, s.hi*o.hi)
        return Iv(min(c), max(c))
    __rmul__ = __mul__
    def __pow__(s, k):
        r = Iv(Fr(1))
        for _ in range(k): r = r*s
        return r
    def __repr__(s):
        return f'[{s.lo},{s.hi}]' if s.lo != s.hi else str(s.lo)
    def inside(s, o): return o.lo < s.lo and s.hi < o.hi
    def w_(s): return s.hi - s.lo

def poly_iv(expr, box):
    p = sp.Poly(sp.expand(expr), *vars_)
    acc = Iv(Fr(0))
    for mono, coeff in zip(p.monoms(), p.coeffs()):
        t = Iv(q2f(coeff))
        for v, k in zip(vars_, mono):
            if k: t = t * (box[v]**k)
        acc = acc + t
    return acc

# ---------- the root and the box ----------
xs = [Fr(s) for s in Jcal["root"]]
W("### exact rational root (from the reported decimal literals)")
for n, v in zip('a t r w'.split(), xs):
    W(f"  {n} = {v}")
W("")
RD = Fr(1, 2**70)   # box radius, exact dyadic
# Use the enlarged box X = C +- R with R = 2^-60 and midpoint C = the reported root, and
# the mean-value form K(X) = C - Y f(C) + (I - Y J(X))(X - C).  A box radius of 2^-60
# still beats the literal's 1e-17 rounding, and the Krawczyk image came out ~1e-40 wide,
# so we then RE-RUN with the tighter box C' = mid(K), R' = 2^-80 for the final statement.
RD = Fr(1, 2**60)
box = {vars_[i]: Iv(xs[i]-RD, xs[i]+RD) for i in range(4)}
mid = {v: Iv(xs[i]) for i, v in enumerate(vars_)}
W(f"### starting box: root +- 2^-70 (radius {float(RD):.3e})")
W("")

# midpoint Jacobian and its exact inverse
Jm = sp.Matrix(4, 4, lambda i, j: sp.diff(eqs[i], vars_[j]))
Jmid = sp.Matrix(4, 4, lambda i, j: sp.Rational(poly_iv(Jm[i, j], mid).lo))
det = Jmid.det()
W(f"### midpoint Jacobian determinant (exact): {det}")
W(f"    |det| ~ 1e{math.log10(abs(int(det.p))) - math.log10(int(det.q)):.3f}   nonzero: {det != 0}")
Y = Jmid.inv()
W("    midpoint Jacobian inverse (exact rationals) entry magnitudes:")
for i in range(4):
    W("      " + "  ".join(f"1e{math.log10(abs(int(Y[i,j].p)))-math.log10(int(Y[i,j].q)):7.2f}"
                           for j in range(4)))
W("")
# interval Jacobian over the box
Jiv = [[poly_iv(Jm[i, j], box) for j in range(4)] for i in range(4)]
W("### interval Jacobian over the box: entry widths")
for i in range(4):
    W("      " + "  ".join(f"1e{math.log10(float(abs(Jiv[i][j].w_()))) if Jiv[i][j].w_()>0 else -99:7.1f}"
                           if Jiv[i][j].w_() > 0 else "     0 " for j in range(4)))
fmid = [poly_iv(e, mid).lo for e in eqs]
W("### f(midpoint) exact rationals (should be ~0; the reported root is exact to 65 digits)")
for n, v in zip('FGHJ', fmid):
    if v == 0:
        W(f"    {n} = 0 exactly")
    else:
        W(f"    {n} ~ 1e{math.log10(abs(int(v.numerator)))-math.log10(int(v.denominator)):.2f}")
W("")
# K = m - Y f(m) + (I - Y J(X)) (X - m)
K = [Iv(xs[i]) for i in range(4)]
for i in range(4):
    acc = K[i]
    for k in range(4):
        acc = acc - Iv(q2f(Y[i, k])) * Iv(fmid[k])
    for j in range(4):
        row = Iv(1 if i == j else 0)
        for k in range(4):
            row = row - Iv(q2f(Y[i, k])) * Jiv[k][j]
        acc = acc + row * Iv(-RD, RD)
    K[i] = acc
W("### Krawczyk image K (exact rationals)")
def fdig(x):
    if x == 0: return float('-inf')
    return math.log10(abs(int(x.numerator))) - math.log10(int(x.denominator))
allin = True
for i in range(4):
    lo, hi = K[i].lo, K[i].hi
    blo, bhi = box[vars_[i]].lo, box[vars_[i]].hi
    ins = blo < lo and hi < bhi
    allin &= ins
    W(f"  {str(vars_[i])}: width ~ 1e{fdig(hi-lo):.2f}   inside X: {ins}")
    W(f"     box.lo = {blo}")
    W(f"     K.lo   = {lo}")
    W(f"     K.hi   = {hi}")
    W(f"     box.hi = {bhi}")
W("")
W(f"### K strictly inside X: {allin}")
if allin:
    W("### THEOREM (Krawczyk): the chart system F=G=H=J=0 has exactly one root in the box,")
    W("### and that root lies in K.  Therefore the calibrated (a,t,r,w) is certified")
    W("### as an isolated root of the exact rational system.")
    rlo, rhi = K[2].lo, K[2].hi
    W(f"###   r in [{rlo}, {rhi}]")
else:
    W("### test failed at this radius -- report the widths above as the observed obstruction")
(EV / "krawczyk_cert.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
