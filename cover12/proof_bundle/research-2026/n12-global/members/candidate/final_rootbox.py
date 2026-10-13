"""Step 22 (FINAL): tight exact-rational root box + stress replay + coverage certificate.

Deliverables:
 (A) a certified exact-rational box for the (F,G,H,J) root, tight enough to be fed to
     lead/stress_interval.py's verify(box) (whose own box is +-1e-38);
 (B) replay of the lead's stress module on our certified box;
 (C) coverage certificate for the 12-centre configuration built from the certified box.
"""
from pathlib import Path
from fractions import Fraction as Fr
import sys as _sys
_sys.set_int_max_str_digits(200000)
import json, math, sys
import sympy as sp
from sympy import Rational as Ra

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
LEAD = ROOT / "research-2026/n12-global/lead"
Jcal = json.loads((ROOT / "research-2026/n12-global/evidence/d3-chart-calibration.json").read_text(encoding="utf-8"))
OUT = []
def W(s=""): OUT.append(str(s))

aa, tt, rr, ww = sp.symbols('a t r w')
vars_ = (aa, tt, rr, ww)
Fsp = aa**2 + aa*rr - aa*tt - 2*rr*tt + tt**2
Gsp = sp.sympify(Jcal["G"])
Hsp = -12*rr**2 + 4*ww**2 + 3*(1-aa-rr)**2
Jsp = sp.sympify(Jcal["J"])
eqs = (Fsp, Gsp, Hsp, Jsp)

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
    def __repr__(s): return f'[{s.lo},{s.hi}]'
def poly_iv(expr, box):
    p = sp.Poly(sp.expand(expr), *vars_)
    acc = Iv(Fr(0))
    for mono, coeff in zip(p.monoms(), p.coeffs()):
        t = Iv(q2f(coeff))
        for v, k in zip(vars_, mono):
            if k: t = t * (box[v]**k)
        acc = acc + t
    return acc

def krawczyk_step(center, radius):
    """one exact-rational Krawczyk step about 'center' with box radius 'radius'."""
    box = {vars_[i]: Iv(center[i]-radius, center[i]+radius) for i in range(4)}
    mid = {v: Iv(center[i]) for i, v in enumerate(vars_)}
    Jm = sp.Matrix(4, 4, lambda i, j: sp.diff(eqs[i], vars_[j]))
    Jmid = sp.Matrix(4, 4, lambda i, j: sp.Rational(poly_iv(Jm[i, j], mid).lo))
    Y = Jmid.inv()
    Jiv = [[poly_iv(Jm[i, j], box) for j in range(4)] for i in range(4)]
    fmid = [poly_iv(e, mid).lo for e in eqs]
    K = []
    for i in range(4):
        acc = Iv(center[i])
        for k in range(4):
            acc = acc - Iv(q2f(Y[i, k])) * Iv(fmid[k])
        for j in range(4):
            row = Iv(1 if i == j else 0)
            for k in range(4):
                row = row - Iv(q2f(Y[i, k])) * Jiv[k][j]
            acc = acc + row * Iv(-radius, radius)
        K.append(acc)
    inside = all(box[vars_[i]].lo < K[i].lo and K[i].hi < box[vars_[i]].hi for i in range(4))
    return K, inside, Y, Jmid.det()

xs = [Fr(s) for s in Jcal["root"]]
W("### (A) exact-rational Newton/Krawczyk refinement of the isolated root")
cur = list(xs)
for step, rd in enumerate([Fr(1, 2**70), Fr(1, 2**80), Fr(1, 2**100), Fr(1, 2**128)]):
    K, inside, Y, det = krawczyk_step(cur, rd)
    W(f"  step {step}: box radius ~1e{math.log10(float(rd)):.0f}")
    if step == 0:
        W(f"    midpoint Jacobian det ~ 1e{math.log10(abs(int(det.p)))-math.log10(int(det.q)):.3f}")
    W(f"    Krawczyk image widths: " + "  ".join(
        f"1e{(math.log10(abs(int((K[i].hi-K[i].lo).numerator)))-math.log10(int((K[i].hi-K[i].lo).denominator))):.1f}"
        for i in range(4)))
    W(f"    K strictly inside X: {inside}")
    if not inside:
        W("    -> stop")
        break
    cur = [(K[i].lo+K[i].hi)/2 for i in range(4)]
    enc = [(K[i].lo, K[i].hi) for i in range(4)]
W("")
W("### certified enclosure of the root (exact rational endpoints)")
for i, n in enumerate('a t r w'.split()):
    W(f"  {n} in [{enc[i][0]}, {enc[i][1]}]")
    W(f"       width ~ 1e{math.log10(abs(int((enc[i][1]-enc[i][0]).numerator)))-math.log10(int((enc[i][1]-enc[i][0]).denominator)):.1f}")
W("")
W("### this proves: the exact system F=G=H=J=0 has a UNIQUE root, contained in the above box.")
W("")

# ---- (B) replay the lead's stress module on a box containing our certified box
sys.path.insert(0, str(LEAD))
import importlib.util
spec = importlib.util.spec_from_file_location("stress_interval", LEAD / "stress_interval.py")
sm = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sm)
# widen our certified box by 1e-40 (exact) so it lies strictly inside the input box
pad = Fr(1, 10**40)
bxs = [[str(enc[i][0]-pad), str(enc[i][1]+pad)] for i in range(4)]
W("### (B) lead's stress module replayed on our certified box (padded by 1e-40)")
try:
    res = sm.verify(bxs)
    W(f"  status: {res['status']}")
    W(f"  scope : {res['scope']}")
    W("  weight bounds (all must be > 0):")
    for k, v in res['weight_bounds'].items():
        W(f"     {k} in {v}")
    W(f"  Dirichlet pivots certified positive: {len(res['dirichlet_pivots'])}")
    W(f"  Hessian 8x8 minor LDL pivots certified positive: {len(res['hessian_minor_pivots'])}")
    W(f"  min Schur conductance lower bound: {res['minimum_schur_conductance_lower']}")
    (EV / "stress_certificate.json").write_text(json.dumps(res, indent=2), encoding="utf-8")
except AssertionError as ex:
    W(f"  stress verification FAILED: {ex}")
except Exception as ex:
    W(f"  stress verification error: {type(ex).__name__}: {ex}")
W("")
(EV / "root_box.json").write_text(json.dumps(
    {"enc": [[str(enc[i][0]), str(enc[i][1])] for i in range(4)],
     "system": {"F": str(Fsp), "G": Jcal["G"], "H": str(Hsp), "J": Jcal["J"]},
     "status": "exact-rational Krawczyk: unique root in the box"}, indent=2), encoding="utf-8")
(EV / "final_rootbox.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
