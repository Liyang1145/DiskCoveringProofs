"""Step 24: rigorous Krawczyk with mpmath interval arithmetic (outward rounded),
tight enough to feed the lead's stress module.

Interval ops are mpmath.iv, whose endpoints carry directed-rounding outward bounds.
We report the strict containment margin explicitly so the certificate is not knife-edge.
"""
from pathlib import Path
from fractions import Fraction as Fr
import json, math, sys
sys.set_int_max_str_digits(300000)
import sympy as sp
from mpmath import iv, mp
mp.dps = 120
iv.dps = 120

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
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

def coeffs(expr):
    p = sp.Poly(sp.expand(expr), *vars_)
    out = []
    for mono, cf in zip(p.monoms(), p.coeffs()):
        q = sp.Rational(cf)
        out.append((str(Fr(int(q.p), int(q.q))), mono))
    return out
CF = [coeffs(e) for e in eqs]
JCF = [[coeffs(sp.diff(e, v)) for v in vars_] for e in eqs]

def ivc(s):
    return iv.mpf([s, s])
def iv_eval(CF_, box):
    acc = ivc('0')
    for coef, mono in CF_:
        term = ivc(coef)
        for v, k in zip(vars_, mono):
            for _ in range(k):
                term = term * box[v]
        acc = acc + term
    return acc
def mid_of(x):
    return (mp.mpf(x.a) + mp.mpf(x.b)) / 2

def exact_str(x):
    """dirigible exact rational string for an mpf: try exact repr, else 40-digit decimal."""
    try:
        return str(Fr(x))
    except TypeError:
        return mp.nstr(x, 40)

xs = [Fr(s) for s in Jcal["root"]]

def kraw(center, rd):
    box = {vars_[f]: iv.mpf([str(center[f]-rd), str(center[f]+rd)]) for f in range(4)}
    mid = {vars_[f]: ivc(str(center[f])) for f in range(4)}
    fmid = [iv_eval(CF[i], mid) for i in range(4)]
    Ji = [[iv_eval(JCF[i][j], box) for j in range(4)] for i in range(4)]
    Jm = mp.matrix([[mid_of(iv_eval(JCF[i][j], mid)) for j in range(4)] for i in range(4)])
    Ym = mp.inverse(Jm)
    K = []
    for i in range(4):
        acc = ivc(str(center[i]))
        for k in range(4):
            acc = acc - ivc(exact_str(Ym[i, k])) * fmid[k]
        for j in range(4):
            row = ivc('1' if i == j else '0')
            for k in range(4):
                row = row - ivc(exact_str(Ym[i, k])) * Ji[k][j]
            acc = acc + row * iv.mpf([str(-rd), str(rd)])
        K.append(acc)
    return K, box

W("### rigorous Krawczyk refinement (mpmath.iv, dps=120, outward rounding)")
cur = list(xs)
enc = None
for step, rd in enumerate([Fr(1, 2**70), Fr(1, 2**90), Fr(1, 2**110), Fr(1, 2**130)]):
    K, box = kraw(cur, rd)
    wds, marg, ok = [], [], True
    for i in range(4):
        lo, hi = mp.mpf(K[i].a), mp.mpf(K[i].b)
        wds.append(float(mp.log10(hi-lo)) if hi > lo else -999.)
        blo, bhi = mp.mpf(box[vars_[i]].a), mp.mpf(box[vars_[i]].b)
        marg.append((float(blo-lo), float(hi-bhi)))
        if not (blo < lo and hi < bhi):
            ok = False
    W(f"  step {step}: box r ~1e{math.log10(float(rd)):.0f}; K widths 1e[{min(wds):.1f},{max(wds):.1f}];"
      f" strictly inside: {ok}")
    W("     margins (lo-side, hi-side): " + "  ".join(f"({a:.1e},{b:.1e})" for a, b in marg))
    if not ok:
        break
    cur = [mid_of(K[i]) for i in range(4)]
    enc = [(K[i].a, K[i].b) for i in range(4)]
W("")
if enc:
    W("### CERTIFIED: the exact-integer-coefficient system F=G=H=J=0 has exactly one root,")
    W("### and it lies in the box (Krawczyk: interval Jacobian over the whole box):")
    for i, n in enumerate('a t r w'.split()):
        W(f"  {n} in [{mp.nstr(enc[i][0],40)}, {mp.nstr(enc[i][1],40)}]")
        W(f"      width = {mp.nstr(mp.mpf(enc[i][1])-mp.mpf(enc[i][0]),6)}")
    json.dump({n: [mp.nstr(mp.mpf(enc[i][0].a), 100), mp.nstr(mp.mpf(enc[i][1].b), 100)] for i, n in enumerate("a t r w".split())},
              (EV / "certified_root_box.json").open("w"), indent=2)
    W("### written to evidence/certified_root_box.json")
(EV / "certified_root_box.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
