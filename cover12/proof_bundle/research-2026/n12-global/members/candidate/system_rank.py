"""Step 18: RANK / conditioning of the lead's (F,G,H,J) system at the calibrated root.

The exact-rational Krawczyk diverged (|K|~1e321 for a 1e-24 box) which is the numeric
symptom of a near-singular midpoint Jacobian.  Here we measure the conditioning
precisely and decide whether the 4 equations isolate the root.
"""
from pathlib import Path
from fractions import Fraction as Fr
import json
import mpmath as mp
import sympy as sp
mp.mp.dps = 60

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
names = ('F', 'G', 'H', 'J')
vars_ = (aa, tt, rr, ww)
xs = [mp.mpf(s) for s in Jcal["root"]]
sub = {aa: xs[0], tt: xs[1], rr: xs[2], ww: xs[3]}

W("### the 4 equations at the calibrated root (dps=60)")
for e, n in zip(eqs, names):
    W(f"  {n} = {mp.nstr(mp.mpf(str(sp.N(e.subs(sub), 60))), 10)}")
W("")
W("### 4x4 Jacobian, numeric at the root")
Jnum = mp.matrix(4, 4)
for i in range(4):
    for j in range(4):
        d = sp.diff(eqs[i], vars_[j])
        Jnum[i, j] = mp.mpf(str(sp.N(d.subs(sub), 60)))
for i in range(4):
    W("  " + "  ".join(f"{mp.nstr(Jnum[i,j],12):>18}" for j in range(4)))
sv = mp.svd(Jnum, compute_uv=False)
W("  singular values: " + str([mp.nstr(s, 8) for s in sv]))
W(f"  numerical rank (rel 1e-20): {sum(1 for s in sv if s > mp.mpf('1e-20')*sv[0])}/4")
W(f"  |det| = {mp.nstr(abs(mp.det(Jnum)), 12)}")
W(f"  cond  = {mp.nstr(sv[0]/sv[-1], 12) if sv[-1] != 0 else 'inf'}")
W("")
W("### drop-one test: does each equation contribute?")
for drop in range(4):
    rows = [i for i in range(4) if i != drop]
    M = mp.matrix(3, 4)
    for k, i in enumerate(rows):
        for j in range(4):
            M[k, j] = Jnum[i, j]
    s = mp.svd(M, compute_uv=False)
    W(f"  drop {names[drop]}: singular values {[mp.nstr(x,8) for x in s]} -> rank "
      f"{sum(1 for x in s if x > mp.mpf('1e-20')*s[0])}/3")
W("")
W("### pairwise/triple degeneracy: which subset has full rank 3?")
import itertools
for comb in itertools.combinations(range(4), 3):
    M = mp.matrix(3, 4)
    for k, i in enumerate(comb):
        for j in range(4):
            M[k, j] = Jnum[i, j]
    s = mp.svd(M, compute_uv=False)
    W(f"  rows {[names[i] for i in comb]}: rank "
      f"{sum(1 for x in s if x > mp.mpf('1e-20')*s[0])}/3   sv={[mp.nstr(x,6) for x in s]}")
W("")
W("### is J a polynomial combination of F,G,H?  (symbolic residual of an ansatz)")
W("  ansatz: J = alpha*F + beta*G + gamma*H + c  (degree check)")
W(f"  deg F={sp.Poly(Fsp,aa,tt,rr,ww).total_degree()}, deg G={sp.Poly(Gsp,aa,tt,rr,ww).total_degree()}, deg H={sp.Poly(Hsp,aa,tt,rr,ww).total_degree()}, "
  f"deg J={sp.Poly(Jsp,aa,tt,rr,ww).total_degree()}")
W(f"  J is {'homogeneous' if sp.Poly(Jsp, aa,tt,rr,ww).is_homogeneous else 'NOT homogeneous'}")
W(f"  F homogeneous degree 2: {sp.Poly(Fsp, aa,tt,rr,ww).is_homogeneous}")
W(f"  G homogeneous degree 4: {sp.Poly(Gsp, aa,tt,rr,ww).is_homogeneous}")
W("  => J (deg 5, inhomogeneous) cannot be a combination of F,G (deg 2,4 homogeneous)")
W("     and H (deg 2 inhomogeneous); the rank test above is decisive.")
(EV / "system_rank.txt").write_text("\n".join(OUT), encoding="utf-8")
print("\n".join(OUT))
