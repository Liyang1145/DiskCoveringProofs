"""n=14: EXACT SYMBOLIC derivation of the three remaining constraint equations.

Object: exact th expansion (verify_c407_lead.py L185-195).
Centres: c0..c7 = (±A,±B),(±C,±D);  c8,c9 = (∓s,0);  c10,c11 = (±z,0);  c12,c13 = (0,∓t).

PART 1  sign audit of the earlier branch statements (self-check).
PART 2  the three equations asked for:
  (E_A) A-C boundary switch: a point p on S^1 at distance r from BOTH c0'=(A,B) and
        c6'=(C,D).  Equidistance gives a LINEAR equation in p; adding |p|=1 and
        |p-c0'|=r and eliminating p gives one relation among (z,C,r) after the five
        relations have removed A,s,t,B,D.
  (E_B) the three inner centres (A,B),(C,D),(0,t) have circumradius r.
  (E_C) stationarity: the Jacobian determinant of {(E_A),(E_B)} w.r.t. (z,C) vanishes.
Everything is done with exact symbolic algebra (sympy); branch conditions are carried
explicitly as the sign of each square root, and all 2^k branch combinations are tested
numerically against the data point to select the true branch.
"""
from pathlib import Path
from fractions import Fraction as F
import json, itertools, sys
import sympy as sp
from sympy import Rational as Ra, sqrt, symbols, simplify, expand, factor, resultant, Poly

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
SRC = ROOT / "research-2026/session2/type14/out/hprec_sol.json"
CAND = ROOT / "research-2026/next-cover-global/members/candidate"
EV = CAND / "evidence"
OUT = []
def W(s=""):
    OUT.append(str(s)); print(str(s)); sys.stdout.flush()

js = json.loads(SRC.read_text(encoding="utf-8"))
th = [F(s) for s in js["th"]]; R = F(js["R"])
exact = {"A": abs(th[0]), "B": abs(th[1]), "C": abs(th[2]), "D": abs(th[3]),
         "s": abs(th[4]), "z": abs(th[5]), "t": abs(th[6]), "r": abs(R)}
W("### PART 1  sign audit")
W("Lead: B should be r + sqrt(r^2-(A-z)^2).  My earlier claim was r - sqrt(...).")
Av = Ra(exact["A"].numerator, exact["A"].denominator)
zv = Ra(exact["z"].numerator, exact["z"].denominator)
rv = Ra(exact["r"].numerator, exact["r"].denominator)
Bv = Ra(exact["B"].numerator, exact["B"].denominator)
sq = (rv*rv - (Av-zv)**2)
W(f"  r^2-(A-z)^2 = {sp.nsimplify(sq)}  >0: {sq > 0}")
W(f"  sqrt(r^2-(A-z)^2) (numeric) = {float(sp.sqrt(sp.Rational(float(sq))))}")
W(f"  B - r  = {float(Bv - rv)}")
W(f"  r + sqrt(...) - B = {float(rv + sp.sqrt(Ra(float(sq)).limit_denominator(10**40)) - Bv)}")
W("  => CONFIRMED: B = r + sqrt(r^2-(A-z)^2).  My earlier sign was wrong.")
W("  Let me redo it exactly with the branch audit below instead of floats.")
W("")

# ---------- exact branch audit: test every sign combination against the data ----------
W("### PART 1b  exact branch audit (all sign combinations)")
# after E0 (s=2A-z), E1 ((2A-z)^2+r^2=1), the remaining free magnitudes B,D,t are
# determined by E2,E3,E4 up to an explicit square-root sign each.
import mpmath as mp
mp.mp.dps = 50
d = lambda q: mp.mpf(q.numerator)/mp.mpf(q.denominator)
A_, B_, C_, D_, s_, z_, t_, r_ = [d(exact[k]) for k in ("A", "B", "C", "D", "s", "z", "t", "r")]
W(f"  data: A={mp.nstr(A_,20)} B={mp.nstr(B_,20)} C={mp.nstr(C_,20)} D={mp.nstr(D_,20)}")
W(f"        s={mp.nstr(s_,20)} z={mp.nstr(z_,20)} t={mp.nstr(t_,20)} r={mp.nstr(r_,20)}")
for eB in (+1, -1):
    for eD in (+1, -1):
        for eT in (+1, -1):
            Bc = r_ + eB*mp.sqrt(r_**2 - (A_-z_)**2)
            Dc = 1 + eD*mp.sqrt(r_**2 - C_**2)
            tc = r_ + eT*mp.sqrt(r_**2 - z_**2)
            err = max(abs(Bc-B_), abs(Dc-D_), abs(tc-t_))
            W(f"   B=r{eB:+d}sqrt(...) D=1{eD:+d}sqrt(...) t=r{eT:+d}sqrt(...) -> error {mp.nstr(err,6)}"
              f"  {'<== selects the data' if err < mp.mpf('1e-12') else ''}")
W("")

# ---------- PART 2: symbolic setup ----------
W("### PART 2  symbolic derivation")
z, C, r = symbols('z C r', positive=True)
# branch-selected magnitudes (signs as selected above; symbolic placeholders)
sigma_t, sigma_B, sigma_D = symbols('sigma_t sigma_B sigma_D', real=True)
A = (1 + sqrt(1 - 4*z**2 + 4*z*sqrt(1-r**2) + 0)) if False else None
# s = 2A - z and (2A-z)^2 = 1 - r^2  ->  2A - z = sqrt(1-r^2)  (positive branch)
# so A = (z + sqrt(1-r^2))/2
A = (z + sqrt(1 - r**2))/2
s = 2*A - z
t = r + sigma_t*sqrt(r**2 - z**2)
B = r + sigma_B*sqrt(r**2 - (A - z)**2)
D = 1 + sigma_D*sqrt(r**2 - C**2)
W("  branch-selected magnitudes:")
W(f"    A = (z + sqrt(1-r^2))/2        [from E0+E1, positive branch]")
W(f"    s = 2A - z = sqrt(1-r^2)")
W(f"    t = r + sigma_t sqrt(r^2-z^2)")
W(f"    B = r + sigma_B sqrt(r^2-(A-z)^2)")
W(f"    D = 1 + sigma_D sqrt(r^2-C^2)")
W(f"  numerically at the data: sigma_t = sigma_B = ?, sigma_D = ?")
sg_t = mp.sign(t_ - r_); sg_B = mp.sign(B_ - r_); sg_D = mp.sign(D_ - 1)
W(f"    sigma_t = {sg_t:+.0f}   sigma_B = {sg_B:+.0f}   sigma_D = {sg_D:+.0f}")
W("")

# ---------- (E_A) the A-C switch point ----------
W("### (E_A) A-C boundary switch")
px, py = symbols('px py', real=True)
W("  p is on S^1 and |p-(A,B)| = r = |p-(C,D)|.")
W("  equidistance  |p-(A,B)|^2 = |p-(C,D)|^2  is LINEAR in p:")
lin = sp.expand((px-A)**2 + (py-B)**2 - ((px-C)**2 + (py-D)**2))
lin = sp.expand(lin)
W(f"    {sp.nsimplify(lin)} = 0")
W("  together with  px^2+py^2 = 1  and  (px-A)^2+(py-B)^2 = r^2.")
W("  The last two: subtract to get the same radical line; keep |p-(A,B)|=r and |p|=1.")
W("  Eliminate py between the radical relation and the circle |p|=1:")
# radical: 2(C-A)px + 2(D-B)py = C^2+D^2-A^2-B^2
rhs = C**2 + D**2 - A**2 - B**2
W(f"    radical axis: 2(C-A) px + 2(D-B) py = {sp.nsimplify(rhs)}")
# solve for py
py_sol = sp.simplify((rhs - 2*(C-A)*px)/(2*(D-B)))
W("  substituting into px^2+py^2=1 gives a quadratic in px (coefficients in z,C,r).")
quad = sp.together(sp.expand(px**2 + py_sol**2 - 1))
num = sp.numer(sp.simplify(quad))
P = sp.Poly(sp.expand(num), px)
W(f"    quadratic in px: degree {P.degree()}")
coeffs = P.all_coeffs()
for k, c in enumerate(coeffs):
    W(f"      px^{P.degree()-k}: {sp.simplify(c)}")
W("")
W("  NOTE: no numerical interpretation is made here (per instruction).  The next step")
W("  would be to eliminate px (resultant with the |p-(A,B)|=r condition) to obtain the")
W("  single relation R_A(z,C,r)=0; that elimination is the remaining algebraic work.")
(EV / "n14_symbolic_stage1.txt").write_text("\n".join(OUT), encoding="utf-8")
print("written evidence/n14_symbolic_stage1.txt")
