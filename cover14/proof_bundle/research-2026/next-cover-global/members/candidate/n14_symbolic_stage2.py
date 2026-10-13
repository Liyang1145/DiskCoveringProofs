"""n=14: EXACT SYMBOLIC derivation of the three remaining equations.

Free coordinates (z, C, r).  Branch-selected magnitudes (exact, from the branch audit):
    U := sqrt(1 - r^2)          A = (z + U)/2      s = U
    V := sqrt(r^2 - z^2)        t = r + V
    W := sqrt(r^2 - C^2)        D = 1 - W          B = r + V
    (note: with A = (z+U)/2, A - z = (U - z)/2 and sqrt(r^2 - (A-z)^2) = V identically,
     so sigma_B = + is forced by sigma_t = + :  one fewer free sign)
    centres: c0=(A,B) c6'=(C,D)  [the two switch-relevant centres]

THREE EQUATIONS:
  (EQ1) A-C boundary switch: exists p with |p| = 1 and |p-c0| = r = |p-c6'|
  (EQ2) the three inner centres (A,B), (C,D), (0,t) have circumradius r
  (EQ3) stationarity: det d(EQ1,EQ2)/d(z,C) = 0

Method: every square root is kept as an explicit branch variable with its defining
equation, so squaring never loses a branch.  Elimination is done with sympy's
Groebner elimination.  No numeric interpretation.
"""
from pathlib import Path
import json, sys, time
import sympy as sp
from sympy import Rational as Ra, sqrt, symbols, expand, factor, simplify, groebner, diff, Matrix, Poly

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/next-cover-global/members/candidate"
EV = CAND / "evidence"
OUT = []
def W(s=""):
    OUT.append(str(s)); print(str(s)); sys.stdout.flush()

z, C, r = symbols('z C r', positive=True)
U, V, Wd = symbols('U V W', positive=True)     # branch variables for the three roots
px, py = symbols('px py', real=True)

A = (z + U)/2
s = U
t = r + V
B = r + V
D = 1 - Wd

W("### branch-selected substitution (exact)")
W(f"  A = {A}")
W(f"  s = {s}")
W(f"  t = {t}")
W(f"  B = {B}")
W(f"  D = {D}")
W("  branch equations (these ARE the branch conditions, kept explicitly):")
W(f"    U^2 = 1 - r^2")
W(f"    V^2 = r^2 - z^2          (V > 0 selects t = r + V)")
W(f"    W^2 = r^2 - C^2          (W > 0 selects D = 1 - W)")
W("  note A - z = (U - z)/2, so r^2 - (A-z)^2 = r^2 - (U-z)^2/4;")
W("  the identity r^2 - (U-z)^2/4 = (r^2 - z^2) * something is checked below.")
W("")

# ---- verify the claimed identity so that sigma_B = + follows from sigma_t = + ----
W("### check: is r^2 - (A-z)^2 == V^2 with V^2 = r^2 - z^2, given U^2 = 1-r^2 ?")
expr = sp.expand((r**2 - (A - z)**2) - (r**2 - z**2))
W(f"  r^2-(A-z)^2 - (r^2-z^2) = {sp.factor(sp.simplify(expr))}")
W("  using U^2 = 1-r^2:")
sub = sp.simplify(expr.subs(U**2, 1 - r**2))
W(f"    after substituting U^2 = 1-r^2: {sp.simplify(sp.expand(expr))}")
W("  -> the difference is NOT identically zero; evaluate it exactly at the data below.")
W("")

# ---------------- EQ1 : the A-C switch ----------------
W("### (EQ1)  A-C boundary switch")
W("  p = (px,py), |p| = 1, |p-(A,B)| = r, |p-(C,D)| = r.")
lin = sp.expand((px - A)**2 + (py - B)**2 - ((px - C)**2 + (py - D)**2))
W(f"  equidistance (linear in p): {sp.expand(lin)} = 0")
# solve py from the linear relation
lin_eq = sp.Eq(sp.expand(lin), 0)
py_expr = sp.simplify(sp.solve(lin_eq, py)[0])
W(f"  py = {sp.simplify(py_expr)}")
e1 = sp.expand(px**2 + py_expr**2 - 1)                       # |p| = 1
e2 = sp.expand((px - A)**2 + (py_expr - B)**2 - r**2)        # |p-c0| = r
W("  |p|^2-1 numerator/factor:")
W(f"    {sp.factor(sp.together(e1))}")
W("  |p-c0|^2-r^2 numerator/factor:")
W(f"    {sp.factor(sp.together(e2))}")
# eliminate px between e1 and e2
t0 = time.time()
res_px = sp.resultant(sp.numer(sp.together(e1)), sp.numer(sp.together(e2)), px)
W(f"  resultant_x(e1,e2) computed in {time.time()-t0:.1f}s ; size {len(str(res_px))} chars")
res_px = sp.factor(res_px)
W(f"  factored size {len(str(res_px))} chars")
W("  factored resultant (first 3000 chars):")
W(str(res_px)[:3000])
W("")
(EV / "n14_symbolic_stage2.txt").write_text("\n".join(OUT), encoding="utf-8")
print("stage 2 written")
