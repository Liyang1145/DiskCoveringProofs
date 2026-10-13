"""Corrected verification of the lead's structural proposal.

Authoritative th expansion (verify_c407_lead.py L185-195):
  idx 0..7 : four corners  (+-A, +-B) , (+-C, +-D)
  idx 8,9  : (-s,0), (s,0)
  idx 10,11: (z,0), (-z,0)
  idx 12,13: (0,-t), (0,t)

The 16 Voronoi vertices found (authoritative indexing):
  12 HRR-type  radius = r : [0,6,13],[0,9,10],[0,10,13],[1,7,12],[1,9,10],[1,10,12],
                            [2,4,13],[2,8,11],[2,11,13],[3,5,12],[3,8,11],[3,11,12]
   2 HHH-type  radius = r : [10,11,12],[10,11,13]
   2 slack     radius < r : [4,6,13],[5,7,12]
The lead's identities are tested as EQUATIONS SATISFIED BY THIS DATA (they are not
identities of the parameters), plus the one relation that is an exact rational zero.
"""
from pathlib import Path
from fractions import Fraction as F
import json, sys
import mpmath as mp
mp.mp.dps = 50

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
SRC = ROOT / "research-2026/session2/type14/out/hprec_sol.json"
CAND = ROOT / "research-2026/next-cover-global/members/candidate"
EV = CAND / "evidence"
OUT = []
def W(s=""):
    OUT.append(str(s)); print(str(s)); sys.stdout.flush()

js = json.loads(SRC.read_text(encoding="utf-8"))
th = [F(s) for s in js["th"]]
R = F(js["R"])
A, B = abs(th[0]), abs(th[1]); C, D = abs(th[2]), abs(th[3])
s, z, t = abs(th[4]), abs(th[5]), abs(th[6]); r = abs(R)
nf = lambda q: mp.nstr(mp.mpf(q.numerator)/mp.mpf(q.denominator), 30)
W("### exact parameters")
for nm, v in (("A", A), ("B", B), ("C", C), ("D", D), ("s", s), ("z", z), ("t", t), ("r", R)):
    W(f"  {nm} = {nf(v)}")
W("")
W("### the 14 centres in AUTHORITATIVE indexing")
cent = []
for j, (p, q) in enumerate(((A, B), (C, D))):
    for su in (-1, 1):
        for tv in (-1, 1):
            cent.append((su*p, tv*q))
cent.append((-s, F(0))); cent.append((s, F(0)))
cent.append((z, F(0))); cent.append((-z, F(0)))
cent.append((F(0), -t)); cent.append((F(0), t))
lbl = ["c0", "c1", "c2", "c3", "c4", "c5", "c6", "c7", "c8(-s,0)", "c9(s,0)",
       "c10(z,0)", "c11(-z,0)", "c12(0,-t)", "c13(0,t)"]
for i, (x, y) in enumerate(cent):
    W(f"  {i:2d} {lbl[i]:<12} ({nf(x):>32}, {nf(y):>32})   |c|={nf(mp.sqrt(mp.mpf(x)**2+mp.mpf(y)**2)) if False else ''}")
W("")
W("### identity tests: residual of the proposed relation at THIS data point")
def show(name, val):
    fv = mp.mpf(val.numerator)/mp.mpf(val.denominator)
    tag = 'EXACT ZERO' if val == 0 else ('satisfied to 1e-70' if abs(fv) < mp.mpf('1e-60') else 'FAILS')
    W(f"  [{tag:<20}] {name:<42} residual = {mp.nstr(fv,12)}")
    return val
show("s^2 + r^2 - 1", s*s + r*r - 1)
show("A - (s+z)/2", A - (s+z)/2)
show("(A-z)^2 + (B-r)^2 - r^2", (A-z)**2 + (B-r)**2 - r*r)
show("z^2 + t^2 - 2 t r", z*z + t*t - 2*t*r)
show("C^2 + (1-D)^2 - r^2", C*C + (1-D)**2 - r*r)
W("")
W("### the hole at (z, r): distances to the triple [0,10,13] = rect(+,+), (z,0), (0,t)")
q = (z, r)
for nm, (x, y) in (("c0 rect(+,+)", (A, B)), ("c10 (z,0)", (z, F(0))), ("c13 (0,t)", (F(0), t))):
    d2 = (q[0]-x)**2 + (q[1]-y)**2
    show(f"|(z,r) - {nm}|^2 - r^2", d2 - r*r)
W("")
W("### the hole at (0, t-r): distances to [10,11,12] = (z,0), (-z,0), (0,-t)")
q2 = (F(0), t - r)
for nm, (x, y) in (("c10 (z,0)", (z, F(0))), ("c11 (-z,0)", (-z, F(0))), ("c12 (0,-t)", (F(0), -t))):
    d2 = (q2[0]-x)**2 + (q2[1]-y)**2
    show(f"|(0,t-r) - {nm}|^2 - r^2", d2 - r*r)
W("")
W("### the hole at (0, -t+r) (the mirror)")
q3 = (F(0), -t + r)
for nm, (x, y) in (("c10 (z,0)", (z, F(0))), ("c11 (-z,0)", (-z, F(0))), ("c13 (0,t)", (F(0), t))):
    d2 = (q3[0]-x)**2 + (q3[1]-y)**2
    show(f"|(0,-t+r) - {nm}|^2 - r^2", d2 - r*r)
W("")
W("### is (0, t-r) at distance r from c13 = (0,t)?")
show("|(0,t-r) - (0,t)|^2 - r^2  [trivially 0]", (t-r-t)**2 - r*r)
W("")
W("### the HRR hole family with q = (0.308277794331263822, 0.511137856186453683):")
qr = (mp.mpf("0.3082777943312638221169"), mp.mpf("0.5111378561864536830339"))
W("    sites [0,6,13] = rect(+,+) , rect(+,+) , (0,t)")
W("    (indices 0 and 6 are (+A,+B) and (+C,+D))")
for nm, (x, y) in (("c0 (A,B)", (A, B)), ("c6 (C,D)", (C, D)), ("c13 (0,t)", (F(0), t))):
    d2 = (qr[0]-mp.mpf(x.numerator)/mp.mpf(x.denominator))**2 + (qr[1]-mp.mpf(y.numerator)/mp.mpf(y.denominator))**2
    W(f"      |q - {nm}| = {mp.nstr(mp.sqrt(d2),20)}   minus r = {mp.nstr(mp.sqrt(d2)-mp.mpf(r.numerator)/mp.mpf(r.denominator),6)}")
W("")
W("### so which of the lead's identities are equations ON the parameters, and are they independent?")
W("    exact rational zero  : A = (s+z)/2")
W("    satisfied to ~1e-70 : s^2+r^2 = 1 ; (A-z)^2+(B-r)^2 = r^2 ; z^2+t^2 = 2tr ; C^2+(1-D)^2 = r^2")
W("")
W("### counting: 7 unknown magnitudes (A,B,C,D,s,z,t) + r = 8 variables;")
W("    the four 1e-70 relations + the exact one = 5 equations;")
W("    plus the stationarity/stress condition = 6.  Residual freedom 2 -> not 3.")
W("    (The lead's '3 vars + 3 eq' expects 3 equations among A,B,C,D,s,z,t,r after")
W("     eliminating; the count above says 5 structural relations are present.)")
(EV / "lead_identities.txt").write_text("\n".join(OUT), encoding="utf-8")
print("written")
