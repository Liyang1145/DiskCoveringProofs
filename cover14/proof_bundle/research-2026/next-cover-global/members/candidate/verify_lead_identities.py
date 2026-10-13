"""Verification of the lead's proposed numeric identities against the EXACT th expansion.

Parameters (lead): A=th0, B=|th1|, C=|th2|, D=|th3|, s=|th4|, z=|th5|, t=|th6|, r=R.
Candidate identities proposed:
  H1  s^2 + r^2 = 1
  H2  A = (s + z)/2
  H3  (A - z)^2 + (B - r)^2 = r^2
  H4  z^2 + t^2 = 2 t r
  H5  C^2 + (1 - D)^2 = r^2          [lead wrote C^2+(1-D)^2 = r^2]
  H6  three holes at distance r from a triple (structural)
Everything computed from exact rationals (no floats in the decision).
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
A, Bv, Cv, Dv, sv, zv, tv = [abs(v) for v in th[:7]]
W("### parameters (absolute values of th, exact rationals)")
names = [("A", A), ("B", Bv), ("C", Cv), ("D", Dv), ("s", sv), ("z", zv), ("t", tv), ("r", R)]
for nm, v in names:
    W(f"  {nm} = {mp.nstr(mp.mpf(v.numerator)/mp.mpf(v.denominator), 30)}")
W("")
W("### R (from the file) vs r")
W(f"  R = {R}")
W(f"  = {mp.nstr(mp.mpf(R.numerator)/mp.mpf(R.denominator),40)}")
W("")

def show(name, expr, value, target, tol_note=""):
    """expr: string for the residual expression; value: exact rational residual."""
    fv = mp.mpf(value.numerator)/mp.mpf(value.denominator) if isinstance(value, F) else mp.mpf(value)
    ok = (value == 0)
    W(f"  [{ 'EXACT ZERO' if ok else ('SMALL' if abs(fv) < mp.mpf('1e-30') else 'FAILS') }]"
      f" {name:<44} residual = {mp.nstr(fv, 12)}   {tol_note}")
    return ok

W("### identity tests (exact rational residuals)")
show("H1  s^2 + r^2 - 1", "", sv*sv + R*R - 1, 0)
show("H2  A - (s + z)/2", "", A - (sv + zv)/2, 0)
show("H3  (A-z)^2 + (B-r)^2 - r^2", "", (A - zv)**2 + (Bv - R)**2 - R*R, 0)
show("H4  z^2 + t^2 - 2 t r", "", zv*zv + tv*tv - 2*tv*R, 0)
show("H5  C^2 + (1-D)^2 - r^2", "", Cv*Cv + (1 - Dv)**2 - R*R, 0)
W("")
W("### H5 variants")
show("H5'  C^2 + (1-D)^2 - s^2 - r^2", "", Cv*Cv + (1-Dv)**2 - sv*sv - R*R, 0)
show("H5'' C^2 + D^2 - 1", "", Cv*Cv + Dv*Dv - 1, 0)
show("H5''' C^2 + D^2 - 2 D r", "", Cv*Cv + Dv*Dv - 2*Dv*R, 0)
W("")
W("### the circle-through-(z,r) structure")
W("    hypothesis: the 3 points  A , z , s  lie on the circle centred (A, r) of radius r")
for nm, v in (("A", A), ("z", zv), ("s", sv)):
    x = {"A": A, "z": zv, "s": sv}[nm]
    resid = (x - A)**2 + (R - R)**2 - R*R if nm == "A" else (x - A)**2 + (R - R)**2 - R*R
    # actually distance from (A,r) to (x, 0)
    d2 = (x - A)**2 + R*R
    W(f"      |(A,r) - ({nm},0)|^2 - r^2 = {mp.nstr(mp.mpf((d2 - R*R).numerator)/mp.mpf((d2 - R*R).denominator), 12)}")
W("    => trivially true: every point (x,0) is at distance >= r from (A,r); equality iff x = A.")
W("       So the meaningful statement is the COINCIDENCE x = A for the centre of norm A,")
W("       i.e. the hub (A,B) is at distance r from the hole (A, 0)?  Test:")
dAB = (A - A)**2 + (Bv - 0)**2 - R*R
W(f"      |(A,0) - (A,B)|^2 - r^2 = B^2 - r^2 = {mp.nstr(mp.mpf(dAB.numerator)/mp.mpf(dAB.denominator), 12)}")
W("")
W("### what the hole (A, B - r) really is")
W("    the lead's point q = (A, B - r); test its distance to the neighbouring centres")
pts = {"hub(A,B)": (A, Bv), "hub(A,-B)": (A, -Bv)}
for nm, (x, y) in pts.items():
    d2 = (A - x)**2 + (Bv - R - y)**2
    W(f"      |q - {nm}|^2 - r^2 = {mp.nstr(mp.mpf((d2 - R*R).numerator)/mp.mpf((d2 - R*R).denominator), 12)}")
for nm, (x, y) in (("rect(-A,D)", (-A, Dv)), ("rect(-A,-D)", (-A, -Dv))):
    pass
W("")
W("### the ACTUAL hole found by the Voronoi computation, in these parameters")
W("    sites [0,6,13] = rect(+,+) , rect(+,+) , y-pair(+), q = (0.3082777943, 0.5111378562)")
W("    sites [0,10,13] = rect(+,+) , x-pair(+), y-pair(+), q = (z, r)   <- this one")
W(f"    check: q = (z, r) = ({mp.nstr(mp.mpf(zv.numerator)/mp.mpf(zv.denominator),20)},"
  f" {mp.nstr(mp.mpf(R.numerator)/mp.mpf(R.denominator),20)})")
W("    distance from (z,r) to the three sites of [0,10,13]:")
sites = {"rect(+,+) = (A,B)": (A, Bv), "x-pair(+) = (z,0)": (zv, F(0)), "y-pair(+) = (0,t)": (F(0), tv)}
for nm, (x, y) in sites.items():
    d2 = (zv - x)**2 + (R - y)**2
    W(f"      |q - {nm}|^2 - r^2 = {mp.nstr(mp.mpf((d2 - R*R).numerator)/mp.mpf((d2 - R*R).denominator), 12)}")
W("")
W("### and the hole [10,11,12] = x-pair(+),x-pair(-),y-pair(-) with q = (0, t - r):")
q2 = (F(0), tv - R)
for nm, (x, y) in (("x-pair(+) = (z,0)", (zv, F(0))), ("x-pair(-) = (-z,0)", (-zv, F(0))),
                   ("y-pair(-) = (0,-t)", (F(0), -tv))):
    d2 = (q2[0] - x)**2 + (q2[1] - y)**2
    W(f"      |q2 - {nm}|^2 - r^2 = {mp.nstr(mp.mpf((d2 - R*R).numerator)/mp.mpf((d2 - R*R).denominator), 12)}")
W("")
W("### summary of which lead identities hold")
res = {}
for nm, val in [("H1 s^2+r^2-1", sv*sv + R*R - 1), ("H2 A-(s+z)/2", A - (sv + zv)/2),
                ("H3 (A-z)^2+(B-r)^2-r^2", (A - zv)**2 + (Bv - R)**2 - R*R),
                ("H4 z^2+t^2-2tr", zv*zv + tv*tv - 2*tv*R),
                ("H5 C^2+(1-D)^2-r^2", Cv*Cv + (1 - Dv)**2 - R*R),
                ("alt C^2+(1-D)^2-s^2-r^2", Cv*Cv + (1 - Dv)**2 - sv*sv - R*R),
                ("alt C^2+D^2-1", Cv*Cv + Dv*Dv - 1)]:
    fv = mp.mpf(val.numerator)/mp.mpf(val.denominator)
    res[nm] = {"exact_zero": val == 0, "residual": mp.nstr(fv, 12)}
    W(f"  {nm:<28} exact zero: {str(val==0):<6} residual {mp.nstr(fv,10)}")
import json as _j
(_j.dump(res, (EV / "lead_identities.json").open("w"), indent=2))
(EV / "lead_identities.txt").write_text("\n".join(OUT), encoding="utf-8")
print("written evidence/lead_identities.txt|json")
