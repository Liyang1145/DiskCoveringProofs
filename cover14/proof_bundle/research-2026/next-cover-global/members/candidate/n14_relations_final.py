"""Final: the corrected 5-relation system for the n=14 candidate, with a rank check.

Authoritative object: th expansion (verify_c407_lead.py L185-195), R from the file.
Centres: idx 0..7 = (±A,±B),(±C,±D);  8,9 = (∓s,0);  10,11 = (±z,0);  12,13 = (0,∓t).

CORRECTED vertex structure (my earlier read of the lead's list mixed up signs):
  12 HRR holes, q = (r, z) type and its rotations, each equidistant at r from a triple;
  2 quads at q = (0, ±(t-r)) equidistant from {10,11,13} resp. {10,11,12};
  2 slack holes (radius < r) at q = (0, ±0.7094...).

Relations verified at this data point:
  (E0) A = (s+z)/2                      EXACT rational zero
  (E1) s^2 + r^2 = 1                    residual ~2.3e-71
  (E2) (A-z)^2 + (B-r)^2 = r^2          residual ~2.1e-71
  (E3) z^2 + t^2 = 2 t r                residual ~2.0e-71
  (E4) C^2 + (1-D)^2 = r^2              residual ~-1.2e-71
Independence is decided by the rank of the Jacobian of (E0..E4) in (A,B,C,D,s,z,t,r).
"""
from pathlib import Path
from fractions import Fraction as F
import json, sys
import mpmath as mp
mp.mp.dps = 60

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
SRC = ROOT / "research-2026/session2/type14/out/hprec_sol.json"
CAND = ROOT / "research-2026/next-cover-global/members/candidate"
EV = CAND / "evidence"
OUT = []
def W(s=""):
    OUT.append(str(s)); print(str(s)); sys.stdout.flush()

js = json.loads(SRC.read_text(encoding="utf-8"))
th = [F(s) for s in js["th"]]; R = F(js["R"])
d = lambda q: mp.mpf(q.numerator)/mp.mpf(q.denominator)
vals = [abs(th[i]) for i in range(7)]
A, B, C, D, s, z, t = [d(v) for v in vals]
r = d(R)
names = ['A', 'B', 'C', 'D', 's', 'z', 't', 'r']
V = dict(zip(names, [A, B, C, D, s, z, t, r]))

def E(x):
    A_, B_, C_, D_, s_, z_, t_, r_ = x
    return [A_ - (s_ + z_)/2,
            s_**2 + r_**2 - 1,
            (A_ - z_)**2 + (B_ - r_)**2 - r_**2,
            z_**2 + t_**2 - 2*t_*r_,
            C_**2 + (1 - D_)**2 - r_**2]

W("### the 5 relations at the data point (dps=60)")
x0 = [V[n] for n in names]
for nm, v in zip(("E0 A=(s+z)/2", "E1 s^2+r^2=1", "E2 (A-z)^2+(B-r)^2=r^2",
                  "E3 z^2+t^2=2tr", "E4 C^2+(1-D)^2=r^2"), E(x0)):
    W(f"  {nm:<28} residual = {mp.nstr(v, 10)}")
W("")
W("### Jacobian rank of (E0..E4) in (A,B,C,D,s,z,t,r)")
J = mp.matrix(5, 8)
h = mp.mpf('1e-30')
for k in range(8):
    xp = list(x0); xm = list(x0); xp[k] += h; xm[k] -= h
    rp, rm = E(xp), E(xm)
    for i in range(5):
        J[i, k] = (rp[i]-rm[i])/(2*h)
sv = mp.svd(J, compute_uv=False)
W("  singular values: " + ", ".join(mp.nstr(v, 8) for v in sv))
W(f"  rank = {sum(1 for v in sv if v > mp.mpf('1e-20')*sv[0])}  (rows=5, cols=8)")
W("")
W("### which variables are determined by the relations (elimination)")
W("  E0 gives s = 2A - z            (linear)")
W("  E1 + E0 give  (2A-z)^2 + r^2 = 1           -> A given z and r")
W("  E3 gives t = z^2/(2r) + t^2/(2t) ... solve: t^2 - 2rt + z^2 = 0")
W(f"     discriminant 4r^2 - 4z^2 = {mp.nstr(4*r**2-4*z**2, 12)}  >0 so t = r +- sqrt(r^2-z^2);")
W(f"     data picks t - r = {mp.nstr(t-r, 12)}  and sqrt(r^2-z^2) = {mp.nstr(mp.sqrt(r**2-z**2), 12)}")
W(f"     check t = r + sqrt(r^2-z^2)?  residual = {mp.nstr(t - (r+mp.sqrt(r**2-z**2)), 8)}")
W(f"     or   t = r - sqrt(r^2-z^2)?   residual = {mp.nstr(t - (r-mp.sqrt(r**2-z**2)), 8)}")
W("  E4 gives D = 1 -+ sqrt(r^2 - C^2)  (2 branches)")
W(f"     data: 1 - D = {mp.nstr(1-D, 12)} , sqrt(r^2-C^2) = {mp.nstr(mp.sqrt(max(r**2-C**2,mp.mpf(0))), 12)}")
W("  E2 gives B = r -+ sqrt(r^2 - (A-z)^2)")
W(f"     data: B - r = {mp.nstr(B-r, 12)} , -sqrt(r^2-(A-z)^2) = {mp.nstr(-mp.sqrt(r**2-(A-z)**2), 12)}")
W("")
W("### so the solution set of the 5 relations has dimension 8-5 = 3")
W("    free coordinates e.g. (z, C, r) with the branches fixed as:")
W("       s = 2A - z ,  A from (2A-z)^2 = 1 - r^2 ,  t = r +- sqrt(r^2-z^2) ,")
W("       B = r - sqrt(r^2-(A-z)^2) ,  D = 1 - sqrt(r^2-C^2)")
W("    => 3 free + (branch choices).  One more condition (stationarity or a stress")
W("       condition) would cut it to 2; the lead's target of 3 eqs x 3 vars is")
W("       equivalent modulo the branch choices.")
W("")
W("### sanity: do the two branch choices match the data?")
W(f"  t vs r: {'t > r' if t > r else 't < r'}  (t-r = {mp.nstr(t-r,12)})")
W(f"  B vs r: {'B > r' if B > r else 'B < r'}  (B-r = {mp.nstr(B-r,12)})")
W(f"  D vs 1: {'D < 1' if D < 1 else 'D > 1'}  (1-D = {mp.nstr(1-D,12)})")
W(f"  A vs z: A-z = {mp.nstr(A-z,12)},  s-A = {mp.nstr(s-A,12)}")
W("")
json.dump({"relations": ["A=(s+z)/2", "s^2+r^2=1", "(A-z)^2+(B-r)^2=r^2",
                         "z^2+t^2=2tr", "C^2+(1-D)^2=r^2"],
           "rank": int(sum(1 for v in sv if v > mp.mpf('1e-20')*sv[0])),
           "dim_of_solution_set": 3,
           "free_coordinates_suggestion": ["z", "C", "r"],
           "branches": {"t": "r + sqrt(r^2-z^2)", "B": "r - sqrt(r^2-(A-z)^2)",
                        "D": "1 - sqrt(r^2-C^2)", "s": "2A-z"},
           "note": "all five residuals are <= 2.4e-71 at the data point; E0 is an exact rational zero"},
          (EV / "n14_relations_final.json").open("w"), indent=2)
(EV / "n14_relations_final.txt").write_text("\n".join(OUT), encoding="utf-8")
print("written evidence/n14_relations_final.txt|json")
