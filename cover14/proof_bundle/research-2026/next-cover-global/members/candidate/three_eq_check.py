"""n=14: independent numeric check of the three-equation system, and of the claim that
the old hprec point is NOT stationary.

Equations, in the free coordinates (z, C, r) with the five relations and the branch-selected
signs (sigma_t, sigma_B, sigma_D) = (+, +, -)  -- note sigma_B = + is FORCED here:

    U = sqrt(1 - r^2)      A = (z+U)/2      s = U
    V = sqrt(r^2 - z^2)    t = r + V        B = r + sqrt(r^2 - (A-z)^2)
    Wd = sqrt(r^2 - C^2)   D = 1 - Wd

  (EQ1) SWITCH:   exists p with |p| = 1 and |p - (A,B)| = r = |p - (C,D)|
  (EQ2) CIRC3:    the three centres (A,B), (C,D), (0,t) have circumradius exactly r
  (EQ3) STATION:  det d(EQ1,EQ2)/d(z,C) = 0

All evaluations use mpmath at high precision, EXCEPT the defining relations which are
taken in their branch-selected closed forms (so no squaring ambiguity).
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
z0, C0, r0 = d(abs(th[5])), d(abs(th[2])), d(abs(R))
W("### the old hprec point (free coordinates)")
W(f"  z = {mp.nstr(z0,40)}")
W(f"  C = {mp.nstr(C0,40)}")
W(f"  r = {mp.nstr(r0,40)}")
W(f"  (full th magnitudes: A={mp.nstr(d(abs(th[0])),30)} B={mp.nstr(d(abs(th[1])),30)}"
  f" D={mp.nstr(d(abs(th[3])),30)} s={mp.nstr(d(abs(th[4])),30)} t={mp.nstr(d(abs(th[6])),30)})")
W("")

def mags(z, C, r):
    U = mp.sqrt(1 - r**2)
    A = (z + U)/2
    V = mp.sqrt(r**2 - z**2)
    Wd = mp.sqrt(r**2 - C**2)
    return {"A": A, "s": U, "B": r + mp.sqrt(r**2 - (A - z)**2), "t": r + V,
            "D": 1 - Wd, "V": V, "Wd": Wd, "U": U}

def circ3(m):
    """circumradius of (A,B),(C,D),(0,t)"""
    p1 = (m["A"], m["B"]); p2 = (m["C"] if "C" in m else None, m["D"]); p3 = (mp.mpf(0), m["t"])
    return p1, p2, p3

def circ_radius(p1, p2, p3):
    def dd2(a, b): return (a[0]-b[0])**2 + (a[1]-b[1])**2
    a2, b2, c2 = dd2(p1, p2), dd2(p2, p3), dd2(p3, p1)
    cross = (p2[0]-p1[0])*(p3[1]-p1[1]) - (p2[1]-p1[1])*(p3[0]-p1[0])
    if cross == 0: return None
    return mp.sqrt(a2*b2*c2)/(2*abs(cross))

def EQ2(z, C, r, m=None):
    m = m or mags(z, C, r)
    p1 = (m["A"], m["B"]); p2 = (C, m["D"]); p3 = (mp.mpf(0), m["t"])
    Rc = circ_radius(p1, p2, p3)
    return (Rc - r) if Rc is not None else None, Rc

def EQ1(z, C, r, m=None):
    """smallest | |p-c0| - r | over p on the UNIT circle at distance r from c6', i.e.
    the existence of a switch point.  Returns the residual of the co-circularity:
    min over p in S1 with |p-c6'|=r of ( |p-c0| - r )."""
    m = m or mags(z, C, r)
    A, B, D, t = m["A"], m["B"], m["D"], m["t"]
    c0 = (A, B); c6 = (C, D)
    # points p on S1 with |p-c6| = r: intersect the unit circle with that circle
    dq = mp.sqrt(c6[0]**2 + c6[1]**2)
    if dq == 0: return None, None
    # circle |p|^2=1 and |p-c6|^2=r^2  ->  p . c6 = (1 + |c6|^2 - r^2)/2
    h = (1 + dq**2 - r**2)/(2*dq)            # distance from origin to the chord line
    if abs(h) > 1: return None, None
    half = mp.sqrt(max(1 - h**2, mp.mpf(0)))
    e1 = (c6[0]/dq, c6[1]/dq); e2 = (-c6[1]/dq, c6[0]/dq)
    best = None
    for sgn in (1, -1):
        p = (h*e1[0] + sgn*half*e2[0], h*e1[1] + sgn*half*e2[1])
        val = mp.sqrt((p[0]-c0[0])**2 + (p[1]-c0[1])**2) - r
        if best is None or abs(val) < abs(best[0]): best = (val, p)
    return best[0], best[1]

W("### evaluation at the OLD hprec point")
m0 = mags(z0, C0, r0)
e2v, Rc = EQ2(z0, C0, r0, m0)
e1v, pswitch = EQ1(z0, C0, r0, m0)
W(f"  EQ2 residual  (circumradius - r) = {mp.nstr(e2v, 12)}   (circumradius = {mp.nstr(Rc, 20)})")
W(f"  EQ1 residual  (|p-c0| - r)       = {mp.nstr(e1v, 12)}")
W(f"  switch point p = ({mp.nstr(pswitch[0],20)}, {mp.nstr(pswitch[1],20)})  |p| = "
  f"{mp.nstr(mp.sqrt(pswitch[0]**2+pswitch[1]**2),20)}")
W("")
W("### stationarity: Jdet = det d(EQ1,EQ2)/d(z,C) at the old point")
h = mp.mpf('1e-25')
def Jdet(z, C, r):
    f1 = lambda zz, CC: EQ1(zz, CC, r)[0]
    f2 = lambda zz, CC: EQ2(zz, CC, r)[0]
    d1z = (f1(z+h, C) - f1(z-h, C))/(2*h)
    d1C = (f1(z, C+h) - f1(z, C-h))/(2*h)
    d2z = (f2(z+h, C) - f2(z-h, C))/(2*h)
    d2C = (f2(z, C+h) - f2(z, C-h))/(2*h)
    return d1z*d2C - d1C*d2z
J0 = Jdet(z0, C0, r0)
W(f"  Jdet(old hprec) = {mp.nstr(J0, 12)}")
W(f"  lead reports   = -4.6184e-10")
W(f"  match at 1e-4 relative: {abs((J0 + mp.mpf('4.6184e-10'))/mp.mpf('4.6184e-10')) < mp.mpf('1e-4')}")
W("")
W("### the three-equation system, solved from the old point")
def F3(v):
    z_, C_, r_ = v
    r1 = EQ1(z_, C_, r_)[0]
    r2 = EQ2(z_, C_, r_)[0]
    return [r1, r2, Jdet(z_, C_, r_)]
try:
    sol = mp.findroot(lambda *v: F3(list(v)), [z0, C0, r0], tol=mp.mpf('1e-45'), maxsteps=60)
    z1, C1, r1 = sol[0], sol[1], sol[2]
    W(f"  solved: z = {mp.nstr(z1,40)}")
    W(f"          C = {mp.nstr(C1,40)}")
    W(f"          r = {mp.nstr(r1,40)}")
    W(f"  residuals: EQ1={mp.nstr(EQ1(z1,C1,r1)[0],6)}  EQ2={mp.nstr(EQ2(z1,C1,r1)[0],6)}"
      f"  Jdet={mp.nstr(Jdet(z1,C1,r1),6)}")
    W(f"  r_new - r_old = {mp.nstr(r1-r0,10)}")
    W(f"  lead's new r  = 0.3317320342762341225578155488")
    W(f"  difference from lead = {mp.nstr(r1 - mp.mpf('0.3317320342762341225578155488'), 10)}")
    m1 = mags(z1, C1, r1)
    W("  new th magnitudes (A,B,C,D,s,z,t = ): ")
    W(f"    A={mp.nstr(m1['A'],40)}")
    W(f"    B={mp.nstr(m1['B'],40)}")
    W(f"    C={mp.nstr(C1,40)}")
    W(f"    D={mp.nstr(m1['D'],40)}")
    W(f"    s={mp.nstr(m1['s'],40)}")
    W(f"    z={mp.nstr(z1,40)}")
    W(f"    t={mp.nstr(m1['t'],40)}")
    W(f"    r={mp.nstr(r1,40)}")
    json.dump({"old": {"z": mp.nstr(z0,40), "C": mp.nstr(C0,40), "r": mp.nstr(r0,40), "Jdet": mp.nstr(J0,12)},
               "new": {"z": mp.nstr(z1,40), "C": mp.nstr(C1,40), "r": mp.nstr(r1,40),
                       "A": mp.nstr(m1['A'],40), "B": mp.nstr(m1['B'],40), "D": mp.nstr(m1['D'],40),
                       "s": mp.nstr(m1['s'],40), "t": mp.nstr(m1['t'],40)},
               "r_diff": mp.nstr(r1-r0, 12)},
              (EV / "three_eq_check.json").open("w"), indent=2)
except Exception as ex:
    W(f"  findroot failed: {ex}")
(EV / "three_eq_check.txt").write_text("\n".join(OUT), encoding="utf-8")
print("written evidence/three_eq_check.txt|json")
