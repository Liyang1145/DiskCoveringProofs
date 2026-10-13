"""step6_verify.py -- consolidated decisive check.

(1) Re-derive the geometry from the Lead's given z,c,r using the SAME algebraic chain as
    lead/root_scout.py (geom()), i.e. a=(s+z)/2, b=r+sqrt(r^2-z^2), d=1-sqrt(r^2-c^2), t=b.
(2) Verify the tight triple {Z1,Z2,T+} has circumradius exactly r*.
(3) Verify the Lead's two contact equations F,G are (numerically) satisfied at this point
    and at the OLD refined root -> the root system is as assumed.
(4) Evaluate the covering radius of the unit disk for both roots on a fine grid and at
    analytically enumerated candidates.
"""
import json, sys, itertools
from pathlib import Path
import mpmath as mp
import numpy as np

mp.mp.dps = 60
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

scout = json.loads((Path(__file__).resolve().parents[3] / "lead/root-scout.json").read_text(encoding="utf-8"))
z, c, r = (mp.mpf(s) for s in scout["z_c_r"])
s_ = mp.sqrt(1 - r * r)
a = (s_ + z) / 2
b = r + mp.sqrt(r * r - z * z)
dd = 1 - mp.sqrt(r * r - c * c)
t = b
W("== step6 consolidated ==")
W("(1) geometry from Lead's z,c,r:")
for nm, v in [("z", z), ("c", c), ("r", r), ("s=sqrt(1-r^2)", s_), ("a=(s+z)/2", a),
              ("b=r+sqrt(r^2-z^2)", b), ("d=1-sqrt(r^2-c^2)", dd), ("t=b", t)]:
    W("    %-22s = %s" % (nm, mp.nstr(v, 30)))
W("    a-b = %s ;  a+b = %s ;  z-t = %s" % (mp.nstr(a - b, 12), mp.nstr(a + b, 12), mp.nstr(z - t, 12)))

# centers arranged as: 0-3 (+-a,+-b) ; 4-7 (+-c,+-d) ; 8,9 (+-s,0) ; 10,11 (+-z,0) ; 12,13 (0,-+t)
C = []
for sy in (1, -1):
    for sx in (1, -1):
        C.append((sx * a, sy * b))
for sy in (1, -1):
    for sx in (1, -1):
        C.append((sx * c, sy * dd))
C.append((s_, mp.mpf(0))); C.append((-s_, mp.mpf(0)))
C.append((z, mp.mpf(0))); C.append((-z, mp.mpf(0)))
C.append((mp.mpf(0), -t)); C.append((mp.mpf(0), t))
dn = lambda p, q: mp.sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)

W("(2) tight triples and their circumradius (independent circle solve):")
def circ(P):
    A = [[2 * (P[1][0] - P[0][0]), 2 * (P[1][1] - P[0][1])],
         [2 * (P[2][0] - P[0][0]), 2 * (P[2][1] - P[0][1])]]
    bx = [P[1][0] ** 2 + P[1][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2,
          P[2][0] ** 2 + P[2][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2]
    det = A[0][0] * A[1][1] - A[0][1] * A[1][0]
    ux = (bx[0] * A[1][1] - A[0][1] * bx[1]) / det
    uy = (A[0][0] * bx[1] - bx[0] * A[1][0]) / det
    u = (ux, uy)
    return u, dn(u, P[0])

for tri in [(10, 11, 12), (10, 11, 13)]:
    u, R3 = circ([C[i] for i in tri])
    W("    tri%-14s u=(%s,%s) R=%s  R-r*=%.3e" % (str(tri), mp.nstr(u[0], 16), mp.nstr(u[1], 16),
                                                  mp.nstr(R3, 25), R3 - r))

W("(3) contact equations F,G from lead/root_scout.py at (a) Lead root, (b) OLD refined root:")
def FG(a_, b_, c_, d_, r_):
    v1 = (1 + a_ * a_ + b_ * b_ - r_ * r_) / 2
    v2 = (1 + c_ * c_ + d_ * d_ - r_ * r_) / 2
    det = a_ * d_ - b_ * c_
    F = ((v1 * d_ - v2 * b_) ** 2 + (a_ * v2 - c_ * v1) ** 2 - det * det) / (a_ * d_ - b_ * c_)
    cross = (c_ - a_) * (t - b_) - (d_ - b_) * (-a_)
    l1 = (a_ - c_) ** 2 + (b_ - d_) ** 2; l2 = c_ * c_ + (d_ - t) ** 2; l3 = a_ * a_ + (b_ - t) ** 2
    G = l1 * l2 * l3 - 4 * r_ * r_ * cross * cross
    return F, G
F, G = FG(a, b, c, dd, r)
W("    Lead root  : F=%s  G=%s" % (mp.nstr(F, 12), mp.nstr(G, 12)))
oj = json.loads((Path(__file__).resolve().parents[5] / "research-2026/session2/type14/out/hprec_sol_refined.json").read_text())
th = [mp.mpf(x) for x in oj["th"][:7]]; Ro = mp.mpf(oj["R"])
# old: a'=th0, b'=th1, c'=th2, d'=th3
t_ = th[6]
Fo, Go = FG(th[0], th[1], th[2], th[3], Ro)
W("    OLD root   : F=%s  G=%s" % (mp.nstr(Fo, 12), mp.nstr(Go, 12)))

W("(4) covering radius of the unit disk:")
Cn = np.array([[float(p[0]), float(p[1])] for p in C])
def brute(Cn, tag, n=4000):
    gx = np.linspace(-1, 1, n)
    XX, YY = np.meshgrid(gx, gx)
    P = np.stack([XX.ravel(), YY.ravel()], 1)
    P = P[(P ** 2).sum(1) <= 1.0]
    d = np.sqrt(((P[:, None, :] - Cn[None, :, :]) ** 2).sum(-1)).min(1)
    j = int(d.argmax())
    W("    [%s] grid %d: max min-dist = %.12f at (%.9f,%.9f) |x|=%.6f" % (
        tag, len(P), d[j], P[j, 0], P[j, 1], np.hypot(*P[j])))
    return float(d[j]), P[j]
mv, pv = brute(Cn, "NEW geometry")
# old geometry numpy
Cold = np.array([[float(x) for x in [th[0], th[1]]], [float(-th[0]), float(th[1])], [float(th[0]), float(-th[1])], [float(-th[0]), float(-th[1])],
                 [float(th[2]), float(th[3])], [float(-th[2]), float(th[3])], [float(th[2]), float(-th[3])], [float(-th[2]), float(-th[3])],
                 [float(th[4]), 0.0], [float(-th[4]), 0.0], [float(th[5]), 0.0], [float(-th[5]), 0.0],
                 [0.0, float(th[6])], [0.0, float(-th[6])]])
mo, po = brute(Cold, "OLD geometry")
W("")
W("    => NEW geometry covers at >= %.12f ; declared r* = %.18f" % (mv, float(r)))
W("    => OLD geometry covers at >= %.12f ; declared R  = %.18f" % (mo, float(Ro)))
W("    uncovered witnesses (NEW): %s" % [tuple(np.round(x, 6)) for x in [pv]])
# distance table at the uncovered point (high precision)
xp = (mp.mpf(float(pv[0])), mp.mpf(float(pv[1])))
ds = sorted((dn(xp, C[i]), i) for i in range(14))
W("    NEW: nearest distances at uncovered witness: %s" % [(mp.nstr(d, 12), i) for d, i in ds[:4]])

json.dump(dict(z=mp.nstr(z, 40), c=mp.nstr(c, 40), r=mp.nstr(r, 40), a=mp.nstr(a, 40), b=mp.nstr(b, 40),
               d=mp.nstr(dd, 40), s=mp.nstr(s_, 40), t=mp.nstr(t, 40),
               F_lead=mp.nstr(F, 20), G_lead=mp.nstr(G, 20), F_old=mp.nstr(Fo, 20), G_old=mp.nstr(Go, 20),
               new_hamax=mv, new_witness=list(map(float, pv)), old_hamax=mo, old_witness=list(map(float, po))),
          open(HERE.parent / "evidence/step6_verify.json", "w"), indent=1)
(HERE.parent / "logs/step6_verify.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/step6_verify.txt")
