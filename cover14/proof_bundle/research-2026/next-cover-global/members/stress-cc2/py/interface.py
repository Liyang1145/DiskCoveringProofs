"""interface.py -- THE fixed geometry interface for the n14 sharp candidate.
Reads the Lead's full-precision strings (no float64), expands to 14 ordered centres,
and emits the structural certificate data requested: centre hash/order, 16 Voronoi triples
(14 tight / 2 slack), 10 anchors, 20 tight edges, 10 gaps with the 2 cap-active ones.
Nothing is optimised here: no LP, no root solving.
"""
import json, sys, hashlib
from pathlib import Path
import itertools
import mpmath as mp

mp.mp.dps = 80
ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

scout = json.loads((ROOT / "research-2026/next-cover-global/lead/root-scout.json").read_text(encoding="utf-8"), parse_float=str, parse_int=str)
z = mp.mpf(scout["z_c_r"][0]); c = mp.mpf(scout["z_c_r"][1]); r = mp.mpf(scout["z_c_r"][2])
s = mp.sqrt(1 - r * r)
a = (s + z) / 2
b = r + mp.sqrt(r * r - (a - z) ** 2)
d = 1 - mp.sqrt(r * r - c * c)
t = r + mp.sqrt(r * r - z * z)

W("== n14 FIXED geometry interface (full-precision strings) ==")
W("input strings from lead/root-scout.json: z=%.60g  c=%.60g  r=%.60g" % (float(z), float(c), float(r)))
for nm, v in [("z", z), ("c", c), ("r", r), ("s", s), ("a", a), ("b", b), ("d", d), ("t", t)]:
    W("  %-12s = %s" % (nm, mp.nstr(v, 45)))

# ordered centres, Lead's expansion: (+-a,+-b) x4, (+-c,+-d) x4, (+-s,0), (0,-+t), (+-z,0)
C = []
for sy in (1, -1):
    for sx in (1, -1):
        C.append((sx * a, sy * b))
for sy in (1, -1):
    for sx in (1, -1):
        C.append((sx * c, sy * d))
C.append((s, mp.mpf(0))); C.append((-s, mp.mpf(0)))
C.append((z, mp.mpf(0))); C.append((-z, mp.mpf(0)))
C.append((mp.mpf(0), -t)); C.append((mp.mpf(0), t))
assert len(C) == 14
W("")
W("### 14 centres in order (40 digits)")
for i, p in enumerate(C):
    W("  %2d  %s  %s" % (i, mp.nstr(p[0], 40), mp.nstr(p[1], 40)))
h = hashlib.sha256("|".join(mp.nstr(p[0], 50) + "," + mp.nstr(p[1], 50) for p in C).encode()).hexdigest()
W("ordered-centre sha256 (50-digit coords): %s" % h)

norm = lambda p: mp.sqrt(p[0] ** 2 + p[1] ** 2)
dist = lambda p, q: mp.sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)

# ---------- anchors: S^1 points where |x-c_i| = r
W("")
W("### anchors (exact S^1 bisector solutions), computed independently of any list")
anch = []
for i in range(14):
    ci = C[i]; rho = norm(ci)
    if rho < mp.mpf("1e-40"):
        continue
    m = (1 + rho * rho - r * r) / (2 * rho)
    if abs(m) > 1:
        continue
    psi = mp.acos(m); phi = mp.atan2(ci[1], ci[0])
    for sg in (1, -1):
        ang = phi + sg * psi
        anch.append(((ang % (2 * mp.pi)), i, (mp.cos(ang), mp.sin(ang))))
anch.sort(key=lambda z_: z_[0])
# dedupe by angle
cl = []
for a_ in anch:
    if cl and abs(a_[0] - cl[-1][0]) < mp.mpf("1e-30"):
        cl[-1][1].append(a_[1])
    else:
        cl.append([a_[0], [a_[1]]])
W("   distinct boundary points: %d" % len(cl))
owners = []
for ang, sites in cl:
    x = (mp.cos(ang), mp.sin(ang))
    ds = sorted((abs(dist(x, C[j]) - r), j) for j in range(14))
    near = [j for dv, j in ds if dv < mp.mpf("1e-14")]
    owners.append((ang, sorted(near)))
    W("   ang=%s deg  tight sites %s  (devs %s)" % (mp.nstr(ang * 180 / mp.pi, 16), sorted(near),
                                                     [mp.nstr(dv, 3) for dv, j in ds[:3]]))
W("   anchors: %d ; all degree 2: %s" % (len(owners), all(len(o[1]) == 2 for o in owners)))
L = 2 * mp.asin(r)
gaps = [((owners[(k + 1) % len(owners)][0] - owners[k][0]) % (2 * mp.pi)) for k in range(len(owners))]
W("   L* = 2asin(r) = %s  (%.12f deg)" % (mp.nstr(L, 30), float(L * 180 / mp.pi)))
W("   gaps (deg): %s" % [mp.nstr(x * 180 / mp.pi, 12) for x in gaps])
W("   cap-active gaps (gap >= L*): %s" % [k for k in range(len(gaps)) if gaps[k] >= L - mp.mpf("1e-40")])
W("   sum gaps - 2pi = %s" % mp.nstr(sum(gaps) - 2 * mp.pi, 8))
W("   max gap <= L*: %s ; 10L*-2pi = %s" % (max(gaps) <= L, mp.nstr(10 * L - 2 * mp.pi, 20)))

# ---------- Voronoi vertices in D
W("")
W("### in-D Voronoi vertices = circumcentres of Delaunay triples (independent enumeration)")
V = []
for tri in itertools.combinations(range(14), 3):
    p, q, s3 = C[tri[0]], C[tri[1]], C[tri[2]]
    det = 2 * ((p[0] - s3[0]) * (q[1] - s3[1]) - (p[1] - s3[1]) * (q[0] - s3[0]))
    if det == 0:
        continue
    b1 = p[0] ** 2 + p[1] ** 2 - s3[0] ** 2 - s3[1] ** 2
    b2 = q[0] ** 2 + q[1] ** 2 - s3[0] ** 2 - s3[1] ** 2
    ux = (b1 * (q[1] - s3[1]) - (p[1] - s3[1]) * b2) / det
    uy = ((p[0] - s3[0]) * b2 - b1 * (q[0] - s3[0])) / det
    u = (ux, uy)
    if norm(u) > 1:
        continue
    R3 = dist(u, p)
    others = [dist(u, C[l]) for l in range(14) if l not in tri]
    if min(others) < R3 - mp.mpf("1e-25"):
        continue
    V.append((tri, u, R3))
W("   in-D Voronoi vertices: %d" % len(V))
tight = [v for v in V if abs(v[2] - r) < mp.mpf("1e-20")]
slackv = [v for v in V if abs(v[2] - r) >= mp.mpf("1e-20")]
W("   TIGHT (circumradius == r*): %d" % len(tight))
for tri, u, R3 in sorted(tight, key=lambda z_: z_[0]):
    W("     %-16s u=(%s, %s) R-r*=%s" % (str(tuple(tri)), mp.nstr(u[0], 20), mp.nstr(u[1], 20), mp.nstr(R3 - r, 3)))
W("   SLACK: %d" % len(slackv))
for tri, u, R3 in sorted(slackv, key=lambda z_: z_[0]):
    W("     %-16s u=(%s, %s) R-r*=%s" % (str(tuple(tri)), mp.nstr(u[0], 20), mp.nstr(u[1], 20), mp.nstr(R3 - r, 8)))

# ---------- tight anchor-site edges
W("")
W("### tight anchor-site edges (each anchor should own exactly 2 centres)")
tp = []
for ang, near in owners:
    for j in near:
        tp.append((ang, j))
W("   count = %d" % len(tp))
deg = {j: sum(1 for (_, jj) in tp if jj == j) for j in range(14)}
W("   anchor degree per centre: %s" % deg)
W("   centres with no anchor edge: %s" % [j for j in range(14) if deg[j] == 0])

# ---------- covering radius (direct, no optimisation)
def minf(x):
    return min(dist(x, C[j]) for j in range(14))
W("")
W("### covering radius of the closed unit disk (this configuration)")
best = (mp.mpf(0), None)
for tri, u, R3 in V:
    f = minf(u)
    if f > best[0]:
        best = (f, u)
W("   max over in-D Voronoi vertices: %s" % mp.nstr(best[0], 20))
bnd = (mp.mpf(0), None)
for k in range(200000):
    th = 2 * mp.pi * k / 200000
    f = minf((mp.cos(th), mp.sin(th)))
    if f > bnd[0]:
        bnd = (f, th)
W("   max over boundary (200k sweep): %s at %.10f deg" % (mp.nstr(bnd[0], 20), float(bnd[1] * 180 / mp.pi)))
W("   => config covers D at radius %s   (declared r* = %s)" % (mp.nstr(max(best[0], bnd[0]), 20), mp.nstr(r, 20)))

data = dict(z=mp.nstr(z, 60), c=mp.nstr(c, 60), r=mp.nstr(r, 60),
            a=mp.nstr(a, 60), b=mp.nstr(b, 60), d=mp.nstr(d, 60), s=mp.nstr(s, 60), t=mp.nstr(t, 60),
            centers=[[mp.nstr(p[0], 45), mp.nstr(p[1], 45)] for p in C], sha256=h,
            anchors=[[mp.nstr(o[0] * 180 / mp.pi, 30), o[1]] for o in owners],
            gaps_deg=[mp.nstr(x * 180 / mp.pi, 30) for x in gaps],
            cap_active=[k for k in range(len(gaps)) if gaps[k] >= L - mp.mpf("1e-40")],
            tight_triples=[list(t) for t, _, _ in sorted(tight, key=lambda z_: z_[0])],
            slack_triples=[list(t) for t, _, _ in sorted(slackv, key=lambda z_: z_[0])],
            tight_edges=[[mp.nstr(aa * 180 / mp.pi, 30), j] for aa, j in tp],
            cover_radius=mp.nstr(max(best[0], bnd[0]), 30), L=mp.nstr(L, 40))
(HERE.parent / "evidence/interface.json").write_text(json.dumps(data, indent=1), encoding="utf-8")
(HERE.parent / "logs/interface.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/interface.txt evidence/interface.json")

