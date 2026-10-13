"""step2_boundary.py -- robust boundary-arc ownership + Voronoi-vertex classification at NEW root.

Independent of Lead's tight/slack lists: scans S^1 for nearest-site ownership, clusters switch
points into anchors, then classifies the in-D Voronoi vertices by circumradius vs r*.

Outputs logs/step2_boundary.txt, evidence/step2_boundary.json
"""
import json, sys
from pathlib import Path
import itertools
import mpmath as mp

mp.mp.dps = 60
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom import new_geom, centers_from, old_geom_centers, norm, dist, circumcenter

OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

g = new_geom()
C = centers_from(g)
r = g["r"]
L = 2 * mp.asin(r)
W("== step2: boundary ownership + vertex classification at NEW root ==")
W("r*=1-|c|+r version: 1-(|c|+r) per site:")
for i, p in enumerate(C):
    W("  %2d |c|=%s  1-(|c|+r)=%s" % (i, mp.nstr(norm(p), 20), mp.nstr(1 - (norm(p) + r), 6)))

# ---- 1. exact arc per boundary-reaching site: |c_i - x| <= r for x on S^1
# d_i(x)^2 = 1 + |c|^2 - 2 c.x  <= r^2  <=>  c.x >= (1+|c|^2-r^2)/2
W("")
W("### sites whose disk reaches S^1 (|c|<=1-r  <=>  2|c| <= 1+r-r^2/|c| ... use formula)")
reach = []
for i, p in enumerate(C):
    rho = norm(p)
    # min distance from c to S^1 = |1-rho|
    if min(rho, 1) >= 1 - r - mp.mpf("1e-25") or (1 - rho) <= r + mp.mpf("1e-25"):
        reach.append(i)
    W("  %2d rho=%s  dist(c,S1)=%s  <= r ? %s" % (i, mp.nstr(rho, 18), mp.nstr(abs(1 - rho), 18), abs(1 - rho) <= r + mp.mpf("1e-25")))
W("  boundary-reaching sites: %s (n=%d)" % (reach, len(reach)))

# arc endpoints: c.x_hat = (1+rho^2-r^2)/2 ; on S^1 c.x = rho cos(ang-phi)
W("")
W("### arcs (angle interval on S^1), computed from half-width psi=acos((1+rho^2-r^2)/(2 rho))")
arcs = []
for i in reach:
    p = C[i]; rho = norm(p)
    m = (1 + rho * rho - r * r) / (2 * rho)
    psi = mp.acos(m); phi = mp.atan2(p[1], p[0])
    arcs.append((i, phi, psi, 2 * psi))
    W("  site %2d phi=%s psi=%s width=%s (deg %s)  2asin(r) = %s" % (
        i, mp.nstr(phi * 180 / mp.pi, 12), mp.nstr(psi, 18), mp.nstr(2 * psi, 18),
        mp.nstr(2 * psi * 180 / mp.pi, 12), mp.nstr(L, 18)))

# ---- 2. brute ownership scan
W("")
W("### S^1 ownership scan (N=72000) : sites with d<=r")
N = 72000
own = {}
for k in range(N):
    a = 2 * mp.pi * k / N
    x = (mp.cos(a), mp.sin(a))
    best, bd = None, mp.inf
    for i in reach:
        d = dist(x, C[i])
        if d < bd - mp.mpf("1e-30"):
            bd, best = d, i
    own[k] = (best, bd, a)
# find switch indices
sw = []
for k in range(N):
    k2 = (k + 1) % N
    if own[k][0] != own[k2][0]:
        sw.append(k2)
W("   switch points: n=%d" % len(sw))
W("   sequence of owners around circle:")
seq = []
prev = own[sw[0] if sw else 0][0]
for k in sw:
    seq.append(own[k][0])
W("   %s" % seq)
W("   distinct owners: %s  n=%d" % (sorted(set(seq)), len(set(seq))))
sw_ang = [own[k][2] for k in sw]
W("   switch angles(deg): %s" % [mp.nstr(a * 180 / mp.pi, 10) for a in sw_ang])
# owners at each switch: nearest and 2nd nearest distances
W("   at each switch: two nearest sites and their distances")
for k in sw:
    a = own[k][2]; x = (mp.cos(a), mp.sin(a))
    ds = sorted(((dist(x, C[i]), i) for i in reach))
    W("     ang=%s  d1=%s(site %d) d2=%s(site %d) d3=%s(site %d)" % (
        mp.nstr(a * 180 / mp.pi, 10), mp.nstr(ds[0][0] - r, 4), ds[0][1], mp.nstr(ds[1][0] - r, 4), ds[1][1],
        mp.nstr(ds[2][0] - r, 4), ds[2][1]))

# ---- 3. Voronoi vertices in D
W("")
W("### all in-D Voronoi vertices (empty-circle + circumcenter in D), with r*-comparison")
V = []
for tri in itertools.combinations(range(14), 3):
    u, d = circumcenter(C[tri[0]], C[tri[1]], C[tri[2]])
    if u is None:
        continue
    if norm(u) > 1 + mp.mpf("1e-40"):
        continue
    Rt = dist(u, C[tri[0]])
    others = [dist(u, C[l]) for l in range(14) if l not in tri]
    m = min(others)
    if m < Rt - mp.mpf("1e-25"):
        continue
    V.append(dict(tri=tuple(tri), u=u, R=Rt, absu=norm(u), margin=m - Rt))
W("   n=%d" % len(V))
for v in sorted(V, key=lambda z: (-float(z["R"]), z["tri"])):
    W("   tri%-16s u=(%s,%s) Rtri=%s  Rtri-r*=%s  |u|=%s  empty-margin=%s" % (
        str(v["tri"]), mp.nstr(v["u"][0], 16), mp.nstr(v["u"][1], 16), mp.nstr(v["R"], 20),
        mp.nstr(v["R"] - r, 6), mp.nstr(v["absu"], 16), mp.nstr(v["margin"], 6)))
# cluster by radius
from collections import Counter
cnt = Counter(mp.nstr(v["R"], 12) for v in V)
W("   radius classes: %s" % dict(cnt))
tight = [v for v in V if abs(v["R"] - r) < mp.mpf("1e-20")]
W("   TIGHT (Rtri == r*): %s" % [tuple(v["tri"]) for v in tight])

# ---- 4. old root, same classification
W("")
W("### OLD (nonstationary) refined root, same code path")
Cold, Rold, _ = old_geom_centers()
W("   Rold=%s ; r*-Rold=%s" % (mp.nstr(Rold, 25), mp.nstr(r - Rold, 6)))
Vo = []
for tri in itertools.combinations(range(14), 3):
    u, d = circumcenter(Cold[tri[0]], Cold[tri[1]], Cold[tri[2]])
    if u is None or norm(u) > 1 + mp.mpf("1e-40"):
        continue
    Rt = dist(u, Cold[tri[0]])
    others = [dist(u, Cold[l]) for l in range(14) if l not in tri]
    if min(others) < Rt - mp.mpf("1e-25"):
        continue
    Vo.append(dict(tri=tuple(tri), u=u, R=Rt))
W("   n=%d" % len(Vo))
co = Counter(mp.nstr(v["R"], 12) for v in Vo)
W("   radius classes: %s" % dict(co))
tighto = [v for v in Vo if abs(v["R"] - Rold) < mp.mpf("1e-20")]
W("   TIGHT at old R: %s" % [tuple(v["tri"]) for v in tighto])
W("")
W("   triples present at old but NOT at new: %s" % sorted(set(tuple(v['tri']) for v in Vo) - set(tuple(v['tri']) for v in V)))
W("   triples present at new but NOT at old: %s" % sorted(set(tuple(v['tri']) for v in V) - set(tuple(v['tri']) for v in Vo)))

data = dict(
    r=mp.nstr(r, 50), L=mp.nstr(L, 40),
    reach=reach,
    arcs={str(i): [mp.nstr(phi, 30), mp.nstr(psi, 30)] for i, phi, psi, w in arcs},
    switch_seq=seq,
    switch_deg=[mp.nstr(a * 180 / mp.pi, 20) for a in sw_ang],
    vertices=[dict(tri=list(v["tri"]), u=[mp.nstr(v["u"][0], 30), mp.nstr(v["u"][1], 30)],
                   R=mp.nstr(v["R"], 30), margin=mp.nstr(v["margin"], 20)) for v in sorted(V, key=lambda z: z["tri"])],
    tight=[list(v["tri"]) for v in tight],
    old_vertices=[dict(tri=list(v["tri"]), R=mp.nstr(v["R"], 30)) for v in sorted(Vo, key=lambda z: z["tri"])],
    old_tight=[list(v["tri"]) for v in tighto],
)
(HERE.parent / "logs/step2_boundary.txt").write_text("\n".join(OUT), encoding="utf-8")
(HERE.parent / "evidence/step2_boundary.json").write_text(json.dumps(data, indent=1), encoding="utf-8")
print("\nwrote logs/step2_boundary.txt evidence/step2_boundary.json")
