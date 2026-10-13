"""Run 1: fammin (record) configuration -- ledger calibration + Voronoi/Delaunay + hole structure.

Checks (all independently coded here, no import from producer scripts):
  L1 ledger reconstruction from the 11 centres, (I)(II)(III) and staircase
  L2 |v_out|=1 iff o=0 ; |v_in|<1<|v_out|
  L3 tips-lemma margin: min_{j not in {k,k+1}} |v_k-c_j| - r
  L4 inward-ray witness for each tip (v_k in cl(H))
  V1 hub cells inside D and inside B(h,r)   (sampled Voronoi cells)
  V2 Delaunay/Voronoi adjacency graph: hub-hub, ring-ring consecutive, ring-ring non-consecutive
  V3 H is contained in the two hub cells: no hole point has a ring centre as nearest
  V4 connectedness of H (grid flood fill) + cl(H) subset conv(tips)
"""
import json
import math
import os
import sys

import numpy as np
from scipy.spatial import Delaunay

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vgeom as V  # noqa: E402

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", ".."))
CFG = os.path.join(ROOT, "research-2026", "team-20260923", "analytic-11", "fammin_config.json")
OUT = os.path.join(ROOT, "research-2026", "team-current", "flash-structure", "out")
os.makedirs(OUT, exist_ok=True)

rep = []
def P(*a):
    s = " ".join(str(x) for x in a)
    rep.append(s)
    print(s)

js, cen = V.load_fammin(CFG)
r = float(js["R_struct"][:20])
P(f"[cfg] R_struct={js['R_struct']}")
P(f"[cfg] r used = {r!r}")

ring, hub = V.classify(cen, r)
P(f"[L0] #ring={len(ring)} ring={ring}")
P(f"[L0] #hub={len(hub)} hub={hub}")
for i in hub:
    P(f"     hub {i}: |c|={math.hypot(*cen[i]):.6f}  |c|+r={math.hypot(*cen[i])+r:.6f}")
for i in ring:
    a = math.hypot(*cen[i])
    P(f"     ring {i}: |c|={a:.6f} t={math.degrees(V.t_from_center(a,r)):.7f} deg")

# ---- L1: rebuild the ledger from the actual centres, on the cyclic order of ring arcs
ang = {}
for i in ring:
    ang[i] = math.atan2(cen[i][1], cen[i][0]) % (2 * math.pi)
order = sorted(ring, key=lambda i: ang[i])
t = [V.t_from_center(math.hypot(*cen[i]), r) for i in order]
phis = [ang[i] for i in order]
o = V.ledger_from_arcs(r, phis, t)
P("[L1] cyclic ring order (labelled by cfg index):", order)
P("[L1] t (deg):", " ".join(f"{math.degrees(x):.6f}" for x in t))
P("[L1] o (deg):", " ".join(f"{math.degrees(x):.3e}" for x in o))
P(f"[L1] sum t - pi = {sum(t)-math.pi:+.3e} rad   sum o - (2 sum t - 2pi) = "
  f"{sum(o)-(2*sum(t)-2*math.pi):+.3e}")
au = V.audit_ledger(r, t, o)
P(f"[L1] ell_i (rad): {' '.join(f'{x:.3e}' for x in au['ell'])}")
P(f"[L1] cover={au['cover']}  only-adjacent(nonadj disjoint)={au['nonadj']}  "
  f"min ell={min(au['ell']):.3e}  max arc 2t={2*max(t):.6f} rad vs 2asin r={2*math.asin(r):.6f}")
P(f"[L1] each arc essential(all ell>0): {min(au['ell'])>0}")

# ---- independent re-derivation of the ledger from the actual disk/circle geometry
# NOTE: all ring computations must use the CYCLIC order, not the config index order.
def tips_cyclic(r, t, o):
    phi, cen, gamma = V.build_ring(r, t, o)
    out = []
    for i in range(len(t)):
        p_in, p_out, M, h, d = V.crossings(r, cen[i], cen[(i + 1) % len(t)])
        out.append(dict(i=i, a=p_in, b=p_out, M=M, h=h, d=d,
                        ra=V.dist(p_in, (0, 0)), rb=V.dist(p_out, (0, 0))))
    for e in out:  # v_in := the crossing inside D (|v|<1)
        e["v"], e["r_in"], e["v_out"], e["r_out"] = ((e["a"], e["ra"], e["b"], e["rb"])
                                                     if e["ra"] < e["rb"] else
                                                     (e["b"], e["rb"], e["a"], e["ra"]))
    return out

def tip_margin(r, t, o):
    phi, cen, gamma = V.build_ring(r, t, o)
    n = len(t)
    worst = (float("inf"), None)
    tab = []
    for k in range(n):
        tt_ = tips_cyclic(r, t, o)
        p = tt_[k]["v"]
        m, arg = float("inf"), None
        for j in range(n):
            if j in (k, (k + 1) % n):
                continue
            val = V.dist(p, cen[j]) - r
            if val < m:
                m, arg = val, j
        tab.append((k, m, arg))
        if m < worst[0]:
            worst = (m, (k, arg))
    return worst, tab

def ray_clear(r, t, o, k, eps_list=(1e-3, 1e-4, 1e-5)):
    phi, cen, gamma = V.build_ring(r, t, o)
    n = len(t)
    tc = tips_cyclic(r, t, o)
    p = tc[k]["v"]
    rv = math.hypot(*p)
    ux, uy = p[0] / rv, p[1] / rv
    res = []
    for eps in eps_list:
        q = (p[0] - eps * ux, p[1] - eps * uy)
        res.append(dict(eps=eps, inside_D=math.hypot(*q) < 1.0,
                        min_clear=min(V.dist(q, cen[j]) - r for j in range(n))))
    return res

tt = tips_cyclic(r, t, o)
P("[L2] tips (inner/outer crossings):")
for e in tt:
    tol = e["r_out"] - 1.0
    P(f"     k={e['i']}: |v_in|={e['r_in']:.9f}  |v_out|={e['r_out']:.9f}  |v_out|-1={tol:+.2e}"
      f"  o_k={math.degrees(o[e['i']]):.3e} deg")
P(f"[L2] max |v_in| = {max(e['r_in'] for e in tt):.9f}   1-r = {1-r:.9f}   1-2r={1-2*r:.9f}")
cf = [math.sqrt(V.closed_form_tip_sq(r, t[i], t[(i+1) % 9], au["gamma"][i])) for i in range(9)]
P("[L2] closed-form |v_in| vs numeric:", " ".join(
    f"{a:.9f}/{b:.9f}" for a, b in zip(cf, [e["r_in"] for e in tt])))

# ---- L3 tips lemma margin
worst, tab = tip_margin(r, t, o)
P(f"[L3] tips-lemma worst margin = {worst[0]:+.6e} at (k,j)={worst[1]}")
P("[L3] per-k margins:", " ".join(f"{k}:{m:+.4e}(j={j})" for k, m, j in tab))

# ---- L4 inward-ray witness
P("[L4] inward radial ray from each tip (must stay in D and outside all ring disks):")
ok_all = True
for k in range(9):
    res = ray_clear(r, t, o, k)
    ok = all(x["inside_D"] and x["min_clear"] > 0 for x in res)
    ok_all &= ok
    P(f"     k={k}: ok={ok} " + " ".join(f"[eps={x['eps']:g} clear={x['min_clear']:+.3e}]" for x in res))
P(f"[L4] all 9 tips have a radial-ray witness in cl(H): {ok_all}")

# ---- V1/V2 Voronoi + Delaunay on the full 11 centres
pts = np.array(cen)
tri = Delaunay(pts)
edges = set()
for s in tri.simplices:
    for a in range(3):
        i, j = int(s[a]), int(s[(a + 1) % 3])
        edges.add((min(i, j), max(i, j)))
hubset = set(hub)
rpos = {idx: pos for pos, idx in enumerate(order)}   # cyclic position of ring index
P(f"[V2] Delaunay edges n={len(edges)}")
hh = [e for e in edges if e[0] in hubset and e[1] in hubset]
P(f"[V2] hub-hub Delaunay edge: {hh}  -> hub cells adjacent: {len(hh)>0}")
rr = [e for e in edges if e[0] in ring and e[1] in ring]
def cyclic_gap(e):
    a, b = rpos[e[0]], rpos[e[1]]
    d = abs(a - b)
    return min(d, 9 - d)
rr_consec = [e for e in rr if cyclic_gap(e) == 1]
rr_nonconsec = sorted(e for e in rr if cyclic_gap(e) >= 2)
P(f"[V2] ring-ring Delaunay edges: {len(rr)} (consecutive {len(rr_consec)}, non-consecutive "
  f"{len(rr_nonconsec)})")
P(f"[V2] non-consecutive ring-ring chords: {[(e, cyclic_gap(e)) for e in rr_nonconsec]}")
rh = sorted(e for e in edges if (e[0] in hubset) ^ (e[1] in hubset))
P(f"[V2] hub-ring Delaunay edges: {len(rh)}")
# hub cell area/scale check via sampled points
P("[V2] nearest-centre census on a polar grid (which cell owns how many sample points):")
NG, NR = 720, 400
th = np.linspace(0, 2 * math.pi, NG, endpoint=False)
rr_ = np.linspace(0.0005, 1.0, NR)
TT, RR = np.meshgrid(th, rr_)
X, Y = RR * np.cos(TT), RR * np.sin(TT)
mind = np.full(X.shape, np.inf)
near = np.zeros(X.shape, dtype=int)
mind_ring = np.full(X.shape, np.inf)
for idx, (cx, cy) in enumerate(pts):
    dd = np.hypot(X - cx, Y - cy)
    upd = dd < mind
    mind = np.where(upd, dd, mind)
    near = np.where(upd, idx, near)
    if idx in set(ring):
        mind_ring = np.minimum(mind_ring, dd)
cover = mind <= r            # D covered by all 11 disks
hole = (RR <= 1.0) & (mind_ring > r)   # hole H of the RING only
cnt = {i: int(np.sum(near == i)) for i in range(11)}
P("     cell sample counts:", {k: v for k, v in sorted(cnt.items())})
ringset = set(ring)
und = hole
# hub cells inside B(h,r): check nearest-centre cell points are within r of their hub
for pos, i in enumerate(hub):
    m = (near == i)
    dd = np.sqrt((X[m] - pts[i, 0]) ** 2 + (Y[m] - pts[i, 1]) ** 2)
    rad = np.sqrt(X[m] ** 2 + Y[m] ** 2)
    P(f"[V1] hub {i}: sampled cell size={m.sum()}, max|p-h|={dd.max():.6f} (r={r:.6f}), "
      f"max|p|={rad.max():.6f} (<1 => inside D)")

viol = int(np.sum(und & np.isin(near, list(ringset))))
P(f"[V3] hole samples whose nearest centre is a RING centre: {viol}  (claim: 0)")
cnt_hub = [int(np.sum(und & (near == i))) for i in hub]
P(f"[V3] hole samples owned by hub cells {hub}: {cnt_hub}  (sum={sum(cnt_hub)}, total hole={int(und.sum())})")
P(f"[V3] coverage check: uncovered samples of D among all 11 disks: {int(np.sum(~cover))}")

# ---- V4 connectedness of H + conv(tips)
from scipy import ndimage
from scipy.spatial import ConvexHull
lab = np.zeros_like(und, dtype=bool)
lab[und] = True
st = np.ones((3, 3), bool)
lab2, ncomp = ndimage.label(lab, structure=st)
sizes = ndimage.sum(lab, lab2, range(1, ncomp + 1))
order_sz = np.argsort(sizes)[::-1]
P(f"[V4] polar-grid hole components: n={ncomp}, sizes(top5)={[int(sizes[i]) for i in order_sz[:5]]}")
P(f"[V4] grid resolution: dtheta={math.degrees(2*math.pi/NG):.3f} deg, dr={1.0/NR:.2e} "
  f"(component count on a polar grid is only as good as this resolution)")
# Cartesian grid for a sharper check
NG2 = 1400
xs = np.linspace(-1, 1, NG2)
XX, YY = np.meshgrid(xs, xs)
inD = XX ** 2 + YY ** 2 <= 1.0
mindC = np.full(XX.shape, np.inf)
mindAllC = np.full(XX.shape, np.inf)
nearC = np.zeros(XX.shape, dtype=int)
ptsf = [(float(a), float(b)) for a, b in pts]
for idx, (cx, cy) in enumerate(ptsf):
    dd = np.hypot(XX - cx, YY - cy)
    mindAllC = np.minimum(mindAllC, dd)
    if idx in set(ring):
        mindC = np.minimum(mindC, dd)
    upd = dd < mindAllC
holeC = inD & (mindC > r)
lab3, n3 = ndimage.label(holeC, structure=st)
s3 = ndimage.sum(holeC, lab3, range(1, n3 + 1))
P(f"[V4] cartesian {NG2}x{NG2}: hole components = {n3}, sizes(top5)="
  f"{[int(x) for x in np.sort(s3)[::-1][:5]]}")
P(f"[V4] cartesian coverage of D by all 11 disks, uncovered samples: "
  f"{int(np.sum(inD & (mindAllC > r)))}")
# conv(tips) membership via ConvexHull half-space test
vtips = np.array([e["v"] for e in tt])
hull = ConvexHull(vtips)
# hull.equations: [A|b] with A.x + b <= 0 for points inside
Pts = np.stack([XX[holeC], YY[holeC]], axis=1)
val = Pts @ hull.equations[:, :2].T + hull.equations[:, 2]
outside = int(np.sum(np.any(val > 1e-12, axis=1)))
P(f"[V4] hull of 9 tips: vertices used={len(hull.vertices)}  hole points outside conv(tips)={outside} "
  f"/ {int(holeC.sum())}")
if outside:
    k = np.argmax(np.max(val, axis=1))
    P(f"     worst hole point {Pts[k]} excess={float(np.max(val[k])):.3e}")

with open(os.path.join(OUT, "run1_fammin_structure.txt"), "w", encoding="utf-8") as fh:
    fh.write("\n".join(rep) + "\n")
print("written", os.path.join(OUT, "run1_fammin_structure.txt"))
