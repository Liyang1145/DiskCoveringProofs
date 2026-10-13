"""Step 5: bottleneck (max-min distance) of D to the 12 centres, fast + exact-ish.

covering radius of the point set on D  = max over Voronoi vertices inside D of their
circumradius (deep-hole max), plus boundary-arc maxima.
"""
from pathlib import Path
from fractions import Fraction as F
import json, math, itertools
import mpmath as mp
mp.mp.dps = 50

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
A = json.loads((ROOT / "research-2026/session2/n1314/cfg/cert_n12_othern.json").read_text(encoding="utf-8"))
B = json.loads((ROOT / "flash-n11/members/othern-scout/s3/n12_d3_kkt.json").read_text(encoding="utf-8"))

OUT = []
def W(s=""): OUT.append(str(s))

def analyse(tag, cfg, key, Rf):
    cen = [(float(x), float(y)) for x, y in cfg[key]]
    n = len(cen)
    W(f"=========== {tag}: n={n}  R_literal={Rf!r}")
    rad = [math.hypot(*c) for c in cen]
    W("   |c_i| (float): " + " ".join(f"{r:.12f}" for r in rad))
    W(f"   min_i |c_i| = {min(rad):.17g}   R_literal - min = {Rf-min(rad):.3e}")
    # 1. Voronoi vertices inside D: circumcentres of triples whose circumcircle is empty of nearer sites
    worst = []
    for i, j, k in itertools.combinations(range(n), 3):
        ax, ay = cen[i]; bx, by = cen[j]; cx, cy = cen[k]
        den = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
        if abs(den) < 1e-14: continue
        ux = ((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/den
        uy = ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/den
        if ux*ux+uy*uy > 1: continue
        rr = math.dist((ux, uy), (ax, ay))
        # Voronoi vertex iff no 4th site strictly nearer
        dm = min(math.dist((ux, uy), c) for c in cen)
        worst.append((dm, (i, j, k), ux, uy, rr, abs(dm-rr)))
    worst.sort(reverse=True)
    W(f"   Voronoi vertices inside D: {len(worst)}; top 8 by min-dist to sites:")
    for dm, tri, ux, uy, rr, dgap in worst[:8]:
        W(f"     tri{str(tri):<14} u=({ux:+.15f},{uy:+.15f}) |u|={math.hypot(ux,uy):.15f} "
          f"min-dist={dm:.17g}  (degeneracy |dm-rr|={dgap:.2e})")
    # 2. boundary arcs: for each centre that is boundary-active, the arc on S1 it covers
    W("   boundary arcs (centre i, angular interval where |p-c_i|<=R_lit and i is nearest):")
    h = 1e-7
    act = []
    N = 4_000_000
    for t in range(N):
        th = 2*math.pi*t/N
        px, py = math.cos(th), math.sin(th)
        ds = [math.dist((px, py), c) for c in cen]
        q = min(range(n), key=lambda z: ds[z])
        if ds[q] <= Rf:
            act.append((th, q))
    W(f"     #boundary samples with R-cover by nearest centre: {len(act)} / {N}"
      f"   (=> boundary covered: {len(act)==N})")
    # which centres are nearest somewhere on S1 (nearest-ownership)
    own = {}
    for t in range(N):
        th = 2*math.pi*t/N
        px, py = math.cos(th), math.sin(th)
        ds = [math.dist((px, py), c) for c in cen]
        q = min(range(n), key=lambda z: ds[z])
        other = sorted(ds)[1]
        exact = ds[q] < other - 1e-15
        own.setdefault(q, []).append((th, ds[q], exact))
    W("   nearest-owned measure on S1 (arc length) & max distance there:")
    for q in sorted(own):
        ts = own[q]
        W(f"     c{q:2d}: #samples={len(ts):8d} arclen={2*math.pi*len(ts)/N:.9f} "
          f"max|p-c|={max(s[1] for s in ts):.17g}  argmax-theta_deg="
          f"{max(ts, key=lambda s: s[1])[0]*180/math.pi:.4f}  (R_lit={Rf!r})")
    W(f"   => #centres nearest-owned on S1 = {len(own)}")
    # boundary max-min over the whole circle, using the max at switch points
    mx = max((s[1] for q in own for s in own[q]), default=0)
    W(f"   boundary max-min (nearest distance, float) = {mx:.17g};  mx - R_lit = {mx-Rf:.3e}")
    return {"min_rad": min(rad), "voronoi_top": [(str(t), repr(d)) for d, t, *_ in worst[:8]],
            "boundary_owner_count": len(own), "boundary_maxmin": repr(mx)}

res = {}
res["A"] = analyse("A (17-digit literal)", A, "centers_dec17", float(A["R_float"]))
res["B"] = analyse("B (KKT source)", B, "centers", float(B["R_D_mpmath"]))
(EV / "bottleneck.txt").write_text("\n".join(OUT), encoding="utf-8")
(EV / "bottleneck.json").write_text(json.dumps(res, indent=2, default=str), encoding="utf-8")
print("\n".join(OUT))
