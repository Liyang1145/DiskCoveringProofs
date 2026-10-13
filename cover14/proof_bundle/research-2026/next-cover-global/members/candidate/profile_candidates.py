"""Finite comparison of saved best candidates n=13/14/15 for the global covering problem.

NUMERIC PROFILE ONLY (no certification): for each saved 17-digit literal configuration
  * exact rational read of the literal (identity check)
  * |c_i| spectrum, boundary-active test  (rho_i + r_i ~ 1  <=>  disk touches S1)
  * Voronoi vertices inside D  -> deepest holes f = min_i |u - c_i|
  * boundary max-min over S1
  * which centres own an arc on S1 and which own a Voronoi region
  * Ck rotation / reflection symmetry residuals
  * slack/redundant centres (no boundary arc AND no deep-hole incidence)
Sources (read-only):
  research-2026/session2/n1314/cfg/cert_n1{3,4,5}_v1.json
  research-2026/session2/n1314/out/cert_n1{3,4,5}_v1.json  (certified R interval)
"""
from pathlib import Path
from fractions import Fraction as F
import json, math, itertools
import mpmath as mp
mp.mp.dps = 50

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
S2 = ROOT / "research-2026/session2/n1314"
CAND = ROOT / "research-2026/next-cover-global/members/candidate"
EV = CAND / "evidence"
EV.mkdir(parents=True, exist_ok=True)
OUT = []
def W(s=""): OUT.append(str(s))

def profile(n):
    cfgp = S2 / f"cfg/cert_n{n}_v1.json"
    outp = S2 / f"out/cert_n{n}_v1.json"
    cfg = json.loads(cfgp.read_text(encoding="utf-8"))
    outj = json.loads(outp.read_text(encoding="utf-8")) if outp.exists() else {}
    cent = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in cfg["centers_dec17"]]
    Rf = mp.mpf(cfg["R_float"])
    W("="*100)
    W(f"### n={n}   source cfg={cfgp.name}   R_float(literal)={mp.nstr(Rf,30)}")
    if outj:
        W("    certified output json keys: " + ", ".join(sorted(outj.keys())))
        for k in ("claim", "r_mp", "d2_argmax", "bb_ok", "bb_stats"):
            if k in outj:
                W(f"      {k} = {outj[k] if not isinstance(outj[k], dict) else json.dumps(outj[k])}")
    # |c| spectrum
    rad = [mp.sqrt(c[0]**2+c[1]**2) for c in cent]
    ang = [mp.atan2(c[1], c[0]) for c in cent]
    W(f"[radii] |c_i| - (1-R) : (positive => centre outside 1-R ring)")
    for i in range(n):
        W(f"   {i:2d} |c|={mp.nstr(rad[i],22):<26} |c|-(1-R)={mp.nstr(rad[i]-(1-Rf),10):<16}"
          f" |c|+R={mp.nstr(rad[i]+Rf,22):<24} touchS1={abs(rad[i]+Rf-1)<1e-9}")
    # Voronoi vertices in D
    verts = []
    for i, j, k in itertools.combinations(range(n), 3):
        ax, ay = cent[i]; bx, by = cent[j]; cx, cy = cent[k]
        den = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
        if abs(float(den)) < 1e-14: continue
        ux = ((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/den
        uy = ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/den
        if ux*ux+uy*uy > 1: continue
        dd = sorted((mp.sqrt((ux-c[0])**2+(uy-c[1])**2), t) for t, c in enumerate(cent))
        verts.append((dd[0][0], (i, j, k), (ux, uy), [t for _, t in dd[:4]]))
    verts.sort(key=lambda z: -z[0])
    W(f"[holes] Voronoi vertices with circumcentre in D: {len(verts)}")
    W(f"   deepest 8 by f=min_i|u-c_i|:")
    for f, tri, u, near in verts[:8]:
        W(f"     tri{str(tri):<18} u=({mp.nstr(u[0],16)},{mp.nstr(u[1],16)}) |u|={mp.nstr(mp.sqrt(u[0]**2+u[1]**2),16)}"
          f"  f={mp.nstr(f,26)}  f-R={mp.nstr(f-Rf,8)}  near={near}")
    # boundary
    N = 400_000
    bb = (-1, None)
    for s in range(N):
        th = 2*mp.pi*s/N
        p = (mp.cos(th), mp.sin(th))
        d = min(mp.sqrt((p[0]-c[0])**2+(p[1]-c[1])**2) for c in cent)
        if d > bb[0]: bb = (d, th)
    W(f"[boundary] max-min over S1 = {mp.nstr(bb[0],26)} at theta_deg={mp.nstr(bb[1]*180/mp.pi,12)}"
      f"   (R_f - this = {mp.nstr(Rf-bb[0],8)})")
    # boundary owners
    own = {}
    for s in range(400_000):
        th = 2*mp.pi*s/400_000
        p = (mp.cos(th), mp.sin(th))
        ds = [mp.sqrt((p[0]-c[0])**2+(p[1]-c[1])**2) for c in cent]
        q = ds.index(min(ds))
        own[q] = own.get(q, 0)+1
    W(f"[boundary-active] {len(own)} centres own an arc on S1: {sorted(own)}")
    hub = [i for i in range(n) if i not in own]
    W(f"   NOT boundary-active (interior): {hub}")
    # deep-hole incidences
    inc = set()
    for f, tri, u, near in verts[:12]:
        inc.update(near)
    W(f"[hole-incidence] centres appearing in the top-12 holes' nearest sets: {sorted(inc)}")
    # symmetry
    W(f"[symmetry] rotation/reflection residuals (max_i min_j |g(c_i)-c_j|)")
    for k in range(1, n):
        dev = 0
        th = 2*mp.pi*k/n
        c_, s_ = mp.cos(th), mp.sin(th)
        for i in range(n):
            q = (c_*cent[i][0]-s_*cent[i][1], s_*cent[i][0]+c_*cent[i][1])
            dev = max(dev, min(mp.sqrt((q[0]-c[0])**2+(q[1]-c[1])**2) for c in cent))
        if dev < 1e-8:
            W(f"   rotation by 2pi*{k}/{n} = {360*k/n:.1f} deg : {mp.nstr(dev,6)}  <-- SYMMETRY")
    best_ref = None
    for k in range(2*n):
        ph = mp.pi*k/(2*n)
        c2, s2 = mp.cos(2*ph), mp.sin(2*ph)
        dev = 0
        for i in range(n):
            q = (c2*cent[i][0]+s2*cent[i][1], s2*cent[i][0]-c2*cent[i][1])
            dev = max(dev, min(mp.sqrt((q[0]-c[0])**2+(q[1]-c[1])**2) for c in cent))
        if best_ref is None or dev < best_ref[0]:
            best_ref = (dev, 180*k/(2*n))
    W(f"   best reflection axis {best_ref[1]:.2f} deg : {mp.nstr(best_ref[0],6)}"
      f"   {'<-- MIRROR' if best_ref[0] < 1e-8 else ''}")
    # radial shells
    shells = {}
    for i in range(n):
        key = mp.nstr(rad[i], 10)
        shells.setdefault(key, []).append(i)
    W(f"[shells] {len(shells)} distinct |c| shells:")
    for k, v in sorted(shells.items(), key=lambda kv: float(kv[0])):
        W(f"   |c|={k:<16} size={len(v):2d}  {v}")
    # slack centres: not boundary-active
    W(f"[summary] n={n}: R_float={Rf}  boundary-active={len(own)}  interior={n-len(own)}"
      f"  deepest hole f={mp.nstr(verts[0][0],24)}  f-R={mp.nstr(verts[0][0]-Rf,6)}")
    W("")
    return {"n": n, "R_float": str(Rf), "n_boundary_active": len(own), "n_interior": n-len(own),
            "deepest_hole_f": mp.nstr(verts[0][0], 24), "f_minus_R": mp.nstr(verts[0][0]-Rf, 6),
            "boundary_maxmin": mp.nstr(bb[0], 24), "boundary_minus_R": mp.nstr(bb[0]-Rf, 6),
            "shells": {k: v for k, v in shells.items()},
            "deepest_triple": list(verts[0][1]), "deepest_nearest": verts[0][3],
            "top_holes": [[mp.nstr(f, 20), list(tri), [mp.nstr(u[0], 18), mp.nstr(u[1], 18)]]
                          for f, tri, u, _ in verts[:8]],
            "boundary_not_active": hub}

res = {}
for n in (13, 14, 15):
    res[n] = profile(n)
(EV / "profile_n13_14_15.txt").write_text("\n".join(OUT), encoding="utf-8")
(EV / "profile_n13_14_15.json").write_text(json.dumps(res, indent=2, default=str), encoding="utf-8")
print("\n".join(OUT))
