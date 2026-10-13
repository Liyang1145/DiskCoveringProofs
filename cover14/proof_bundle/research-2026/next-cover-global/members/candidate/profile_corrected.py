"""Corrected, reproducible numeric profile summary (JSON) for n=13/14/15.

Every number is numeric; no claim of exactness.  Interface fixes applied:
  * symmetry searched over ALL axes, not just x/y;
  * Voronoi vertices (nearest-site filtered) separated from raw triple circumcentres;
  * D2 orbits computed from the actual permutations;
  * dimension conventions stated correctly.
"""
from pathlib import Path
from collections import Counter
import json, itertools, sys
import mpmath as mp
mp.mp.dps = 50

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
S2 = ROOT / "research-2026/session2/n1314"
CAND = ROOT / "research-2026/next-cover-global/members/candidate"
EV = CAND / "evidence"
dd = lambda p, q: mp.sqrt((p[0]-q[0])**2+(p[1]-q[1])**2)
nn = lambda p: mp.sqrt(p[0]**2+p[1]**2)
def circ(p, q, s):
    ax, ay = p; bx, by = q; cx, cy = s
    den = 2*((ax-cx)*(by-cy)-(ay-cy)*(bx-cx))
    if abs(den) < mp.mpf('1e-40'): return None
    return (((ax*ax+ay*ay-cx*cx-cy*cy)*(by-cy)-(ay-cy)*(bx*bx+by*by-cx*cx-cy*cy))/den,
            ((ax-cx)*(bx*bx+by*by-cx*cx-cy*cy)-(ax*ax+ay*ay-cx*cx-cy*cy)*(bx-cx))/den)

def full_profile(tag, cent, Rstr):
    m = len(cent)
    R = mp.mpf(Rstr) if Rstr else None
    rad = [nn(c) for c in cent]
    # --- Voronoi vertices inside D (nearest-site filtered)
    vv = []
    raw_in = 0
    for tri in itertools.combinations(range(m), 3):
        u = circ(cent[tri[0]], cent[tri[1]], cent[tri[2]])
        if u is None or nn(u) > 1: continue
        raw_in += 1
        ds = sorted((dd(u, c), t) for t, c in enumerate(cent))
        if set(x for _, x in ds[:3]) != set(tri): continue
        vv.append({"tri": list(tri), "u": [mp.nstr(u[0], 24), mp.nstr(u[1], 24)],
                   "abs_u": mp.nstr(nn(u), 20), "f": mp.nstr(ds[0][0], 24),
                   "f_minus_R": (mp.nstr(ds[0][0]-R, 8) if R else None),
                   "nearest3": [x for _, x in ds[:3]], "slack_4th": mp.nstr(ds[3][0]-ds[0][0], 10)})
    vv.sort(key=lambda z: -float(mp.mpf(z["f"])))
    # --- boundary-active owners (arc owners on S1)
    own = {}
    N = 200000
    for s in range(N):
        th = 2*mp.pi*s/N
        p = (mp.cos(th), mp.sin(th))
        ds = [dd(p, c) for c in cent]
        q = ds.index(min(ds)); own[q] = own.get(q, 0)+1
    bound = sorted(own)
    # --- symmetry, all axes
    bestm = None
    for k in range(4*m):
        ph = mp.pi*k/(4*m)
        c2, s2 = mp.cos(2*ph), mp.sin(2*ph)
        dev = mp.mpf(0)
        for i in range(m):
            q = (c2*cent[i][0]+s2*cent[i][1], s2*cent[i][0]-c2*cent[i][1])
            dev = max(dev, min(dd(q, c) for c in cent))
        if bestm is None or dev < bestm[0]: bestm = (dev, 180*k/(4*m))
    bestr = None
    for k in range(1, 4*m):
        th = 2*mp.pi*k/(4*m)
        cc, ss = mp.cos(th), mp.sin(th)
        dev = mp.mpf(0)
        for i in range(m):
            q = (cc*cent[i][0]-ss*cent[i][1], ss*cent[i][0]+cc*cent[i][1])
            dev = max(dev, min(dd(q, w) for w in cent))
        if bestr is None or dev < bestr[0]: bestr = (dev, 360*k/(4*m))
    # --- exact symmetry test (permutation based)
    def perm_of(g):
        return [min(range(m), key=lambda t: dd(g(cent[i]), cent[t])) for i in range(m)]
    def cycles(pm):
        seen, out = set(), []
        for i in range(m):
            if i in seen: continue
            cyc, cur = [], i
            while cur not in seen:
                seen.add(cur); cyc.append(cur); cur = pm[cur]
            out.append(cyc)
        return out
    px = perm_of(lambda p: (p[0], -p[1])); py = perm_of(lambda p: (-p[0], p[1]))
    pc2 = perm_of(lambda p: (-p[0], -p[1]))
    # D2 orbits
    seen, dorbs = set(), []
    for i in range(m):
        if i in seen: continue
        o = {i}
        for _ in range(3):
            o = set().union(*[{px[j], py[j], pc2[j]} for j in o])
        dorbs.append(sorted(o)); seen.update(o)
    mult = Counter(mp.nstr(r, 9) for r in rad)
    return {"tag": tag, "n": m, "R_used": Rstr,
            "radii": [mp.nstr(r, 24) for r in rad],
            "norm_multiplicities_rounded": sorted(mult.values(), reverse=True),
            "n_distinct_norms": len(mult),
            "boundary_active": bound, "n_boundary_active": len(bound),
            "interior": sorted(set(range(m))-set(bound)),
            "raw_triples_with_circumcentre_in_D": raw_in,
            "n_voronoi_vertices_in_D": len(vv),
            "deepest_6": vv[:6],
            "n_active_holes_f_eq_R_1e15": (sum(1 for z in vv if abs(mp.mpf(z["f"])-R) < mp.mpf('1e-15')) if R else None),
            "symmetry": {
                "best_mirror_axis_deg": bestm[1], "best_mirror_residual": mp.nstr(bestm[0], 10),
                "best_rotation_deg": bestr[1], "best_rotation_residual": mp.nstr(bestr[0], 10),
                "sigma_x_cycles": cycles(px), "sigma_y_cycles": cycles(py), "c2_cycles": cycles(pc2),
                "D2_orbits": dorbs, "D2_orbit_sizes": sorted(len(o) for o in dorbs)},
            "dimension_note": ("configuration space = 2n coordinates minus the 1-dim rotation "
                               "gauge (centres not all at the origin) = 2n-1")}

D14 = json.loads((ROOT / "research-2026/session2/type14/out/hprec_sol.json").read_text(encoding="utf-8"))
C14 = [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in D14["centers"]]
res = {}
res["n13"] = full_profile("n13 (17-digit literal)",
                          [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in
                           json.loads((S2/"cfg/cert_n13_v1.json").read_text())["centers_dec17"]],
                          "0.34664545692738974")
res["n14_hprec"] = full_profile("n14 (hprec_sol.json, C411 object)", C14, D14["R"])
res["n14_literal"] = full_profile("n14 (17-digit literal cert_n14_v1)",
                                  [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in
                                   json.loads((S2/"cfg/cert_n14_v1.json").read_text())["centers_dec17"]],
                                  "0.3317320342762342")
res["n15"] = full_profile("n15 (17-digit literal)",
                          [(mp.mpf(str(x)), mp.mpf(str(y))) for x, y in
                           json.loads((S2/"cfg/cert_n15_v1.json").read_text())["centers_dec17"]],
                          "0.31814293085926293")
(EV / "profile_corrected.json").write_text(json.dumps(res, indent=2), encoding="utf-8")
print(json.dumps({k: {"n": v["n"], "n_voronoi_vertices_in_D": v["n_voronoi_vertices_in_D"],
                      "raw_triples_in_D": v["raw_triples_with_circumcentre_in_D"],
                      "n_boundary_active": v["n_boundary_active"],
                      "D2_orbit_sizes": v["symmetry"]["D2_orbit_sizes"],
                      "best_mirror_residual": v["symmetry"]["best_mirror_residual"],
                      "best_mirror_axis": v["symmetry"]["best_mirror_axis_deg"],
                      "best_rotation_residual": v["symmetry"]["best_rotation_residual"],
                      "n_active_holes": v["n_active_holes_f_eq_R_1e15"]}
                 for k, v in res.items()}, indent=2))
