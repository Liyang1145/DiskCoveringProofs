"""Compact statistics for the nesting-slack hunt + dump of violating configurations."""
import json, math, sys
from pathlib import Path
import numpy as np
from fractions import Fraction

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom_exact import anchor_records, covering_radius
from hunt import premises_ok, load_candidate

def eval_cfg(sites):
    recs, anch = anchor_records(sites)
    if len(recs) == 0:
        return None
    mn = min(min(r["nest_ccw"], r["nest_cw"]) for r in recs)
    mx = max(abs(r["resid"]) for r in recs)
    ok, why = premises_ok(recs, sites)
    return dict(q=len(recs), min_nest=mn, max_resid=mx, premises=ok, why=why,
                r_cov=covering_radius(sites, 150), recs=recs, sites=sites)

if __name__ == "__main__":
    rng = np.random.default_rng(20260927)
    base = load_candidate()
    saved = []
    print("== perturbations of the campaign candidate (14 sites, |c|max=0.9434) ==")
    print("scale    reps  viol  viol&premises  min_nest        max|resid|")
    for scale in (1e-6, 1e-5, 1e-4, 1e-3, 1e-2, 3e-2, 1e-1, 2e-1):
        nv = np_ = 0
        mn = 1e9; mres = 0.0
        for rep in range(120):
            S = base + rng.normal(0, scale, base.shape)
            nrm = np.linalg.norm(S, axis=1)
            bad = nrm > 0.996
            if bad.any():
                S[bad] = S[bad] * (0.996 / nrm[bad])[:, None]
            e = eval_cfg(S)
            if e is None: continue
            mn = min(mn, e["min_nest"]); mres = max(mres, e["max_resid"])
            if e["min_nest"] < -1e-7:
                nv += 1
                if e["premises"]:
                    np_ += 1
                    if len(saved) < 8:
                        saved.append(dict(scale=scale, rep=rep, r_cov=e["r_cov"],
                                          sites=S.tolist(), min_nest=e["min_nest"]))
        print(f"{scale:<8g} {120:4d} {nv:5d} {np_:8d}      {mn:+.6e}   {mres:.3e}")
    print()
    print("== random interior configurations ==")
    print("n     reps  usable  viol  viol&premises  min_nest")
    for n in (8, 9, 10, 11, 12, 14, 16):
        nv = np_ = 0; usable = 0; mn = 1e9
        for rep in range(500):
            rad = rng.uniform(0.3, 0.995, n)
            ang = rng.uniform(0, 2 * math.pi, n)
            S = np.stack([rad * np.cos(ang), rad * np.sin(ang)], 1)
            e = eval_cfg(S)
            if e is None: continue
            usable += 1
            mn = min(mn, e["min_nest"])
            if e["min_nest"] < -1e-7:
                nv += 1
                if e["premises"]:
                    np_ += 1
                    if len(saved) < 8:
                        saved.append(dict(scale=None, rep=rep, n=n, r_cov=e["r_cov"],
                                          sites=S.tolist(), min_nest=e["min_nest"]))
        print(f"{n:3d} {500:6d} {usable:7d} {nv:5d} {np_:8d}      {mn:+.6e}")
    (HERE / "violating-configs.json").write_text(json.dumps(saved, indent=1))
    print("\nsaved", len(saved), "violating configurations to violating-configs.json")
