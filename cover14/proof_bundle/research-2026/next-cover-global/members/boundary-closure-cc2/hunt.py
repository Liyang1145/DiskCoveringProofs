"""Hunt for a genuine failure of the claimed cyclicity identity, i.e. nesting slack < 0,
under configurations that satisfy every stated premise of
lead/BOUNDARY-ANCHOR-OUTSIDE-EDGE.md + BOUNDARY-CYCLICITY-INTERFACE.md:
  sites distinct + strictly interior; at the anchor exactly two owners and a strict third-site
  margin; every owned arc < pi (excludes the full-chord facet case); the facet [A,O] closes at an
  interior vertex O (|O| < 1); h_A < 0 i.e. gamma_A < pi/2.
"""
import json, math, sys
from pathlib import Path
import numpy as np
from fractions import Fraction

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom_exact import anchor_records, covering_radius

LEAD = HERE.parent.parent / "lead"
rng = np.random.default_rng(20260927)

def load_candidate():
    D = json.loads((LEAD / "improved-upper-test.json").read_text())
    return np.array([[float(Fraction(x)) for x in p] for p in D["centers"]])

def premises_ok(recs, sites, arc_tol=1e-9, tie_tol=1e-9):
    """returns (ok, why) -- all *stated* premises, per anchor and globally."""
    if len(recs) == 0:
        return False, "no anchors"
    issues = []
    for r in recs:
        if r["nmargin"] < tie_tol:
            issues.append(f"anchor {r['k']}: third-site margin {r['nmargin']:.2e} (degenerate)")
        if max(r["theta_ccw"], r["theta_cw"]) > math.pi - arc_tol:
            issues.append(f"anchor {r['k']}: arc >= pi")
        if r["facet"] is None:
            issues.append(f"anchor {r['k']}: no interior facet closure (full chord)")
        else:
            if float(np.linalg.norm(r["facet"][0])) >= 1 - 1e-12:
                issues.append(f"anchor {r['k']}: facet vertex O not interior")
            if r["facet"][2] <= 0:
                issues.append(f"anchor {r['k']}: facet length <= 0")
        if len(r["arc_cw"]) != 1 or len(r["arc_ccw"]) != 1:
            issues.append(f"anchor {r['k']}: arc owner not unique {r['arc_cw']} {r['arc_ccw']}")
        if r["gam"] >= math.pi / 2:
            issues.append(f"anchor {r['k']}: h_A>=0 (gam={r['gam']:.6f})")
    if np.max(np.linalg.norm(sites, axis=1)) >= 1:
        issues.append("site not strictly interior")
    for i in range(len(sites)):
        for j in range(i + 1, len(sites)):
            if np.linalg.norm(sites[i] - sites[j]) < 1e-9:
                issues.append("coincident sites")
    return (len(issues) == 0), "; ".join(issues)

def evaluate(sites, name, fh, do_print=False):
    recs, anch = anchor_records(sites)
    if len(recs) == 0:
        return None
    mn = min(min(r["nest_ccw"], r["nest_cw"]) for r in recs)
    mx = max(abs(r["resid"]) for r in recs)
    ok, why = premises_ok(recs, sites)
    rec = dict(name=name, q=len(recs), min_nest=mn, max_abs_resid=mx, premises=ok, why=why,
               r_cov=covering_radius(sites, 200))
    if mn < -1e-7:
        print(f"*** NESTING VIOLATION {name}: min_nest={mn:+.6e} max|resid|={mx:.3e} "
              f"premises_ok={ok} r_cov={rec['r_cov']:.4f}")
        if why: print("    premise issues:", why)
        if fh: fh.write(f"VIOLATION {name} min_nest={mn!r} resid={mx!r} premises={ok} why={why} "
                        f"r_cov={rec['r_cov']!r}\n")
        for r in recs:
            for tag, val in (("ccw", r["nest_ccw"]), ("cw", r["nest_cw"])):
                if val < -1e-9:
                    s = (f"      k={r['k']} t={r['t']:.9f} side={tag} nest={val:+.6e} "
                         f"pair={r['pair']} arc_cw={r['arc_cw']} arc_ccw={r['arc_ccw']} "
                         f"th_cw={r['theta_cw']:.9f} th_ccw={r['theta_ccw']:.9f} gam={r['gam']:.9f} "
                         f"ang_m={r['ang_m']:.9f} resid={r['resid']:+.6e} nmargin={r['nmargin']:.2e} "
                         f"facet_scale={None if r['facet'] is None else round(r['facet'][2],6)}")
                    print(s)
                    if fh: fh.write(s + "\n")
        rec["sites"] = sites.tolist()
    return rec

if __name__ == "__main__":
    fh = open(HERE / "hunt-violations.txt", "w")
    base = load_candidate()
    print("== perturbation family around the campaign candidate ==")
    worst = []
    for scale in (1e-6, 1e-5, 1e-4, 1e-3, 1e-2, 3e-2, 1e-1):
        mn_all = 1e9; nviol = 0
        for rep in range(60):
            S = base + rng.normal(0, scale, base.shape)
            # keep strictly interior
            nrm = np.linalg.norm(S, axis=1)
            bad = nrm > 0.995
            if bad.any():
                S[bad] = S[bad] * (0.995 / nrm[bad])[:, None]
            rec = evaluate(S, f"perturb scale={scale} rep={rep}", fh)
            if rec is None: continue
            mn_all = min(mn_all, rec["min_nest"])
            if rec["min_nest"] < -1e-7: nviol += 1
        print(f"scale={scale:<7g}  min over {60} reps of min_nest = {mn_all:+.4e}   violations={nviol}")
    print()
    print("== random interior configurations (no covering requirement) ==")
    for n in (9, 10, 11, 12, 14):
        mn_all = 1e9; nviol = 0; nok = 0
        for rep in range(400):
            rad = rng.uniform(0.35, 0.995, n)
            ang = rng.uniform(0, 2 * math.pi, n)
            S = np.stack([rad * np.cos(ang), rad * np.sin(ang)], 1)
            rec = evaluate(S, f"random n={n} rep={rep}", fh)
            if rec is None: continue
            nok += 1
            mn_all = min(mn_all, rec["min_nest"])
            if rec["min_nest"] < -1e-7: nviol += 1
        print(f"n={n:2d}  usable={nok:3d}  min min_nest={mn_all:+.4e}  violations={nviol}")
    fh.close()
