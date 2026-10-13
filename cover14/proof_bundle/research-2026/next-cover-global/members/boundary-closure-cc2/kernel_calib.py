"""Calibrate the exact kernel against the sampled kernel on the campaign candidate,
then hunt for nesting-slack violations (which are exactly the failures of the
claimed cyclicity identity)."""
import json, math, sys
from pathlib import Path
import numpy as np
from fractions import Fraction

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom_exact import anchor_records, anchors_exact, covering_radius

LEAD = HERE.parent.parent / "lead"

def load_candidate():
    D = json.loads((LEAD / "improved-upper-test.json").read_text())
    return np.array([[float(Fraction(x)) for x in p] for p in D["centers"]]), D

def summarize(tag, recs, fh=None):
    q = len(recs)
    mx = max(abs(r["resid"]) for r in recs)
    ming = min(r["gam"] for r in recs); maxg = max(r["gam"] for r in recs)
    nmin = min(min(r["nest_ccw"], r["nest_cw"]) for r in recs)
    amin = min(min(r["theta_ccw"], r["theta_cw"]) for r in recs)
    amax = max(max(r["theta_ccw"], r["theta_cw"]) for r in recs)
    sym = max(r["sym_err"] for r in recs)
    line = (f"{tag}: q={q} max|resid|={mx:.3e} gam in [{ming:.9f},{maxg:.9f}] pi/2={math.pi/2:.9f} "
            f"min nest={nmin:+.6e} arcs [{amin:.6f},{amax:.6f}] sym_err={sym:.2e}")
    print(line)
    if fh: fh.write(line + "\n")
    return line

def detail(tag, recs, fh, only_bad=True):
    for r in recs:
        bad = (r["nest_ccw"] < -1e-9) or (r["nest_cw"] < -1e-9) or abs(r["resid"]) > 1e-9
        if only_bad and not bad:
            continue
        s = (f"   {tag} k={r['k']} t={r['t']:.9f} pair={r['pair']} arc_cw={r['arc_cw']} "
             f"arc_ccw={r['arc_ccw']} th_cw={r['theta_cw']:.9f} th_ccw={r['theta_ccw']:.9f} "
             f"gam={r['gam']:.9f} ang_m={r['ang_m']:.9f} nest_ccw={r['nest_ccw']:+.3e} "
             f"nest_cw={r['nest_cw']:+.3e} resid={r['resid']:+.3e} nmargin={r['nmargin']:.2e}")
        print(s)
        if fh: fh.write(s + "\n")

if __name__ == "__main__":
    sites, D = load_candidate()
    log = open(HERE / "hunt-log.txt", "w")
    recs, anch = anchor_records(sites)
    print("candidate (exact kernel):", len(anch), "anchors, covering radius grid=",
          round(covering_radius(sites, 400), 6))
    summarize("candidate", recs, log)
    for r in recs:
        print(f"  k={r['k']} t={r['t']:.9f} pair={r['pair']} arc_cw={r['arc_cw']} arc_ccw={r['arc_ccw']} "
              f"th_cw={r['theta_cw']:.9f} th_ccw={r['theta_ccw']:.9f} gam={r['gam']:.12f} "
              f"nest_ccw={r['nest_ccw']:+.3e} nest_cw={r['nest_cw']:+.3e} resid={r['resid']:+.3e} "
              f"facet_scale={None if r['facet'] is None else round(r['facet'][2],6)} "
              f"|O|={None if r['facet'] is None else round(float(np.linalg.norm(r['facet'][0])),6)}")
    # per-site participation on the circle
    part = {}
    for r in recs:
        for x in r["pair"]:
            part[x] = part.get(x, 0) + 1
    print("boundary owner multiplicities:", dict(sorted(part.items())))
    print("interior sites (Delaunay, not on boundary):", sorted(set(range(len(sites))) - set(part)))
    log.close()
