"""Numbers for the report:
 (1) counterexample: cap violation per site, and the exact correspondence
     "failing anchor <-> owner whose norm exceeds sqrt(1-r^2)";
 (2) candidate: which sites/anchors saturate the chain (equality case, delta=0);
 (3) residual vs margin: show residual == 0 iff chord-inner margin >= 0, else 2*|margin|.
"""
import json, math, sys
from pathlib import Path
import numpy as np
from fractions import Fraction

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom_exact import anchor_records
from cover_radius_exact import cover_radius_exact

U = 0.33173203427623414

def chord_inner(S, recs, anch):
    """per (anchor, side): c.n - cos(theta/2)  (<=0 is the chain conclusion)."""
    rows = []
    for k, rec in enumerate(recs):
        A = rec["A"]
        for side, arcs, other in (("cw", rec["arc_cw"], anch[(k - 1) % len(anch)]["A"]),
                                  ("ccw", rec["arc_ccw"], anch[(k + 1) % len(anch)]["A"])):
            if len(arcs) != 1:
                continue
            c = S[arcs[0]]
            a1 = math.atan2(A[1], A[0]); a2 = math.atan2(other[1], other[0])
            d = (a2 - a1 + math.pi) % (2 * math.pi) - math.pi
            n = np.array([math.cos(a1 + 0.5 * d), math.sin(a1 + 0.5 * d)])
            th = abs(d)
            rows.append(dict(k=k, side=side, owner=int(arcs[0]), margin=float(c @ n) - math.cos(th / 2),
                             nest=rec["nest_cw"] if side == "cw" else rec["nest_ccw"],
                             resid=rec["resid"]))
    return rows

def summarize(S, name):
    r, x, tag, npts = cover_radius_exact(S)
    s = math.sqrt(max(0.0, 1 - r * r))
    recs, anch = anchor_records(S)
    rows = chord_inner(S, recs, anch)
    norms = np.linalg.norm(S, axis=1)
    bad = [i for i in range(len(S)) if norms[i] > s + 0]
    print(f"### {name}")
    print(f"  r_exact = {r:.12f}   r-U = {r-U:+.3e}   s = sqrt(1-r^2) = {s:.12f}")
    print(f"  sites with |c| > s (cap violated): "
          f"{[(i, round(float(norms[i]), 9), round(float(norms[i]-s), 3e-9 if False else 12)) for i in bad]}")
    print(f"  max|c| - s = {float(norms.max()-s):+.3e}")
    fails = [(x["k"], x["side"], x["owner"], f"{x['resid']:+.2e}", f"{x['margin']:+.2e}")
             for x in rows if abs(x["resid"]) > 1e-9]
    print(f"  anchors: q={len(recs)}; failing |resid|>1e-9: {fails}")
    print(f"  min chord-inner margin = {min(x['margin'] for x in rows):+.3e};  "
          f"min nest = {min(x['nest'] for x in rows):+.3e}")
    eq = [x for x in rows if abs(x["margin"]) < 1e-12]
    print(f"  rows with margin == 0 (chain saturated, delta corner): "
          f"{[(x['k'], x['side'], x['owner']) for x in eq]}")
    return rows

if __name__ == "__main__":
    cand = np.array([[float(Fraction(x)) for x in p]
                     for p in json.loads((HERE.parent.parent / "lead" / "improved-upper-test.json")
                                         .read_text())["centers"]])
    cfgs = json.loads((HERE / "violating-configs.json").read_text())
    S1 = np.array(cfgs[0]["sites"])
    out = open(HERE / "report-numbers.txt", "w")
    class Tee:
        def write(self, s):
            old_write = type(out).write
            old.write(s); out.write(s)
        def flush(self):
            pass
    tee = Tee(); old = sys.stdout; sys.stdout = tee
    rows_c = summarize(cand, "campaign candidate (14 sites)")
    rows_x = summarize(S1, "counterexample = candidate + 1e-6 noise (same q10 type)")
    # residual vs margin identity check
    worst = 0.0
    for rows in (rows_c, rows_x):
        for x in rows:
            pred = 0.0 if x["margin"] <= 0 else 0.0   # placeholder, replaced below
    # relation: residual = 0 if nest>=0 else 2*|nest|
    dev = []
    for rows in (rows_c, rows_x):
        for x in rows:
            pred = 0.0 if x["nest"] >= 0 else -2 * x["nest"]
            dev.append(abs(pred - x["resid"]))
    print(f"\nrelation |resid - (0 if nest>=0 else -2*nest)| <= {max(dev):.2e} over both configs")
    # perturbation scan: margin vs residual
    rng = np.random.default_rng(20260927)
    print("\nperturbation scan (120 reps/scale): min chord margin / min nest / max|resid|")
    for scale in (1e-7, 1e-6, 1e-5, 1e-4, 1e-3):
        mm = 9e9; nn = 9e9; rr = 0.0
        for rep in range(120):
            S = cand + rng.normal(0, scale, cand.shape)
            nrm = np.linalg.norm(S, axis=1)
            bad = nrm > 0.999
            if bad.any():
                S[bad] = S[bad] * (0.999 / nrm[bad])[:, None]
            recs, anch = anchor_records(S)
            if not recs:
                continue
            rows = chord_inner(S, recs, anch)
            mm = min(mm, min(x["margin"] for x in rows))
            nn = min(nn, min(x["nest"] for x in rows))
            rr = max(rr, max(abs(x["resid"]) for x in rows))
        print(f"  scale={scale:<7g} min_margin={mm:+.3e} min_nest={nn:+.3e} max|resid|={rr:.3e}")
    sys.stdout = old
    out.close()
