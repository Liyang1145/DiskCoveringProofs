"""Candidate + randomization control for the boundary-anchor audit (cc2).

Part 1: the actual 14-site candidate of the campaign (improved-upper-test.json centres).
        - independent Voronoi ownership recomputation from the 14 coordinates alone
        - h_A<0 (gam<pi/2) and cyclicity residual at every anchor
        - relaxation form  y_e > x_f cos(beta_e)  on every boundary edge
Part 2: random interior site sets -- hunt for nesting violation (resid != 0).
"""
import json, math, sys
from pathlib import Path
import numpy as np
from fractions import Fraction

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom import anchors_of, analyse, circumcenter, facet_end, covering_radius, angle_between

LEAD = HERE.parent.parent / "lead"
CAND = LEAD / "improved-upper-test.json"
U = 0.33173203427623414

def load_candidate():
    D = json.loads(CAND.read_text())
    return np.array([[float(Fraction(x)) for x in p] for p in D["centers"]]), D

def report(title, d, fh=None):
    line = (f"{title} q={len(d)}  max|resid|={max(abs(r['resid']) for r in d):.3e}"
            f"  max gam={max(r['gam'] for r in d):.9f} (pi/2={math.pi/2:.9f})"
            f"  min nest_ccw={min(r['nest_ccw'] for r in d):+.3e}"
            f"  min nest_cw={min(r['nest_cw'] for r in d):+.3e}"
            f"  min arc={min(min(r['theta_ccw'], r['theta_cw']) for r in d):.6f}"
            f"  max arc={max(max(r['theta_ccw'], r['theta_cw']) for r in d):.6f}")
    print(line)
    if fh: fh.write(line + "\n")

def relax_check(sites, d, fh=None):
    """y_e > x_f cos beta_e  for every boundary edge, using true geometry.
    x_f = |circumcentre - site| (face circumradius), y_e = |anchor - site|,
    beta_e = angle at the site between (site->circumcentre) and (site->anchor)."""
    out = []
    for r in d:
        A = None
        # rebuild A
        A = np.array([math.cos(r["t"]), math.sin(r["t"])])
        u, v = r["pair"]
        fe = facet_end(sites, u, v, A)
        if fe is None:
            out.append((r["k"], None)); continue
        O, w, s = fe
        xf = float(np.linalg.norm(O - sites[u]))
        ye = float(np.linalg.norm(A - sites[u]))
        beta = angle_between(O - sites[u], A - sites[u])
        out.append((r["k"], ye - xf * math.cos(beta), gamma_tri(xf, ye, beta), r["gam"], O))
    bad = [o for o in out if o[1] is None]
    if bad:
        print("  boundary edges with no interior facet vertex:", bad)
    else:
        lo = min(o[1] for o in out)
        mx = max(abs(o[2] - o[3]) for o in out)
        mxO = max(np.linalg.norm(o[4]) for o in out)
        line = (f"  relaxation form y_e - x_f cos beta_e: min={lo:.6e}  "
                f"max|gamma_tri - gam|={mx:.3e}  max|O|={mxO:.6f}")
        print(line)
        if fh: fh.write(line + "\n")
    return out

def gamma_tri(x, y, beta):
    return math.atan2(x * math.sin(beta), y - x * math.cos(beta))

if __name__ == "__main__":
    sites, D = load_candidate()
    log = open(HERE / "control-log.txt", "w")
    r = covering_radius(sites, 500)
    print(f"candidate: n={len(sites)} grid covering radius r={r:.6f} (U={U:.6f})")
    log.write(f"candidate covering radius (grid 500) = {r!r}\n")
    d = analyse(sites, M=1200000, tag="candidate")
    report("candidate", d, log)
    for rec in d:
        print(f"  k={rec['k']:2d} pair={rec['pair']} owners_order={rec['owners_order']} "
              f"nmargin={rec['nmargin']:.3e} arc_cw={rec['arc_cw']} arc_ccw={rec['arc_ccw']} "
              f"th_cw={rec['theta_cw']:.9f} th_ccw={rec['theta_ccw']:.9f} "
              f"gam={rec['gam']:.12f} ang_m={rec['ang_m']:.9f} "
              f"nest_ccw={rec['nest_ccw']:+.3e} nest_cw={rec['nest_cw']:+.3e} resid={rec['resid']:+.3e}")
    relax_check(sites, d, log)
    log.close()
