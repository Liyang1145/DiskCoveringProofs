"""Final numbers: chord-inner slack (cos(theta/2) - c.n) >= 0 (= the chain's conclusion),
cap violation, and the exact residual/nest relation per anchor."""
import json, math, sys
from pathlib import Path
import numpy as np
from fractions import Fraction

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom_exact import anchor_records
from cover_radius_exact import cover_radius_exact

U = 0.33173203427623414

def rows_of(S):
    recs, anch = anchor_records(S)
    out = []
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
            out.append(dict(k=k, side=side, owner=int(arcs[0]),
                            slack=math.cos(th / 2) - float(c @ n),
                            nest=rec["nest_cw"] if side == "cw" else rec["nest_ccw"],
                            resid=rec["resid"]))
    return out, recs

def show(S, name):
    r = cover_radius_exact(S)[0]
    s = math.sqrt(1 - r * r)
    rows, recs = rows_of(S)
    norms = np.linalg.norm(S, axis=1)
    i = int(np.argmax(norms))
    mn = min(rows, key=lambda x: x["slack"])
    print(f"{name}: r={r:.12f} (r-U={r-U:+.2e})  s={s:.12f}  max|c|={norms[i]:.12f} (site {i})"
          f"  cap-violation={norms[i]-s:+.3e}")
    print(f"   min chord-inner slack = {mn['slack']:+.6e} at (k={mn['k']},{mn['side']},owner {mn['owner']})"
          f";  #rows with slack==0: {sum(1 for x in rows if abs(x['slack'])<1e-12)}"
          f";  #rows with slack<0: {sum(1 for x in rows if x['slack']<-1e-12)}")
    for rec in recs:
        kk = rec["k"]
        rr = [x for x in rows if x["k"] == kk]
        ne = min(x["nest"] for x in rr)
        pred = 0.0 if ne >= 0 else -2 * ne
        print(f"     k={kk:2d} nest_cw={rec['nest_cw']:+.3e} nest_ccw={rec['nest_ccw']:+.3e} "
              f"resid={rec['resid']:+.6e}  2*max(0,-min nest)={pred:+.6e}  "
              f"match={abs(pred-rec['resid'])<1e-12}")

if __name__ == "__main__":
    cand = np.array([[float(Fraction(x)) for x in p]
                     for p in json.loads((HERE.parent.parent / "lead" / "improved-upper-test.json")
                                         .read_text())["centers"]])
    cfgs = json.loads((HERE / "violating-configs.json").read_text())
    show(cand, "candidate")
    print()
    show(np.array(cfgs[0]["sites"]), "counterexample(1e-6,rep0)")
