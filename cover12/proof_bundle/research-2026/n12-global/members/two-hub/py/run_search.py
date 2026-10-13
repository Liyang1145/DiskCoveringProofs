"""run_search.py -- r-sweep of the k=10 family search (diagnostic driver).

For each r: minimise R_cand over the parametrised k=10 family (10 inner-root
rings + 2 non-active hubs), then report
  R_cand  (candidate reading, lower-biased for R)
  R_ref   (independent grid + pattern search reference)
  grid_upper (Lipschitz-valid upper bound for R, from candlib.sandwich)
  n_active (count of boundary-active disks in the found configuration)
and the deficit  R_ref - r  (positive => the found configuration does NOT cover
at radius r; the search found no cover for this r).
Only the sign of the deficit for the *searched* configurations is informative;
neither sign is a proof about the whole family.
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent.parent / "finite-reduction" / "py"))

import k10_feas as K  # noqa: E402

OUT = HERE.parent / "evidence"
OUT.mkdir(parents=True, exist_ok=True)


def run_one(r, restarts, maxfev, seed, tag):
    t0 = time.time()
    (val, p), tmax = K.search(r, restarts, maxfev, seed, verbose=False)
    C = K.make_centers(p, r, tmax)
    rep = K.report(C, r, val)
    row = dict(r=r, tag=tag, restarts=restarts, maxfev=maxfev, seed=seed,
               R_cand=val, R_ref=rep["R_ref"], grid_upper=rep["grid_upper"],
               n_active=rep["n_active"],
               hub_norms=[rep["norms"][10], rep["norms"][11]],
               deficit_Rref=r - rep["R_ref"], deficit_Rcand=r - val,
               t=time.time() - t0)
    print("r=%.9f  R_cand=%.9f  R_ref=%.9f  deficit(R_ref-r)=%+.6f  "
          "n_active=%d  hubs=%.4f,%.4f  %.1fs"
          % (r, val, rep["R_ref"], r - rep["R_ref"], rep["n_active"],
             row["hub_norms"][0], row["hub_norms"][1], row["t"]), flush=True)
    json.dump(dict(row=row, params=p.tolist(), centers=C.tolist(), report=rep),
              open(OUT / ("search_%s.json" % tag), "w"), indent=1)
    return row


def main():
    rs = [float(x) for x in sys.argv[1].split(",")] if len(sys.argv) > 1 else [K.U]
    restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    maxfev = int(sys.argv[3]) if len(sys.argv) > 3 else 5000
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 4242
    tag0 = sys.argv[5] if len(sys.argv) > 5 else "sweep"
    rows = []
    for i, r in enumerate(rs):
        for rep in range(2):
            rows.append(run_one(r, restarts, maxfev, seed + 1000 * rep + i,
                                "%s_r%.9f_%d" % (tag0, r, rep)))
    json.dump(rows, open(OUT / ("%s_summary.json" % tag0), "w"), indent=1)


if __name__ == "__main__":
    main()
