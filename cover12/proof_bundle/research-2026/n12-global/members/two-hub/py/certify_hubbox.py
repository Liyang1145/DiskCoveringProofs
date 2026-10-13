"""certify_hubbox.py -- interface test: one HUB BOX of positive width.

Same statement as certify_ring2.py but with the hub parameters themselves taken
as intervals:
    t1 in [0.2-dt, 0.2+dt], t2 in [0.2-dt, 0.2+dt], delta in [delta0-dd, delta0+dd]
and the ring domain continuous.  We require
    10 * sup_{(param, ring), cap} < req_lo/10 ,
where req_lo is the *lower* end of the interval enclosure of req over the hub box
(so it bounds min_over_box req) and the cap bound encloses all values over
(param, ring).  Weights are the single rational dual fixed at the box centre
(0.2, 0.2, 604457/200000); no per-box re-optimisation.  Purpose: measure how the
margin degrades with the hub-box width, i.e. test the certification interface.
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction
from pathlib import Path

from mpmath import iv, mp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import certify_ring2 as C2  # noqa: E402

OUT = HERE.parent / "evidence"
DELTA0 = Fraction(604457, 200000)


class CertBox(C2.Cert):
    def __init__(self, W, t1_iv, t2_iv, del_iv, dps=25):
        iv.dps = dps
        mp.dps = dps + 15
        self.check_extraction()
        self.W = [[C2.ivf(c) for c in blk] for blk in W]
        self.U = C2.ivf(C2.U_FR)
        self.h1 = [t1_iv, iv.mpf(0)]
        self.h2 = [t2_iv * iv.cos(del_iv), t2_iv * iv.sin(del_iv)]
        dx = self.h1[0] - self.h2[0]
        dy = self.h1[1] - self.h2[1]
        self.d = iv.sqrt(dx * dx + dy * dy)
        assert (self.d > 1e-6) is True, "merge branch not implemented: need d>0"
        # hub disks must lie in int D for the exposed-boundary lemma
        for h in (self.h1, self.h2):
            nrm = iv.sqrt(h[0] * h[0] + h[1] * h[1])
            assert (nrm + self.U < 1) is True, "hub not strictly inactive"
        q = C2.clip_unit(self.d / (2 * self.U))
        self.b = iv.atan2(iv.sqrt(1 - q ** 2), q)
        self.away = [iv.atan2(dy, dx), iv.atan2(-dy, -dx)]
        self.E = [(self.away[0], iv.pi - self.b), (self.away[1], iv.pi - self.b)]
        self.req = self._req()
        self.rho_lo = iv.mpf(1) - self.U
        self.rho_hi = iv.sqrt(1 - self.U * self.U)
        self.two_pi = 2 * iv.pi


def main():
    W, meta = C2.load_weights()
    cases = [(0.0, 0.0), (0.005, 0.02), (0.01, 0.04), (0.02, 0.08), (0.04, 0.16)]
    rows = []
    for (dt, dd) in cases:
        t1i = iv.mpf([mp.mpf(str(0.2 - dt)), mp.mpf(str(0.2 + dt))])
        t2i = iv.mpf([mp.mpf(str(0.2 - dt)), mp.mpf(str(0.2 + dt))])
        d0 = float(DELTA0)
        di = iv.mpf([mp.mpf(str(d0 - dd)), mp.mpf(str(d0 + dd))])
        c = CertBox(W, t1i, t2i, di)
        t0 = time.time()
        res = c.run(max_boxes=400000, max_depth=16, verbose=False)
        row = dict(dt=dt, dd=dd, req_lo=res["req_lo"], threshold=res["threshold"],
                   nbox=res["nbox"], leaves=res["leaves"], unsolved=res["unsolved"],
                   worst_leaf_ub=res["worst_leaf_ub"],
                   margin_ratio=res["margin_ratio"], secs=res["secs"])
        rows.append(row)
        print("dt=%.3f dd=%.3f  unsolved=%-6d leaves=%-6d worst_leaf=%.9f  ratio=%s  (%.0fs)"
              % (dt, dd, row["unsolved"], row["leaves"],
                 float(mp.mpf(row["worst_leaf_ub"])), row["margin_ratio"][:10],
                 time.time() - t0), flush=True)
    json.dump(rows, open(OUT / "certify_hubbox.json", "w"), indent=1)


if __name__ == "__main__":
    main()
