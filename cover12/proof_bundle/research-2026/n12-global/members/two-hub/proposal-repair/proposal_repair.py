"""proposal_repair.py -- bounded (10 min) proposal-quality experiment for Lead.

Task: from the latest full-domain snapshot (read once, READ-ONLY), take a pending
ancestor box near the stuck region (s,x,y) ~ (0.172, 0.04, 0.02) with
maxwidth ~ 0.01, and test whether DENSER LP proposals (nr=48, np_=360, order
4/6) let the exact integer atomic kernel certify that whole box, where the
default proposal (order=4, nr=24, np_=120) fails.

Outputs (all inside members/two-hub/proposal-repair/): exact H, weights, status.
No writes anywhere else. Numeric max is never a certificate: only the atomic
kernel's 'certified' status counts here.
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction as F
from pathlib import Path

LEAD = Path("research-2026/n12-global/lead").resolve()
HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "proposal-repair"
OUT.mkdir(parents=True, exist_ok=True)
sys.path.insert(0, str(LEAD))
sys.path.insert(0, str(HERE.parent / "py"))

SNAP = Path("research-2026/n12-global/evidence/hubline-domain.json").resolve()
TARGET = (0.172, 0.04, 0.02)


def decode(B):
    return tuple(tuple(F(v) for v in r) for r in B)


def main():
    import hubline_capacity as H          # noqa: E402
    import hubline_atoms_fast as AF       # noqa: E402

    snap = json.loads(SNAP.read_text())
    pend = [decode(b) for b in snap.get("pending", [])]
    print("snapshot status=%s  pending=%d  counts=%s"
          % (snap.get("status"), len(pend), snap.get("counts")), flush=True)

    def ctr(B):
        return [float((lo + hi) / 2) for lo, hi in B]

    def maxw(B):
        return float(max(hi - lo for lo, hi in B))

    # candidate: pending box closest to TARGET with maxwidth near 0.01,
    # preferring the largest width <= 0.02 (an "ancestor" of the stuck leaves)
    near = sorted(pend, key=lambda B: sum((a - b) ** 2 for a, b in zip(ctr(B), TARGET)))
    cand = None
    for B in near[:4000]:
        w = maxw(B)
        if 0.008 <= w <= 0.02:
            cand = B
            break
    if cand is None:
        cand = near[0]
    B = cand
    print("chosen pending box H = %s   centre=%s  maxwidth=%.6f"
          % ([[str(v) for v in r] for r in B], ctr(B), maxw(B)), flush=True)

    mid = ctr(B)
    mid[0] = min(mid[0], float(H.K.Uq) - 1e-15)
    results = []

    def trial(tag, order, nr, np_, N=2048, budget=150000):
        t0 = time.time()
        try:
            p = H.propose(mid[0], mid[1], mid[2], order=order, nr=nr, np_=np_)
        except Exception as exc:                     # noqa: BLE001
            row = dict(tag=tag, order=order, nr=nr, np=np_, error=str(exc))
            results.append(row)
            print("  %-22s EXC %s" % (tag, exc), flush=True)
            return row
        row = dict(tag=tag, order=order, nr=nr, np=np_, numeric_max=p["numeric_max"],
                   weights=p["weights"], seconds_proposal=time.time() - t0)
        try:
            C = AF.FastAtoms(B, p["weights"], N)
            res = C.certify(budget=budget)
        except Exception as exc:                     # noqa: BLE001
            row["cert_error"] = str(exc)
            results.append(row)
            print("  %-22s numeric=%.5f  certify EXC %s"
                  % (tag, p["numeric_max"], exc), flush=True)
            return row
        row.update(cert=res, seconds=time.time() - t0, N=N,
                   H=[[str(v) for v in r] for r in B])
        results.append(row)
        print("  %-22s numeric=%.5f -> %s  (%.0fs)"
              % (tag, p["numeric_max"], res.get("status"), time.time() - t0),
              flush=True)
        return row

    t_start = time.time()
    # default proposal (the run's current choice)
    trial("default o4 24x120", 4, 24, 120)
    # denser proposals, bounded to <=6 trials
    for (order, nr, np_) in [(4, 48, 360), (6, 48, 360), (4, 96, 720),
                             (6, 96, 720), (4, 48, 1440)]:
        if time.time() - t_start > 540:
            print("time cap reached, stopping trials", flush=True)
            break
        trial("dense o%d %dx%d" % (order, nr, np_), order, nr, np_)

    out = dict(target=list(TARGET), chosen_H=[[str(v) for v in r] for r in B],
               centre=mid, maxwidth=maxw(B), snapshot_counts=snap.get("counts"),
               snapshot_status=snap.get("status"), trials=results,
               seconds_total=time.time() - t_start)
    (OUT / "proposal_repair_result.json").write_text(json.dumps(out, indent=1))
    print("saved %s" % (OUT / "proposal_repair_result.json"), flush=True)


if __name__ == "__main__":
    main()
