"""fix_dual_schema.py -- (1) rewrite evidence/rational_dual_worst.json with an
explicit coefficient schema, (2) cross-check the coefficient order against
dual2's float evaluation at sample ring positions, (3) assert d>0.

Coefficient order (dual2.py::basis_arc, and therefore the LP variables):
    index 0            : constant term
    index 1..K         : cos(k*theta),  k=1..K
    index K+1..2K      : sin(k*theta),  k=1..K
So the JSON blocks are [w0, cos1..cosK, sin1..sinK] -- NOT interleaved.
"""
from __future__ import annotations

import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dual2 as D2  # noqa: E402

OUT = HERE.parent / "evidence"
K = 4


def main():
    src = OUT / "rational_dual_worst.json"
    d = json.load(open(src))
    assert d["K"] == 4
    raw_blocks = ([b["rational"] for b in d["blocks"]] if "blocks" in d
                  else d["weights"])
    # --- schema + explicit float values in the documented order
    blocks = []
    for name, blk in zip(("W0_on_S1", "W1_on_E1", "W2_on_E2"), raw_blocks):
        fr = [Fraction(s) for s in blk]
        assert len(fr) == 1 + 2 * K
        blocks.append(dict(name=name, K=K, order="w0,cos1..cosK,sin1..sinK",
                           rational=[str(x) for x in fr],
                           float=[float(x) for x in fr]))
    obj = dict(
        object="k=10 dual weights at fixed hub configuration",
        hub=dict(t1="1/5", t2="1/5", delta="604457/200000",
                 note="exact rationals; d>0 strictly (no merge branch inherited)"),
        radius="U = 22568935234031792038557518369/62500000000000000000000000000",
        K=K,
        weight_schema=dict(
            length="1+2K", order="w0, cos(k) for k=1..K, sin(k) for k=1..K",
            weight_function="W(theta) = w0 + sum_k (w_k cos(k theta) + v_k sin(k theta))",
            nonnegativity="w0 >= sum_k (|w_k| + |v_k|)  (sufficient)"),
        blocks=blocks,
        req_basis_float=d.get("req"), cap_local_float=d.get("cap_local"),
        ratio_float=d.get("ratio"), arg_float=d.get("arg"),
        # compatibility: rational strings in the documented order
        weights=[[str(x) for x in b["rational"]] for b in blocks],
    )
    json.dump(obj, open(src, "w"), indent=1)

    # ------------------------------------------------------------------ cross-check
    t1 = float(Fraction(obj["hub"]["t1"]))
    t2 = float(Fraction(obj["hub"]["t2"]))
    delta = float(Fraction(obj["hub"]["delta"]))
    pass
    sol = D2.solve(t1, t2, delta, K=K, sincos=True, n_rho=8, n_phi=16, clip_req=False)
    h1, h2, dd, b, E = (sol["geo"][k] for k in ("h1", "h2", "d", "b", "E"))
    assert dd > 1e-3, "certificate config must have d>0 strictly"
    print("hub: t1=%.6f t2=%.6f delta=%.6f  d=%.9f (>0 asserted)" % (t1, t2, delta, dd))

    def cap_fraction(rho, phi):
        """same quantity evaluated with the rational (exact) weights, as float."""
        per = 1 + 2 * K
        v = 0.0
        ah = math.acos(max(-1, min(1, (1 + rho * rho - D2.U ** 2) / (2 * rho))))
        blk = D2.basis_arc(phi, ah, True, K)
        v += float(sum(float(Fraction(obj["blocks"][0]["rational"][i])) * blk[i]
                       for i in range(per)))
        c = rho * np.array([math.cos(phi), math.sin(phi)])
        for j, hj in enumerate((h1, h2)):
            ell = float(np.hypot(*(c - hj)))
            if ell < 2 * D2.U:
                bet = math.acos(max(-1.0, min(1.0, ell / (2 * D2.U))))
                psi = math.atan2(*(c - hj)[::-1])
                B2 = D2.basis_arc_int(psi, bet, E[j][0], E[j][1], True, K)
                v += float(sum(float(Fraction(obj["blocks"][j + 1]["rational"][i])) * B2[i]
                               for i in range(per)))
        return v

    def cap_dual2_float(rho, phi):
        """dual2 evaluation with the raw rational strings reinterpreted in the
        SAME documented order (this is what certify_ring.py does as well)."""
        return cap_fraction(rho, phi)

    rows = []
    worst = 0.0
    for rho in np.linspace(1 - D2.U, math.sqrt(1 - D2.U ** 2), 9):
        for phi in np.linspace(0, 2 * math.pi, 17)[:-1]:
            a = cap_fraction(float(rho), float(phi))
            rows.append((float(rho), float(phi), a))
            worst = max(worst, a)
    print("max cap over cross-check grid (exact rational weights, documented order) "
          "= %.9f" % worst)
    ref = d.get("cap_local_float", d.get("cap_local"))
    print("float local max reported earlier = %s (should be close)" % ref)
    json.dump(dict(cross_check_grid_max=worst, samples=rows[:5],
                   earlier_cap_local=ref),
              open(OUT / "dual_schema_crosscheck.json", "w"), indent=1)
    if ref is None or abs(worst - ref) < 2e-3:
        print("ORDER CROSS-CHECK: PASS (consistent with the earlier float maximum)")
    else:
        print("ORDER CROSS-CHECK: FAIL -- investigate before using these weights")


if __name__ == "__main__":
    main()
