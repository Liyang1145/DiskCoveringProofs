#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""test_atomn_dispatch.py -- independent controls for the atom-count dispatch.

A. Vector sources: independently REGENERATE the stereographic rational unit sets from
   scratch (my own code, exact c^2+s^2==1 verified) and compare elementwise with
     * evidence/atomic-unit-vectors-2048.json   (frozen evidence file, cache-critical)
     * members/.../canonical-unit-vectors-8192.json
   Also report the rounding-robustness of every t (distance of tan(pi j/N)*1e8 from the
   .5 boundary) so a different float tan could not silently pick another parameter.
B. N=2048 dispatch consistency: IntAtomsN(N=2048) must reproduce the frozen kernel's
   positive-box reading exactly (certified / 11875 / max 32575800681 / gap 1271822).
C. N=8192 two-hub saved instance (members/two-hub/proposal-repair/N_scan.json): the pure
   integer kernel must reproduce certified with the saved FastAtoms numbers
   (boxes 16911, leaves 8334, outside 122, max 130169221852, total 1301696319067,
   gap 4100547, atoms 18886).
D. Independent re-derivation of the N=2048 positive-box atoms: recompute the atom
   rectangles myself in exact Fractions and check the integer floor/ceil endpoints match
   the kernel's arrays, plus the total weight.
"""
import hashlib
import json
import math
import os
import sys
from fractions import Fraction as F

import mpmath as mp
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
MEM = os.path.abspath(os.path.join(HERE, ".."))
N12 = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
EV = os.path.join(N12, "evidence")
UPPER = os.path.join(N12, "members", "upper-audit", "integer-atomic", "py")
VECDIR = os.path.join(N12, "members", "upper-audit", "integer-atomic", "evidence")
sys.path.insert(0, UPPER)

U = F('0.361102963744508672616920293904')
mp.mp.dps = 60


def my_stereo_units(N, decimals=8):
    """regenerate independently (own code); each point verified exactly on S^1.

    Also returns, per index, the deviation |tan(pi j/N)*10^dec - t_file| of the file's
    integer parameter from the true scaled tangent.  The meaningful robustness statement
    is that this deviation stays below 0.5 (the file rounds to the true integer), and we
    report the tightest margin 0.5 - max|deviation|.
    """
    scale = 10 ** decimals
    pts = []
    for j in range(N):
        if 2 * j == N:
            pts.append((F(-1), F(0)))
            continue
        scaled = mp.tan(mp.pi * j / N) * mp.mpf(10) ** decimals
        t = F(round(float(scaled)), scale)
        pts.append(((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t)))
    assert all(c * c + s * s == 1 for c, s in pts)
    return pts


def rounding_margins(N, their, decimals=8):
    """Two well-posed quantities per index j (no ill-conditioned recovery of t):

      dev_j    = |scaled_exact - round(scaled_exact)|      (distance to nearest integer)
      margin_j = 0.5 - dev_j                               (distance to the flip boundary)
      budget_j = |scaled_exact| * 1e-15                    (float tan error budget)

    The file reproduces the exact rounding iff margin_j > budget_j for every j; we report
    the tightest margin and the largest budget, plus the count of j with margin < 10*budget.
    """
    worst_margin, worst_id = None, None
    worst_budget = mp.mpf(0)
    worst_ratio, worst_ratio_id = None, None
    violations = 0
    for j in range(N):
        if 2 * j == N:
            continue
        scaled = mp.tan(mp.pi * j / N) * mp.mpf(10) ** decimals
        nearest = mp.nint(scaled)
        margin = mp.mpf('0.5') - abs(scaled - nearest)
        budget = abs(scaled) * mp.mpf('1e-15')      # generous float-tan error bound
        worst_budget = max(worst_budget, budget)
        if worst_margin is None or margin < worst_margin:
            worst_margin, worst_id = margin, j
        if budget > 0:
            ratio = margin / budget
            if worst_ratio is None or ratio < worst_ratio:
                worst_ratio, worst_ratio_id = ratio, j
        if margin <= budget:                        # the same j could flip
            violations += 1
    return dict(min_rounding_margin=worst_margin, min_margin_index=worst_id,
                max_float_error_budget=worst_budget,
                min_margin_over_budget=worst_ratio,
                min_ratio_index=worst_ratio_id,
                n_per_index_violations=violations,
                unambiguous=bool(violations == 0))


def load_vecs(path):
    d = json.loads(open(path, encoding="utf-8").read())
    raw = d["vectors"] if isinstance(d, dict) and "vectors" in d else d
    return [(F(a), F(b)) for a, b in raw]


def main():
    rep, checks = {}, {}

    # ---- A. vector sets ----
    for N, path in ((2048, os.path.join(EV, "atomic-unit-vectors-2048.json")),
                    (8192, os.path.join(VECDIR, "canonical-unit-vectors-8192.json"))):
        mine = my_stereo_units(N)
        their = load_vecs(path)
        same = (len(mine) == len(their) == N and
                all(a == b for a, b in zip(mine, their)))
        margin = rounding_margins(N, their)
        rep["vec_N%d" % N] = dict(path_sha256=hashlib.sha256(open(path, "rb").read()).hexdigest(),
                                  n=N, elementwise_identical=bool(same),
                                  min_rounding_margin=mp.nstr(margin["min_rounding_margin"], 6),
                                  min_margin_index=margin["min_margin_index"],
                                  max_float_error_budget=mp.nstr(margin["max_float_error_budget"], 6),
                                  min_margin_over_budget=mp.nstr(margin["min_margin_over_budget"], 6),
                                  n_per_index_violations=margin["n_per_index_violations"],
                                  all_on_S1=all(c * c + s * s == 1 for c, s in their),
                                  exact_on_S1_is_the_proof_relevant_fact=True)
        # the stored set reproduces the exact rounding iff my regenerated set is identical
        # (it is, elementwise) AND no j sits within its float error budget of the boundary
        checks["A_N%d_vectors_reproduced" % N] = bool(same and margin["unambiguous"])

    # ---- D. independent atom re-derivation for the positive box (N=2048) ----
    import integer_kernel as IK
    pos = json.loads(open(os.path.join(EV, "hubline-atoms-1-1000-2048.json"),
                          encoding="utf-8").read())
    H_raw, W_raw = pos["H"], pos["weights"]
    A = IK.IntAtoms([(F(a), F(b)) for a, b in H_raw], W_raw, 26)
    V = load_vecs(os.path.join(EV, "atomic-unit-vectors-2048.json"))
    (sl, sh), (xl, xh), (yl, yh) = [(F(a), F(b)) for a, b in H_raw]
    Wflat = [[F(x) for x in row] for row in W_raw]
    n = (len(Wflat[0]) - 1) // 2
    S = A.S
    ax0, ax1, ay0, ay1, wts = [], [], [], [], []
    for j, w in enumerate(Wflat):
        for (c, s) in V:
            if j == 1 and U * c > sl:
                continue
            if j == 2 and U * c < -sl:
                continue
            v = F(w[0]); co, si = F(1), F(0)
            for k in range(1, n + 1):
                co, si = co * c - si * s, si * c + co * s
                v += F(w[k]) * co + F(w[n + k]) * si
            wt = round(v * 10 ** 9)
            if not wt:
                continue
            if j == 0:
                rx, ry = (c, c), (s, s)
            elif j == 1:
                rx = (xl - sh + U * c, xh - sl + U * c); ry = (yl + U * s, yh + U * s)
            else:
                rx = (xl + sl + U * c, xh + sh + U * c); ry = (yl + U * s, yh + U * s)
            ax0.append(math.floor(rx[0] * S)); ax1.append(math.ceil(rx[1] * S))
            ay0.append(math.floor(ry[0] * S)); ay1.append(math.ceil(ry[1] * S))
            wts.append(wt)
    checks["D_atom_arrays_identical"] = bool(
        wts == list(A.W) and ax0 == list(A.Ax0) and ax1 == list(A.Ax1) and
        ay0 == list(A.Ay0) and ay1 == list(A.Ay1))
    checks["D_total_identical"] = (sum(wts) == A.total)
    rep["D"] = dict(n_atoms=len(wts), kernel_n_atoms=len(A.W), total=sum(wts),
                    kernel_total=A.total, maxend=max(max(map(abs, ax0)), max(map(abs, ax1)),
                                                     max(map(abs, ay0)), max(map(abs, ay1))))

    # ---- B. N=2048 dispatch consistency ----
    import integer_kernel_n as IKN
    B = IKN.IntAtomsN(H_raw, W_raw, 2048, Sexpt=26)
    rb = B.certify()
    checks["B_dispatch_2048_matches_frozen"] = bool(
        rb["status"] == "certified" and rb["boxes"] == 11875 and
        rb["max_integer_capture"] == 32575800681 and rb["gap_integer"] == 1271822)
    rep["B"] = dict(status=rb["status"], boxes=rb["boxes"],
                    max=rb["max_integer_capture"], gap=rb["gap_integer"],
                    expected=dict(boxes=11875, max=32575800681, gap=1271822))

    # ---- C. N=8192 two-hub saved instance ----
    src = os.path.join(N12, "members", "two-hub", "proposal-repair", "N_scan.json")
    d = json.loads(open(src, encoding="utf-8").read())
    C = IKN.IntAtomsN(d["H"], d["weights_o6"], 8192, Sexpt=26)
    rc = C.certify()
    exp = dict(certified=True, boxes=16911, leaves=8334, outside=122,
               max=130169221852, total=1301696319067, gap=4100547, atoms=18886)
    checks["C_n8192_matches_saved"] = bool(
        rc["status"] == "certified" and rc["boxes"] == exp["boxes"] and
        rc["leaves"] == exp["leaves"] and rc["outside"] == exp["outside"] and
        rc["max_integer_capture"] == exp["max"] and
        rc["total_integer_demand"] == exp["total"] and rc["gap_integer"] == exp["gap"] and
        len(C.W) == exp["atoms"])
    rep["C"] = dict(source_sha256=hashlib.sha256(open(src, "rb").read()).hexdigest(),
                    got=dict(status=rc["status"], boxes=rc["boxes"], leaves=rc["leaves"],
                             outside=rc["outside"], max=rc["max_integer_capture"],
                             total=rc["total_integer_demand"], gap=rc["gap_integer"],
                             atoms=len(C.W)),
                    expected=exp)
    # saved float row cross-check (diagnostic)
    row = [r for r in d["N_scan"] if r["N"] == 8192]
    rep["C"]["saved_float_row"] = row[0] if row else None

    rep["checks"] = checks
    rep["all_pass"] = all(checks.values())
    with open(os.path.join(MEM, "out", "atomn-dispatch-controls.json"), "w",
              encoding="utf-8") as f:
        json.dump(rep, f, indent=1)
    print(json.dumps(rep, indent=1)[:2600])
    if not rep["all_pass"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()