"""qe_interface_check.py -- calibration of the denominator-free interface against the
geometric candidate predicate (two representations of the same condition).

Representation 1 (geometric, py/candlib.py):  R_cand(C) <= r, where R_cand is the max
    of f_C over the candidate *points* (K_d filtered by |x|<=1).
Representation 2 (polynomial interface, QE-interface.md §1):  A ^ B ^ C ^ D, built from
    the polynomial conditions with auxiliary variables t_i, nu, w and NO domain-wide
    quantifier.

Both are supposed to express "D is covered by the disks B(c_i,r)".  A mismatch on any
(C, r) is a bug in the interface or in the candidate evaluation.

Usage: py -3 -B qe_interface_check.py [outfile]
"""
from __future__ import annotations

import itertools
import json
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from candlib import R_cand, distinct_positions                    # noqa: E402
from run_battery import battery                                   # noqa: E402


# ----------------------------------------------------- polynomial interface
def iface(C, r, verbose=False):
    """A ^ B ^ C ^ D of QE-interface.md §1. Returns (ok, parts)."""
    C = np.asarray(C, float)
    n = len(C)
    rho = float(r) ** 2
    parts = {}

    # A: fixed point (1,0)
    parts["A"] = any(float(c @ c) - 2.0 * float(c[0]) + 1.0 <= rho for c in C)

    # B: antipodes (auxiliary t_i = |c_i|, linear in t_i)
    B_ok = True
    for i in range(n):
        s = float(C[i] @ C[i])
        if s <= 0.0:
            continue                      # guard t_i>0 unsatisfiable: conjunct vacuous
        t = math.sqrt(s)
        B_ok &= any(t * (float(C[j] @ C[j]) + 1.0 - rho) + 2.0 * float(C[i] @ C[j]) <= 0.0
                    for j in range(n))
    parts["B"] = B_ok

    # C: pair bisector ∩ circle (auxiliaries nu, w)
    C_ok = True
    for i, j in itertools.combinations(range(n), 2):
        nvec = C[j] - C[i]
        N = float(nvec @ nvec)
        if N <= 0.0:
            continue                      # guard nu>0 unsatisfiable: vacuous
        H = float(C[j] @ C[j]) - float(C[i] @ C[i])
        nu = math.sqrt(N)
        w2 = 4.0 * nu * nu - H * H
        if w2 < 0.0:
            raise AssertionError("guaranteed impossible by PROOF L2 (no tangency)")
        w = math.sqrt(w2) / 2.0
        perp = np.array([-nvec[1], nvec[0]])
        for sigma in (1.0, -1.0):
            ok_s = any(nu * nu * (1.0 + float(C[k] @ C[k]) - rho)
                       - H * float(nvec @ C[k])
                       - sigma * 2.0 * w * float(perp @ C[k]) <= 0.0 for k in range(n))
            C_ok &= ok_s
    parts["C"] = C_ok

    # D: circumcenters of non-collinear triples with |x|<=1 (x from two linear equations)
    D_ok = True
    for i, j, k in itertools.combinations(range(n), 3):
        a, b, c = C[i], C[j], C[k]
        delta = float((b - a)[0] * (c - a)[1] - (b - a)[1] * (c - a)[0])
        if delta == 0.0:
            continue                      # collinear (or repeated positions): vacuous
        M = np.array([[2.0 * (b - a)[0], 2.0 * (b - a)[1]],
                      [2.0 * (c - a)[0], 2.0 * (c - a)[1]]])
        rhs = np.array([float(b @ b) - float(a @ a), float(c @ c) - float(a @ a)])
        x = np.linalg.solve(M, rhs)
        if float(x @ x) > 1.0:            # circumcenter outside D -> not a candidate
            continue
        D_ok &= any(float((x - C[m]) @ (x - C[m])) <= rho for m in range(n))
    parts["D"] = D_ok

    ok = parts["A"] and parts["B"] and parts["C"] and parts["D"]
    if verbose:
        print(f"    iface parts: {parts}")
    return ok, parts


def main():
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "..", "evidence",
        "qe-interface-check.json")
    cases = dict(battery())
    picks = ["all-zero-n12", "all-zero-n1", "single-origin", "single-0.5",
             "single-rational", "pair-anticlockwise", "pair-origin-0.9",
             "all-same-0.6-0.8", "ring+origin-m3-rho0.9", "ring+origin-m12-rho1.0",
             "ring-m12-rho1.0", "ring+origin-m6-rho1.0", "dup6x2+origin", "dup6x2",
             "collinear-x12", "collinear-y+origin", "collinear-3+random",
             "cc-on-bd-triple", "cc-on-bd-triple+origin",
             "near-tangent-bis-1e-09", "tight-pair-1.0-0.999999",
             "ess-a-only-origin", "ess-b-single-center", "ess-c-two-centers",
             "ess-d-regular12-on-circle", "ess-d-square-on-circle",
             "rand-disk-n12-3", "rand-circle-n12-0", "c182-n12-diagnostic"]
    rows, mismatches, borderline = [], [], []
    for name in picks:
        if name not in cases:
            continue
        C = np.asarray(cases[name], float)
        Rc, _ = R_cand(C)
        # probes: far from R_cand (decisive) and a narrow band around R_cand
        probes = {0.0, 1 / 3, 0.25, 0.5, 1.0, 2.0}
        if Rc > 0:
            probes |= {Rc * (1.0 + d) for d in (-1e-3, -1e-6, 1e-6, 1e-3, 2.0, 0.5)}
        for r in sorted(probes):
            if r <= 0.0:
                continue
            cov_iface, parts = iface(C, r)
            margin = r - Rc
            if abs(margin) <= 1e-9 * max(1.0, Rc):
                borderline.append(dict(name=name, r=r, R_cand=Rc, iface=cov_iface,
                                       margin=margin, parts=parts))
                continue
            cov_geom = (margin > 0)          # exact comparison, no tolerance
            agree = (cov_iface == cov_geom)
            rows.append(dict(name=name, r=r, R_cand=Rc, margin=margin,
                             iface=cov_iface, geom=cov_geom, agree=agree, parts=parts))
            if not agree:
                mismatches.append(dict(name=name, r=r, R_cand=Rc, margin=margin,
                                       iface=cov_iface, geom=cov_geom, parts=parts))
        nm = sum(1 for x in rows if x["name"] == name and not x["agree"])
        nb = sum(1 for x in borderline if x["name"] == name)
        print(f"{name:28s} R_cand={Rc:.12f}  decisive={sum(1 for x in rows if x['name']==name)}"
              f"  mismatch={nm}  borderline_skipped={nb}")
    summary = dict(n_decisive=len(rows), n_mismatch=len(mismatches),
                   n_borderline_skipped=len(borderline),
                   mismatches=mismatches[:10],
                   borderline=borderline[:10])
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(dict(summary=summary, rows=rows), fh, indent=1)
    print("\n== summary ==")
    print(json.dumps({k: v for k, v in summary.items()
                      if k not in ("mismatches", "borderline")}, indent=1))
    for m in summary["mismatches"]:
        print("  MISMATCH:", m)
    for m in summary["borderline"]:
        print("  BORDERLINE(skipped):", {k: m[k] for k in ("name", "r", "R_cand", "iface")})
    print("log ->", out)


if __name__ == "__main__":
    main()
