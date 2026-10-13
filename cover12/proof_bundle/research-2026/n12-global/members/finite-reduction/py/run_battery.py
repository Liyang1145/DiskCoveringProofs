"""run_battery.py -- falsification battery for the finite candidate reduction.

For each configuration C (generic + degenerate families) we compute
  R_cand  = max over the finite candidate list K(C) of f_C      (float)
  R_ref   = independent reference max over D (grid + projected pattern search)
  gap     = R_ref - R_cand
The theorem predicts gap <= 0 up to floating point noise and R_cand = R(C) exactly.
A *sustained positive* gap (>> 1e-9) on any configuration is a counterexample
candidate and must be investigated by hand.  Negative gap beyond 1e-12 means the
reference search failed (grid/refinement issue), not a theorem failure.

Usage:  py -3 -B run_battery.py [outdir]
"""
from __future__ import annotations

import json
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from candlib import (R_cand, R_cand_all, R_ref, f_min, nearest_set,  # noqa: E402
                     candidate_points, classify_argmax, antipode)

RNG = np.random.default_rng(20260926)


# ------------------------------------------------------------ family builders
def random_disk(n, rng, rmax=1.0):
    r = rmax * np.sqrt(rng.random(n))
    a = 2 * np.pi * rng.random(n)
    return np.stack([r * np.cos(a), r * np.sin(a)], axis=1)


def random_circle(n, rng):
    a = 2 * np.pi * rng.random(n)
    return np.stack([np.cos(a), np.sin(a)], axis=1)


def regular(m, rho, phase=0.0, n=None, origin=False):
    a = phase + 2 * np.pi * np.arange(m) / m
    P = rho * np.stack([np.cos(a), np.sin(a)], axis=1)
    if origin:
        P = np.vstack([np.zeros((1, 2)), P])
    if n is not None:                       # pad with repetitions of the last point
        while len(P) < n:
            P = np.vstack([P, P[-1:]])
    return P


def circumcenter_on_bd_triple(rho0=0.5, phi_deg=(120.0, 180.0, 240.0), xstar=(1.0, 0.0)):
    xs = np.array(xstar, float)
    out = []
    for ph in phi_deg:
        t = np.deg2rad(ph)
        out.append(xs + rho0 * np.array([np.cos(t), np.sin(t)]))
    return np.array(out)


def load_c182(path=None, key="centers_dec17"):
    """Read-only reuse of the n=12 C182 configuration (diagnostic object only)."""
    if path is None:
        here = os.path.dirname(os.path.abspath(__file__))
        path = os.path.join(here, "..", "..", "..", "..", "session2", "n1314", "cfg",
                            "cert_n12_othern.json")
    with open(path, encoding="utf-8") as fh:
        j = json.load(fh)
    obj = j
    for k in key.split("."):
        obj = obj[int(k)] if isinstance(obj, list) else obj[k]
    return np.array([[float(p[0]), float(p[1])] for p in obj], dtype=float)


def battery():
    """Return list of (name, C)."""
    cases = []
    rng = RNG

    # --- (0) tiny / fully degenerate --------------------------------------
    cases.append(("all-zero-n12", np.zeros((12, 2))))
    cases.append(("all-zero-n1", np.zeros((1, 2))))
    cases.append(("single-origin", np.zeros((1, 2))))
    cases.append(("single-0.5", np.array([[0.5, 0.0]])))
    cases.append(("single-0.99-diag", np.array([[0.99 / math.sqrt(2)] * 2])))
    cases.append(("single-rational", np.array([[0.6, 0.8]])))
    cases.append(("all-same-0.6-0.8", np.tile([0.6, 0.8], (12, 1))))
    cases.append(("pair-anticlockwise", np.array([[0.5, 0.0], [-0.5, 0.0]])))
    cases.append(("pair-origin-0.9", np.array([[0.0, 0.0], [0.9, 0.0]])))

    # --- (1) structural ring families -------------------------------------
    for m in (3, 4, 5, 6, 8, 12):
        for rho in (0.25, 0.5, 0.75, 0.9, 1.0):
            cases.append((f"ring-m{m}-rho{rho}", regular(m, rho)))
            cases.append((f"ring+origin-m{m}-rho{rho}", regular(m, rho, origin=True)))
    for m in (3, 4, 5, 6, 12):
        for rho in (0.4, 0.8, 0.99):
            cases.append((f"ring+3origin-m{m}-rho{rho}",
                          np.vstack([np.zeros((3, 2)), regular(m, rho)])))

    # --- (2) duplicates / collinear ---------------------------------------
    base = regular(6, 0.8)
    cases.append(("dup6x2", np.vstack([base, base])))
    cases.append(("dup6x2+origin", np.vstack([np.zeros((1, 2)), base, base])))
    xs = np.linspace(-1.0, 1.0, 12)
    cases.append(("collinear-x12", np.stack([xs, np.zeros(12)], axis=1)))
    cases.append(("collinear-3+random", np.vstack([
        np.array([[-0.6, 0.0], [0.0, 0.0], [0.6, 0.0]]), random_disk(4, rng)])))
    cases.append(("collinear-y+origin", np.stack([np.zeros(6), np.linspace(-1, 1, 6)], axis=1)))

    # --- (3) boundary tangency / Voronoi vertex on bd ---------------------
    cases.append(("cc-on-bd-triple", circumcenter_on_bd_triple()))
    cases.append(("cc-on-bd-triple+origin", np.vstack([np.zeros((1, 2)),
                                                       circumcenter_on_bd_triple()])))
    for eps in (1e-2, 1e-4, 1e-6, 1e-9):
        cases.append((f"near-tangent-bis-{eps:g}",
                      np.array([[1.0, 0.0], [1.0 - eps, 0.0], [0.0, 0.0], [-0.3, 0.4]])))
    cases.append(("tight-pair-1.0-0.999999", np.array([[1.0, 0.0], [0.999999, 0.0],
                                                       [0.0, 1.0], [0.0, -1.0]])))

    # --- (4) essentiality examples for each candidate class ---------------
    cases.append(("ess-a-only-origin", np.zeros((1, 2))))
    cases.append(("ess-b-single-center", np.array([[0.0, 0.9]])))
    cases.append(("ess-c-two-centers", np.array([[0.5, 0.0], [-0.5, 0.0]])))
    cases.append(("ess-d-regular12-on-circle", regular(12, 1.0)))
    cases.append(("ess-d-regular6-on-circle", regular(6, 1.0)))
    cases.append(("ess-d-square-on-circle", regular(4, 1.0)))

    # --- (5) random generic ------------------------------------------------
    for n in (1, 2, 3, 5, 8, 12):
        for t in range(12):
            cases.append((f"rand-disk-n{n}-{t}", random_disk(n, rng)))
    for n in (3, 6, 12):
        for t in range(8):
            cases.append((f"rand-circle-n{n}-{t}", random_circle(n, rng)))
    for t in range(10):   # mixed: circle + interior + possible origin
        n1 = 6
        C = np.vstack([random_disk(n1, rng), random_circle(4, rng)])
        if t % 3 == 0:
            C = np.vstack([np.zeros((1, 2)), C])
        cases.append((f"rand-mixed-{t}", C))

    # --- (6) perturbed structured (near-degenerate) -----------------------
    for t in range(8):
        base = regular(5, 0.95, phase=0.3, origin=True)
        C = base + 1e-3 * rng.standard_normal(base.shape)
        cases.append((f"pert-ring5-{t}", C))
    for t in range(6):
        base = regular(3, 1.0)
        C = base + 1e-6 * rng.standard_normal(base.shape)
        cases.append((f"pert-tri-on-circle-{t}", C))
    try:
        C182 = load_c182()
        cases.append(("c182-n12-diagnostic", C182))
    except Exception as exc:                                  # pragma: no cover
        print(f"[warn] C182 not loaded: {exc}")
    return cases


# ------------------------------------------------------------------ driver
def main():
    outdir = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "..", "evidence")
    os.makedirs(outdir, exist_ok=True)
    cases = battery()
    rows = []
    t0 = time.time()
    worst = (-1e9, None)
    for name, C in cases:
        C = np.asarray(C, float)
        n = len(C)
        Rc, argc = R_cand(C)
        Ra, arga = R_cand_all(C)
        ref = R_ref(C)
        gap = ref["value"] - Rc
        vg = ref["grid_value"] - Rc
        tags, ns = classify_argmax(C, argc["pos"])
        rows.append(dict(name=name, n=n,
                         n_distinct=len({(round(float(p[0]), 12), round(float(p[1]), 12))
                                         for p in C}),
                         R_cand=Rc, R_cand_nofilter=Ra, R_ref=ref["value"],
                         gap=gap, gap_all=ref["value"] - Ra,
                         argmax_kind=argc["kind"], argmax_idx=list(argc["idx"]),
                         argmax_pos=[float(argc["pos"][0]), float(argc["pos"][1])],
                         ref_argmax=[float(ref["argmax"][0]), float(ref["argmax"][1])],
                         ref_n_nearest=ref["n_nearest"],
                         ref_ns=ref["nearest"],
                         grid_value=ref["grid_value"],
                         grid_violation=vg,
                         tags=tags))
        if gap > worst[0]:
            worst = (gap, name)
        flag = "  <== LARGE GAP" if gap > 1e-7 else ""
        vflag = "  <== GRID VIOLATION" if vg > 1e-9 else ""
        print(f"{name:32s} n={n:2d} R_cand={Rc:.12f} R_ref={ref['value']:.12f} "
              f"gap={gap:+.2e} gviol={vg:+.2e} kind={argc['kind']} "
              f"|argmin|={ref['n_nearest']}{flag}{vflag}")
        if name.startswith("ess-"):
            from candlib import R_by_class
            print("      per-class maxima:")
            R_by_class(C, verbose=True)

    summary = dict(
        n_cases=len(rows),
        worst_gap=worst[0], worst_gap_case=worst[1],
        n_gap_gt_1em7=sum(1 for r in rows if r["gap"] > 1e-7),
        n_gap_gt_1em9=sum(1 for r in rows if r["gap"] > 1e-9),
        max_grid_violation=max(r["grid_violation"] for r in rows),
        n_grid_violation_gt_1em9=sum(1 for r in rows if r["grid_violation"] > 1e-9),
        max_negative_gap=min(r["gap"] for r in rows),
        cpu_s=time.time() - t0,
    )
    with open(os.path.join(outdir, "battery.json"), "w", encoding="utf-8") as fh:
        json.dump(dict(summary=summary, rows=rows), fh, indent=1)
    print("\n== summary ==")
    print(json.dumps(summary, indent=1))
    print(f"log -> {os.path.join(outdir, 'battery.json')}")


if __name__ == "__main__":
    main()
