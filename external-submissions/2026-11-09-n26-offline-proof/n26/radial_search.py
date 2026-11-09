"""Find a numerical dual certificate for the concentric-circle relaxation."""

import argparse
import json
import os
from pathlib import Path

os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["OMP_NUM_THREADS"] = "1"

import numpy as np
from scipy.optimize import linprog


def dual(rmin, rmax, k, samples):
    s = np.linspace(.004, 1, 251)
    s = np.unique(np.round(np.concatenate((s, [rmax, 2 * rmax, 1 - 2 * rmax])), 10))
    core = np.linspace(0, rmax, samples // 2 + 1)
    inner = np.linspace(0, 1 - rmin, samples + 1)
    # Moving an exterior center radially in to the unit circle only improves
    # its distances to the unit disk. The exact verifier uses the same bound.
    outer = np.linspace(1 - rmax, 1, samples // 2 + 1)
    t = np.concatenate((core, inner, outer))
    with np.errstate(divide="ignore", invalid="ignore"):
        v = (t * t + s[:, None] ** 2 - rmax * rmax) / (2 * s[:, None] * t)
    v[:, t == 0] = np.where(s[:, None] <= rmax, -1, 1)
    angle = np.arccos(np.clip(v, -1, 1)).T / np.pi
    groups = np.eye(3)[np.repeat(np.arange(3), [len(core), len(inner), len(outer)])]
    obj = np.concatenate((np.zeros(len(s)), [1, 25 - k, k]))
    mat = np.concatenate((angle, -groups), axis=1)
    res = linprog(obj, A_ub=mat, b_ub=np.zeros(len(t)),
                  A_eq=[np.concatenate((np.ones(len(s)), np.zeros(3)))],
                  b_eq=[1], bounds=(0, 1), method="highs", options={"threads": 1})
    if not res.success:
        raise RuntimeError(res.message)
    return res.fun, s, res.x[: len(s)], res.x[-3:]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rmin", type=float)
    parser.add_argument("--rmax", type=float, required=True)
    parser.add_argument("--k", type=int, nargs="+", default=[14, 15, 16, 17])
    parser.add_argument("--samples", type=int, default=1000)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    rmin = args.rmax if args.rmin is None else args.rmin
    payload = []
    for k in args.k:
        score, s, w, b = dual(rmin, args.rmax, k, args.samples)
        print(f"k={k}, [{rmin:.7f}, {args.rmax:.7f}]: {score:.10f}", flush=True)
        if score >= 1:
            continue
        weights = np.rint(w * 10**9).astype(int)
        payload.append({
            "k": k,
            "r_min": f"{rmin:.10f}",
            "r_max": f"{args.rmax:.10f}",
            "weights": [[f"{radius:.10f}", int(weight)] for radius, weight in zip(s, weights) if weight],
            "caps": [f"{v + (1 - score) * .75 / 26:.12f}" for v in b],
        })
    if args.out:
        args.out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
