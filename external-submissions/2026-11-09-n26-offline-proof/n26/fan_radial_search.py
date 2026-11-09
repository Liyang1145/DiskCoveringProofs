"""Numerical search for joint Voronoi fan and radial dual certificates."""

import argparse
import json
import os
from pathlib import Path
import warnings

os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["OMP_NUM_THREADS"] = "1"

import numpy as np
from scipy.optimize import OptimizeWarning, linprog


def angular_fractions(s, t, r):
    with np.errstate(divide="ignore", invalid="ignore"):
        u = (t * t + s[:, None] ** 2 - r * r) / (2 * s[:, None] * t)
    u[:, t == 0] = np.where(s[:, None] <= r, -1, 1)
    return np.arccos(np.clip(u, -1, 1)).T / np.pi


def fan_constant(lam):
    return (np.sqrt(1 - 4 * lam * lam) - 2 * lam * np.arccos(2 * lam)) / 2


def joint_dual(r, k, lam, samples, rmin=None, low=None, step=.008, no_repeat=False, tau=0, n=26,
               core_caps=False, middle_split=None):
    rmin = r if rmin is None else rmin
    radii = [1,r,2*r,1-2*r]
    cap = r
    if core_caps:
        central = 1-4*r
        if not 0 < central < r or low not in (0,1):
            raise ValueError("Invalid central disk grouping")
        cap = r-central if low == 0 else np.sqrt(r*r-central*central)
        radii.append(central)
    s = np.unique(np.round(np.concatenate((np.arange(step, 1, step), radii)), 10))
    count_s = s[s > r]
    need = np.floor(np.pi / np.arcsin(r / count_s) - 1e-9).astype(int) + 1
    ranges = [(0, cap)]
    counts = [1]
    if low is None:
        ranges.append((0, 1 - rmin))
        counts.append(n - 1 - k)
    else:
        ranges.extend(((0, 1 - 3 * r), (1 - 3 * r, 1 - rmin)))
        counts.extend((low, n - 1 - k - low))
        if middle_split is not None:
            q,left = middle_split
            a,b = ranges.pop()
            count = counts.pop()
            if not a < q < b or not 0 <= left <= count:
                raise ValueError("Invalid middle split")
            ranges.extend(((a,q),(q,b)))
            counts.extend((left,count-left))
    ranges.append((1 - r, 1))
    counts.append(k)
    edges = np.concatenate((np.abs(s - r), s + r, np.sqrt(count_s*count_s - r*r)))
    edges = np.concatenate((edges, edges - 1e-9, edges + 1e-9))
    grids = []
    for a, b in ranges:
        grids.append(np.unique(np.concatenate(
            (np.linspace(a, b, 1 + int((b - a) * samples)), edges[(edges > a) & (edges < b)]))))
    t = np.concatenate(grids)
    outer = grids[-1]
    outer_start = len(t) - len(outer)
    beta = np.linspace(0, np.arcsin(r), 1201)
    c = fan_constant(lam)
    lam_arc = lam - tau
    c_arc = fan_constant(lam_arc)
    change = 0
    if tau:
        h = np.sqrt(2 * lam)
        side = (np.sqrt(1 - h * h) - h * np.arccos(h)) / 2
        seam = max(0, 2 * fan_constant(lam - tau / 2) - np.pi * tau, h * (2 * side - 2 * tau))
        change = seam - 2 * c
    cap = (beta - np.sin(2 * beta) / 2) / (r * r)

    def fan_cost(half_angle):
        x = np.clip(np.sin(half_angle) / r, 0, 1)
        cap = (half_angle - np.sin(2 * half_angle) / 2) / (r * r)
        long = x * np.sqrt(1 - x * x) - 2 * lam_arc * np.arcsin(x)
        return np.where(x > .5,np.minimum(c_arc,long),c_arc) + cap - 2*c + change

    h = fan_cost(beta)
    delta = lam * np.pi + min(c, 2*c - cap[-1]) - .0005
    short = (beta > 0) & (beta <= beta[-1] / 2 + .0004)
    slope_min = np.max((h[short] - delta) / beta[short]) + .02
    if k == 14 or no_repeat:
        # All fourteen exterior disks are indispensable on the unit circle,
        # so a split Voronoi arc would contradict boundary coverage.
        slope_min, delta = -40, 0
    h[0] = 0

    max_beta = angular_fractions(np.ones(1), outer, r)[:, 0] * np.pi
    end_cost = fan_cost(max_beta)
    allowed = np.clip(np.searchsorted(beta, max_beta + 1e-12, side="right") - 1, 0, len(beta) - 1)
    groups = np.eye(len(counts))[np.repeat(np.arange(len(counts)), list(map(len, grids)))]
    positive = (t[:, None] > count_s - r + 1e-13) & (t[:, None] < count_s + r - 1e-13)
    angle = np.column_stack((angular_fractions(s, t, r), positive / need))
    n_s = angle.shape[1]
    base_mat = np.column_stack((angle, np.zeros(len(t)), -groups))
    obj = np.concatenate((-np.ones(n_s), [np.pi, *counts]))
    mat = [base_mat]
    rhs = [np.zeros(len(t))]
    for _ in range(30):
        with warnings.catch_warnings():
            warnings.filterwarnings("ignore", "Unrecognized options detected", OptimizeWarning)
            res = linprog(obj, A_ub=np.vstack(mat), b_ub=np.concatenate(rhs),
                          bounds=[(0, 25)] * n_s + [(slope_min, 0)] + [(0, None)] * len(counts),
                          method="highs", options={"threads": 1})
        if not res.success:
            raise RuntimeError(res.message)
        slope = res.x[n_s]
        f = h - slope * beta
        # For each t take the largest score with beta within its available arc.
        index = np.zeros(len(f), dtype=int)
        best = 0
        for j, value in enumerate(f):
            if value > f[best]:
                best = j
            index[j] = best
        selected = index[allowed]
        use_endpoint = end_cost - slope * max_beta > f[selected]
        beta_choice = np.where(use_endpoint, max_beta, beta[selected])
        cost_choice = np.where(use_endpoint,end_cost,h[selected])
        violation = angle[outer_start:] @ res.x[:n_s] + cost_choice - slope * beta_choice - res.x[-1]
        use = violation > 3e-7
        if not np.any(use):
            break
        rows = base_mat[outer_start:][use].copy()
        rows[:, n_s] = -beta_choice[use]
        mat.append(rows)
        rhs.append(-cost_choice[use])
    else:
        raise RuntimeError("Constraint generation did not converge")
    area = (n * 2 * np.pi * lam + (6*n-6) * c - 2 * np.pi * tau + res.fun) * r * r
    return area, s, count_s, need, res.x[:n_s], res.x[n_s], res.x[n_s+1:], delta


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--r", type=float, required=True)
    parser.add_argument("--rmin", type=float)
    parser.add_argument("--k", type=int, nargs="+", default=[14, 15, 16, 17])
    parser.add_argument("--lams", type=float, nargs="+", default=[.15, .185, .22, .255])
    parser.add_argument("--samples", type=int, default=300)
    parser.add_argument("--step", type=float, default=.008)
    parser.add_argument("--no-repeat", action="store_true")
    parser.add_argument("--taus", type=float, nargs="+", default=[0])
    parser.add_argument("--disks", type=int, default=26)
    parser.add_argument("--split", action="store_true", help="Branch on the count below 1-3r")
    parser.add_argument("--low-count", type=int, nargs="+")
    parser.add_argument("--integer-fans", action="store_true")
    parser.add_argument("--core-caps", action="store_true")
    parser.add_argument("--middle-cut",type=float)
    parser.add_argument("--middle-counts",type=int,nargs="+")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    payload = []
    rmin = args.r if args.rmin is None else args.rmin
    participants = int(np.floor(np.pi / np.arcsin(args.r / (1-2*args.r)) - 1e-9)) + 1
    branches = [(k, low) for k in args.k for low in (
        args.low_count if args.low_count is not None else (
            range(args.disks - k - participants) if args.split else [None])
    )]
    if args.middle_cut is not None and any(low is None for _,low in branches):
        parser.error("The middle cut requires the inner population split")
    split_branches = [(k,low,(args.middle_cut,left) if args.middle_cut is not None else None)
                      for k,low in branches for left in (
                          (args.middle_counts or range(args.disks-k-low))
                          if args.middle_cut is not None else [None])]
    for k, low, middle in split_branches:
        best = None
        for lam, tau in ((l, t) for l in args.lams for t in args.taus if 0 <= t < l):
            if tau and not args.no_repeat:
                raise ValueError("Seam coupling currently requires the no-repeat domain")
            result = joint_dual(args.r, k, lam, args.samples, rmin, low, args.step,
                                args.no_repeat, tau, args.disks,args.core_caps,middle)
            area, s, count_s, need, w, slope, caps, delta = result
            if args.integer_fans:
                c = fan_constant(lam)
                loss = max(0., 2*np.pi*lam - max(
                    m/2*np.sin(2*np.pi/m) - m*c for m in range(3, args.disks)
                ))
                area -= args.r**2 * (args.disks-k) * loss
                result = (area, *result[1:])
            print(f"r={args.r:.7f} k={k} low={low} mid={middle} lambda={lam:.5f} tau={tau:.5f} "
                  f"area={area:.10f} slope={slope:.7f} weights={np.sum(w):.6g}", flush=True)
            if best is None or area < best[0]:
                best = (*result, lam, tau)
        area, s, count_s, need, w, slope, caps, delta, lam, tau = best
        if area < np.pi:
            slack = (np.pi - area) / (args.disks * args.r * args.r)
            entry = {
                "disks": args.disks,
                "k": k,
                "low": low,
                "participants": participants,
                "r_min": f"{rmin:.10f}",
                "r_max": f"{args.r:.10f}",
                "lambda": f"{lam:.10f}",
                "tau": f"{tau:.10f}",
                "slope": f"{slope:.10f}",
                "repeat_penalty": f"{delta:.10f}",
                "integer_fans": args.integer_fans,
                "core_caps": args.core_caps,
                "weights": [[f"{s0:.10f}", f"{w0:.10f}"] for s0, w0 in zip(s, w) if w0 > 1e-9],
                "count_weights": [[f"{s0:.10f}", int(m0), f"{w0:.10f}"]
                                  for s0, m0, w0 in zip(count_s, need, w[len(s):]) if w0 > 1e-9],
                "caps": [f"{v + .74 * slack:.12f}" for v in caps],
            }
            if middle is not None:
                entry["middle_split"] = [f"{middle[0]:.10f}",middle[1]]
            payload.append(entry)
    if args.out:
        args.out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
