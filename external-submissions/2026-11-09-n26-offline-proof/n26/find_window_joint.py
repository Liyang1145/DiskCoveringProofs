"""Generate offline numerical proposals for short-window radial proofs."""

import argparse
import json
import warnings
from pathlib import Path

from fan_radial_search import angular_fractions, fan_constant, np
from scipy.optimize import OptimizeWarning, linprog
from verify_patch14 import RADIUS
from verify_window_joint import HALF, branches, groups


def solve(b, k, outside, lam, tau, samples, step):
    r = float(RADIUS)
    domains = groups(b, k, outside)
    s = np.unique(np.round(np.r_[np.arange(step, 1, step), 1, r, 2*r, 1-2*r], 10))
    ss = s[s > r]
    m = np.floor(np.pi / np.arcsin(r / ss) - 1e-9).astype(int) + 1
    t_edges = np.concatenate((np.abs(s-r), s+r, np.sqrt(ss*ss-r*r)))
    t_edges = np.r_[t_edges, t_edges-1e-9, t_edges+1e-9]
    grids = []
    for _, lo, hi, _ in domains:
        a, b1 = float(lo), float(hi)
        grids.append(np.unique(np.r_[np.linspace(a, b1, 2+int((b1-a)*samples)),
                                     t_edges[(t_edges > a) & (t_edges < b1)]]))
    t = np.concatenate(grids)
    group = np.repeat(np.arange(len(domains)), list(map(len, grids)))
    arc_type = np.repeat([j if j is not None else -1 for _, _, _, j in domains],
                         list(map(len, grids)))
    angles = np.column_stack((angular_fractions(s, t, r),
                              ((t[:, None] > ss-r+1e-13) & (t[:, None] < ss+r-1e-13)) / m))
    nw = angles.shape[1]
    c, ca = fan_constant(lam), fan_constant(lam-tau)
    seam = 2*c
    if tau:
        h = np.sqrt(2*lam)
        side = (np.sqrt(1-h*h)-h*np.arccos(h))/2
        seam = max(0, 2*fan_constant(lam-tau/2)-np.pi*tau, h*(2*side-2*tau))

    def cost(a):
        x = np.clip(np.sin(a)/r, 0, 1)
        g = np.where(x > .5, np.minimum(ca, x*np.sqrt(1-x*x)-2*(lam-tau)*np.arcsin(x)), ca)
        return g + (a-np.sin(2*a)/2)/(r*r) + seam - 4*c

    arc_rows = np.flatnonzero(arc_type >= 0)
    caps_alpha = angular_fractions(np.ones(1), t[arc_rows], r)[:, 0] * np.pi
    grid = np.linspace(0, np.arcsin(r), 2001)
    grid_h = cost(grid)
    end_h = cost(caps_alpha)
    allowed = np.clip(np.searchsorted(grid, caps_alpha+1e-12, side="right")-1, 0, len(grid)-1)
    rows = np.column_stack((angles, np.zeros((len(t), 2)), -np.eye(len(domains))[group]))
    rhs = np.where(arc_type >= 0, -cost(0.), 0.)
    order = np.zeros(rows.shape[1])
    order[nw:nw+2] = [-1, 1]
    obj = np.r_[-np.ones(nw), float(HALF), np.pi-float(HALF), [d[0] for d in domains]]
    mat, bound = [rows, order[None, :]], [rhs, np.zeros(1)]
    for _ in range(40):
        with warnings.catch_warnings():
            warnings.filterwarnings("ignore", "Unrecognized options detected", OptimizeWarning)
            res = linprog(obj, A_ub=np.vstack(mat), b_ub=np.concatenate(bound),
                          bounds=[(0, 30)]*nw + [(-60, 0), (-220, 0)] + [(None, None)]*len(domains),
                          method="highs", options={"threads": 1})
        if not res.success:
            raise RuntimeError(res.message)
        added = False
        for j in (0, 1):
            slope = res.x[nw+j]
            f = grid_h - slope*grid
            prefix, best = [], 0
            for i, v in enumerate(f):
                if v > f[best]:
                    best = i
                prefix.append(best)
            selection = np.array(prefix)[allowed]
            ends = end_h - slope*caps_alpha > f[selection]
            a = np.where(ends, caps_alpha, grid[selection])
            h = np.where(ends, end_h, grid_h[selection])
            err = angles[arc_rows] @ res.x[:nw] + h - slope*a - res.x[nw+2+group[arc_rows]]
            use = (arc_type[arc_rows] == j) & (err > 5e-7)
            if np.any(use):
                proposal = rows[arc_rows[use]].copy()
                proposal[:, nw+j] = -a[use]
                mat.append(proposal)
                bound.append(-h[use])
                added = True
        if not added:
            break
    else:
        raise RuntimeError("Constraint generation did not converge")
    area = r*r*(52*np.pi*lam + 150*c - 2*np.pi*tau + res.fun)
    return area, s, ss, m, res.x[:nw], res.x[nw:nw+2], res.x[nw+2:]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--boundary", type=int, nargs="+", default=[15, 16])
    parser.add_argument("--lams", type=float, nargs="+", default=[.247, .254, .26])
    parser.add_argument("--taus", type=float, nargs="+", default=[.04, .07, .103, .12])
    parser.add_argument("--samples", type=int, default=1000)
    parser.add_argument("--step", type=float, default=.006)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    entries = []
    for b in args.boundary:
        for k, outside in branches(b):
            best = None
            for lam in args.lams:
                for tau in args.taus:
                    if tau >= lam:
                        continue
                    ans = solve(b, k, outside, lam, tau, args.samples, args.step)
                    if best is None or ans[0] < best[0]:
                        best = (*ans, lam, tau)
            area, s, ss, m, w, slopes, caps, lam, tau = best
            print(f"b={b} k={k} outside={outside} area={area:.10f} lambda={lam} tau={tau}", flush=True)
            if area >= np.pi:
                continue
            slack = (np.pi-area)/(26*float(RADIUS)**2)
            entries.append({
                "b": b, "k": k, "outside": outside,
                "lambda": f"{lam:.10f}", "tau": f"{tau:.10f}",
                "slopes": [f"{a:.12f}" for a in slopes],
                "caps": [f"{a + .7*slack:.12f}" for a in caps],
                "weights": [[f"{a:.10f}", f"{v:.10f}"] for a, v in zip(s, w) if v > 1e-9],
                "count_weights": [[f"{a:.10f}", int(b1), f"{v:.10f}"]
                                  for a, b1, v in zip(ss, m, w[len(s):]) if v > 1e-9],
            })
    if args.out:
        args.out.write_text(json.dumps(entries, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
