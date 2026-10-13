"""hubline_proposals.py -- PROPOSALS ONLY (numeric, Lead-assigned task).

h-line chart (lead/K10-HUB-LINE-CHART.md): h1=(x-s,y), h2=(x+s,y), s=d/2 in
(0,U), x,y >= 0.  Exposed hub arcs: centres pi and 0, halfwidth pi-acos(s/U).

Every sampled point here passes the FULL exact-core numeric criterion:
  * x >= a:            (x-s)^2 + y^2 <= e0^2                     [e0 = 3U-1]
  * 0 <= x < a:        s^2 + (y + sqrt(a^2-x^2))^2 <= U^2
  * antipode guard:    if a(s-x) <= x*sqrt((x-s)^2+y^2) then (x-s)^2+y^2 <= e0^2
together with x <= s+e0, (x+s)^2+y^2 <= (1-U)^2, 0 <= y <= e0, s < U.

Outputs per sampled point: (s,x,y), the criterion values, the weight triples and
the normalised min-max capture m* (criterion needs m* < 0.1), plus a per-s joint
test: does ONE weight triple cover all that layer's samples at t = 0.1?
"""
from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import hubline_lp_probe as H  # build() with chart geometry (float)

OUT = HERE.parent / "evidence"
U = H.U
A_CORE = 1 - 2 * U
E0 = 3 * U - 1
PER = H.PER
K = H.K


def core_vals(s, x, y):
    """numeric exact-core criterion values (returns detail dict)."""
    d = dict(s=s, x=x, y=y)
    if x >= A_CORE:
        d["branch"] = "x>=a"
        d["core_lhs"] = (x - s) ** 2 + y * y
        d["core_rhs"] = E0 ** 2
    else:
        q = math.sqrt(max(0.0, A_CORE ** 2 - x * x))
        d["branch"] = "x<a"
        d["q"] = q
        d["core_lhs"] = s * s + (y + q) ** 2
        d["core_rhs"] = U ** 2
        ap = A_CORE * (s - x)
        thr = x * math.sqrt((x - s) ** 2 + y * y)
        d["antipode_active"] = bool(ap <= thr + 1e-15)
    d["core_ok"] = bool(d["core_lhs"] <= d["core_rhs"] + 1e-12)
    d["surplus"] = float(d["core_rhs"] - d["core_lhs"])
    if d.get("antipode_active") and (x - s) ** 2 + y * y > E0 ** 2 + 1e-12:
        d["antipode_lhs"] = (x - s) ** 2 + y * y
        d["antipode_rhs"] = E0 ** 2
        d["core_ok"] = False
    d["inactive_ok"] = bool((x + s) ** 2 + y * y <= (1 - U) ** 2 + 1e-12)
    d["x_le_s_e0"] = bool(x <= s + E0 + 1e-12)
    d["legal"] = bool(d["core_ok"] and d["inactive_ok"] and d["x_le_s_e0"]
                      and 0 < s < U and x >= 0 and 0 <= y <= E0 + 1e-12)
    return d


def lp_normalised(A, req):
    """minimise m s.t. A w <= m (req.w = 1), w nonneg in the sufficient sense."""
    nw = 3 * PER
    nvar = nw + 6 * K + 1
    mi = nw + 6 * K
    A_ub = np.zeros((A.shape[0], nvar))
    A_ub[:, 0:nw] = A
    A_ub[:, mi] = -1.0
    b_ub = np.zeros(A.shape[0])
    rows, b2 = [], []
    for j in range(3):
        r = np.zeros(nvar)
        r[j * PER] = -1.0
        for k in range(6 * K // 3):     # 2K coefficients per block
            r[nw + j * (2 * K) + k] = 1.0
        rows.append(r); b2.append(0.0)
        for k in range(2 * K):
            r1 = np.zeros(nvar); r1[j * PER + 1 + k] = 1.0
            r1[nw + j * (2 * K) + k] = -1.0
            rows.append(r1); b2.append(0.0)
            r2 = np.zeros(nvar); r2[j * PER + 1 + k] = -1.0
            r2[nw + j * (2 * K) + k] = -1.0
            rows.append(r2); b2.append(0.0)
    A_ub = np.vstack([A_ub, np.array(rows)])
    b_ub = np.concatenate([b_ub, np.array(b2)])
    A_eq = np.zeros((1, nvar)); A_eq[0, 0:nw] = req
    b_eq = np.array([1.0])
    c = np.zeros(nvar); c[mi] = 1.0
    bounds = [(0.0, None)] + [(None, None)] * (PER - 1) + [(None, None)] * (2 * PER) + \
             [(0.0, None)] * (6 * K) + [(0.0, None)]
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds,
                  method="highs")
    if res.status != 0:
        return None, None
    w = res.x[0:nw]
    return float(res.fun), [w[j * PER:(j + 1) * PER].tolist() for j in range(3)]


def legal_grid(s, n=41):
    """fine grid in the containing box filtered by the full exact-core criterion."""
    out = []
    for xf in np.linspace(0, 1, n):
        for yf in np.linspace(0, 1, n):
            x = xf * (s + E0)
            y = yf * E0
            d = core_vals(s, x, y)
            if d["legal"] and (x + s) ** 2 + y * y <= (1 - U) ** 2 + 1e-12:
                out.append(d)
    return out


def pick(pts):
    """3 x-values x 3 y-values spread over the legal set + tight-boundary ones."""
    if not pts:
        return []
    xs = sorted(p["x"] for p in pts)
    ys = sorted(p["y"] for p in pts)
    take = []
    for xq in (0.10, 0.5, 0.9):
        for yq in (0.10, 0.5, 0.9):
            xt = xs[min(len(xs) - 1, int(xq * (len(xs) - 1)))]
            yt = ys[min(len(ys) - 1, int(yq * (len(ys) - 1)))]
            best = min(pts, key=lambda p: abs(p["x"] - xt) + abs(p["y"] - yt))
            if best not in take:
                take.append(best)
    tight = sorted(pts, key=lambda p: p["surplus"])[:2]
    for t in tight:
        if t not in take:
            take.append(t)
    return take


def main():
    ss = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35]
    t0 = time.time()
    res = dict(note="proposals only; every point passes the FULL exact-core numeric "
                    "criterion of lead/K10-HUB-LINE-CHART.md; criterion needs m*<0.1",
               layers=[])
    for s in ss:
        pts = legal_grid(s)
        sel = pick(pts)
        rows = []
        for p in sel:
            A, req = H.build(s, p["x"], p["y"], n_rho=20, n_phi=72)
            m, w = lp_normalised(A, req)
            rows.append(dict(x=round(p["x"], 6), y=round(p["y"], 6),
                             branch=p["branch"], core_lhs=p["core_lhs"],
                             core_rhs=p["core_rhs"], surplus=p["surplus"],
                             antipode_active=p.get("antipode_active", None),
                             m_star=m, criterion_ok=(m is not None and m < 0.1),
                             weights=w))
        # joint test: one weight triple at t = 0.1 for all selected samples
        blocks, reqs = [], []
        for p in sel:
            A, req = H.build(s, p["x"], p["y"], n_rho=20, n_phi=72)
            blocks.append(A)
            reqs.append(req)
        joint_ok = H.feasible_at_t(blocks, reqs, 0.1) if sel else None
        lo, hi = 0.02, 0.12
        for _ in range(12):
            mid = (lo + hi) / 2
            if H.feasible_at_t(blocks, reqs, mid):
                hi = mid
            else:
                lo = mid
        worst = max((r for r in rows if r["m_star"] is not None),
                    key=lambda r: r["m_star"], default=None)
        res["layers"].append(dict(s=s, n_legal=len(pts), n_sel=len(sel),
                                  joint_t_star=hi, joint_ok_at_0p1=joint_ok,
                                  rows=rows,
                                  worst=(None if worst is None else
                                         dict(x=worst["x"], y=worst["y"],
                                              m_star=worst["m_star"],
                                              branch=worst["branch"]))))
        print("s=%.2f legal=%4d sel=%d  joint_t*=%.5f(joint@0.1=%s)  worst=(x=%.4f,y=%.4f,branch=%s,m*=%.5f)  %.0fs"
              % (s, len(pts), len(sel), hi, joint_ok,
                 worst["x"], worst["y"], worst["branch"], worst["m_star"],
                 time.time() - t0), flush=True)
    json.dump(res, open(OUT / "hubline_proposals_v2.json", "w"), indent=1)
    print("saved evidence/hubline_proposals_v2.json  (%.0fs)" % (time.time() - t0))


if __name__ == "__main__":
    main()
