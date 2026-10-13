"""R20-C: calibration leg — evaluate the residual definitions at the SAVED genuine candidate.

The candidate (n11/upper/certified_object.json, remapped to the q0(6,7) span-4 graph by
lead/q0_exact_closure_radius.py) is an actual covering configuration with radius
R_cand = 0.3799838531... < 19/50.  All the equalities that the 29-factor dual dualizes
(vertex angle sums, shared side lengths, endpoint-radius copies, cyclic closure, total width)
must therefore have residual ~0 there, while the Delaunay slacks stay strictly positive.

This calibrates the residual definitions used in r20_residuals.py (same conventions).
Diagnostic only.
"""
import json, math
import numpy as np
from pathlib import Path

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
ROOT = HERE.parent.parent.parent
PI = math.pi


def main():
    o = json.loads((LEAD / 'q0_exact_closure_radius.json').read_text(encoding='utf-8'))
    x0 = np.array(o['x0']); faces = o['faces']; edges = [tuple(e) for e in o['edges']]
    Rcand = o['candidate_radius']
    R = 19 / 50                      # dual allowance used by certify_q0_closure.py
    ang = x0[:33].reshape(11, 3)
    bsw = x0[33:42]
    rho = np.exp(x0[42:62] + x0[62])          # absolute local radii (face0..10, switch0..8)
    yface = rho[:11] / R
    ysw = rho[11:20] / R
    y = ysw.copy()
    u = np.roll(y, 1); v = y
    alpha = np.zeros(9)
    alpha_raw = np.zeros(9)
    # alpha_i = pi - sum_{faces at i}(angle at i) + (b_{i-1}+b_i)   [lead q0_exact_closure_radius.py]
    for t, f in enumerate(faces):
        for k, i in enumerate(f):
            if i < 9: alpha_raw[i] += ang[t, k]
    alpha = PI - alpha_raw + np.roll(bsw, 1) + bsw
    q = (u - v) ** 2 + 4 * u * v * np.sin(alpha / 2) ** 2
    w = 2 * np.arcsin(np.clip(R * np.sqrt(q) / 2, 0, 1))
    qmin = 4 * math.sin(PI - 8 * math.asin(R)) ** 2 / R ** 2
    L = np.arctan2(v * np.sin(alpha), u - v * np.cos(alpha)); T = PI - alpha - L

    # --- residuals
    Rsite = np.zeros(9)
    for i in range(9): Rsite[i] = -PI
    Rhub = np.zeros(2)
    for t, f in enumerate(faces):
        for k, i in enumerate(f):
            if i < 9: Rsite[i] += ang[t, k]
            else: Rhub[i - 9] += ang[t, k]
    Rsite += alpha - np.roll(bsw, 1) - bsw
    Rhub -= 2 * PI
    adj = {e: [(t, next(vv for vv in f if vv not in e)) for t, f in enumerate(faces)
               if e[0] in f and e[1] in f] for e in edges}
    slack = np.zeros(21); m2 = np.zeros(21); m1 = np.zeros(21)
    for ei, e in enumerate(edges):
        ad = adj[e]; t2 = []; t1 = []; opp = []
        for k, (t, oppv) in enumerate(ad):
            mtx = faces[t].index(oppv); sgn = 1.0 if k == 0 else -1.0
            t2.append(sgn * yface[t] ** 2 * math.sin(ang[t, mtx]) ** 2)
            t1.append(sgn * yface[t] * math.sin(ang[t, mtx])); opp.append(ang[t, mtx])
        if len(ad) == 1:
            bi = next(b for b in range(9) if {b, (b + 1) % 9} == set(e))
            t2.append(-ysw[bi] ** 2 * math.sin(bsw[bi]) ** 2)
            t1.append(-ysw[bi] * math.sin(bsw[bi])); opp.append(bsw[bi])
        slack[ei] = PI - sum(opp); m2[ei] = sum(t2); m1[ei] = sum(t1)
    c2L = ysw[np.arange(9) - 1] ** 2 - u ** 2; c2R = ysw ** 2 - v ** 2
    c1L = ysw[np.arange(9) - 1] - u; c1R = ysw - v
    Gc = T + np.roll(L, -1) + 2 * bsw + (w + np.roll(w, -1)) / 2 - PI
    W = w.sum() - 2 * PI
    # shared side lengths from the two sides (sine law: side/2 = rho*sin(opposite angle))
    side_gap = []
    for ei, e in enumerate(edges):
        vals = []
        for (t, oppv) in adj[e]:
            vals.append(rho[t] * math.sin(ang[t, faces[t].index(oppv)]))
        if len(adj[e]) == 1:
            bi = next(b for b in range(9) if {b, (b + 1) % 9} == set(e))
            vals.append(rho[11 + bi] * math.sin(bsw[bi]))
        side_gap.append(vals[0] - vals[1])
    side_gap = np.array(side_gap)
    loggap = []
    for ei, e in enumerate(edges):
        vals = []
        for (t, oppv) in adj[e]:
            vals.append(math.log(rho[t]) + math.log(math.sin(ang[t, faces[t].index(oppv)])))
        if len(adj[e]) == 1:
            bi = next(b for b in range(9) if {b, (b + 1) % 9} == set(e))
            vals.append(math.log(rho[11 + bi]) + math.log(math.sin(bsw[bi])))
        loggap.append(vals[0] - vals[1])
    loggap = np.array(loggap)

    rep = dict(candidate_radius=float(Rcand), dual_R=R, qmin=float(qmin),
               q_min_actual=float(q.min()),
               max_abs_site=float(np.abs(Rsite).max()),
               max_abs_hub=float(np.abs(Rhub).max()),
               max_abs_closure=float(np.abs(Gc).max()),
               sum_w_minus_2pi=float(W),
               max_abs_copy2=float(max(np.abs(c2L).max(), np.abs(c2R).max())),
               max_abs_copy1=float(max(np.abs(c1L).max(), np.abs(c1R).max())),
               max_abs_match1=float(np.abs(m1).max()),
               max_abs_match2=float(np.abs(m2).max()),
               min_slack=float(slack.min()), max_slack=float(slack.max()),
               max_abs_side_gap=float(np.abs(side_gap).max()),
               max_abs_log_side_gap=float(np.abs(loggap).max()),
               yface_range=[float(yface.min()), float(yface.max())],
               ysw_range=[float(ysw.min()), float(ysw.max())])
    (HERE / 'r20_candidate_calibration.json').write_text(json.dumps(rep, indent=1))
    for k, vv in rep.items():
        print(f'{k:24s} {vv}')


if __name__ == '__main__':
    main()
