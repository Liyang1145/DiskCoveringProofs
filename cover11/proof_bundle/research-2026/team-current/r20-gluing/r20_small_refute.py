"""R20-FINAL4: small, fully transparent refutation test (all numbers printed).

System (competitor-only, a SUPERSET of any sharp-support family, so a refutation here is
unconditional for the pure 121-column family):

    find z with    f_k(pi*; z) >= f_k(X; z)   for the sampled competitors X
    where          f_k(Y; z) = v_k(Y) + M_k(Y) . z       (linear in z)

Equivalently  G z >= h  with  G[j] = M_k(pi*) - M_k(X_j),  h[j] = v_k(X_j) - v_k(pi*).
The set {z : G z >= h} is a translate of a cone.  z = 0 is feasible iff h <= 0, i.e. iff the
candidate's primal value dominates every competitor's primal value; otherwise the cone is empty
unless it is a pointed cone with a feasible ray.  This file decides it SMALL: it prints the LP,
the margin, the dual multipliers, and checks the Farkas identity by hand on a handful of rows.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_small_refute.py
"""
import json, math, sys
import numpy as np
from pathlib import Path
from scipy.optimize import linprog

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
PI = math.pi
NZ = 121
R_CAND = 0.3799838531198388
sys.path.insert(0, str(HERE))
from r20_producer_family import load_candidate, value_and_row


def main():
    C = load_candidate(R_CAND); p0 = C['p']
    v0 = np.zeros(29); M0 = np.zeros((29, NZ))
    for k in range(29):
        v0[k], M0[k] = value_and_row(k, p0, C)

    # ---- pick the competitors that beat the SAVED dual and a few generic ones
    zc = np.array([float(f'{v:.9f}') for v in
                   json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])
    rng = np.random.default_rng(5)
    cand = []
    for k in range(29):
        for _ in range(300):
            X = p0.copy()
            if k < 11:
                a = rng.uniform(1e-6, PI); b = rng.uniform(1e-6, PI - a)
                X[3 * k:3 * k + 3] = (a, b, rng.uniform(0, 1))
            elif k < 20:
                X[33 + k - 11] = rng.uniform(1e-6, PI / 2)
                X[42 + k - 11] = rng.uniform(0, 1)
            else:
                i = k - 20
                X[51 + 3 * i:51 + 3 * i + 3] = (rng.uniform(1e-6, PI - 1e-6),
                                                rng.uniform(0, 1), rng.uniform(0, 1))
            v, M = value_and_row(k, X, C)
            slack = (v0[k] - v) + (M0[k] - M) @ zc
            if slack < -1e-5:
                cand.append((k, X, float(slack), float(v - v0[k]), M0[k] - M))
    print('=== R20-FINAL4: small transparent refutation test ===')
    print('candidate primal value sum v0 = %.12f' % v0.sum())
    print('competitors that beat the SAVED dual z_c825: %d' % len(cand))
    for k, X, sl, hv, G in cand[:6]:
        print('   factor %2d  slack(with z_c825) %+.3e  h = v_k(X)-v_k(pi*) = %+.3e' % (k, sl, hv))

    # ---- 1) does the candidate dominate all competitors AT z = 0?  (h <= 0 ?)
    hall = []
    for k in range(29):
        for _ in range(60):
            X = p0.copy()
            if k < 11:
                a = rng.uniform(1e-6, PI); b = rng.uniform(1e-6, PI - a)
                X[3 * k:3 * k + 3] = (a, b, rng.uniform(0, 1))
            elif k < 20:
                X[33 + k - 11] = rng.uniform(1e-6, PI / 2)
                X[42 + k - 11] = rng.uniform(0, 1)
            else:
                i = k - 20
                X[51 + 3 * i:51 + 3 * i + 3] = (rng.uniform(1e-6, PI - 1e-6),
                                                rng.uniform(0, 1), rng.uniform(0, 1))
            v, M = value_and_row(k, X, C)
            hall.append(float(v - v0[k]))
    hall = np.array(hall)
    print('over %d random competitors: max h = %+.6e, min h = %+.6e'
          % (len(hall), hall.max(), hall.min()))
    print('  -> if max h > 0, then z=0 is INFEASIBLE, so the cone has no obvious interior point')

    # ---- 2) the real LP on the beating competitors + generic sample
    rows = []
    for k, X, sl, hv, G in cand:
        rows.append((k, X))
    for k in range(29):
        for _ in range(4):
            X = p0.copy()
            if k < 11:
                a = rng.uniform(1e-6, PI); b = rng.uniform(1e-6, PI - a)
                X[3 * k:3 * k + 3] = (a, b, rng.uniform(0, 1))
            elif k < 20:
                X[33 + k - 11] = rng.uniform(1e-6, PI / 2)
                X[42 + k - 11] = rng.uniform(0, 1)
            else:
                i = k - 20
                X[51 + 3 * i:51 + 3 * i + 3] = (rng.uniform(1e-6, PI - 1e-6),
                                                rng.uniform(0, 1), rng.uniform(0, 1))
            rows.append((k, X))
    G = np.zeros((len(rows), NZ)); h = np.zeros(len(rows))
    for j, (k, X) in enumerate(rows):
        v, M = value_and_row(k, X, C)
        G[j] = M0[k] - M; h[j] = v - v0[k]
    print()
    print('small LP: %d rows, %d columns' % (len(rows), NZ))
    A = np.hstack([-G, -np.ones((len(rows), 1))])
    b = -h
    c = np.zeros(NZ + 1); c[NZ] = 1.0
    res = linprog(c, A_ub=A, b_ub=b, bounds=[(-1, 1)] * NZ + [(None, None)], method='highs')
    print('   status %d  margin (min over z of max violation) = %+.6e' % (res.status, res.fun))
    lam = -np.asarray(res.ineqlin.marginals)
    print('   dual multipliers: min %+.3e max %+.3e ; count > 1e-9: %d'
          % (lam.min(), lam.max(), int((lam > 1e-9).sum())))
    # Farkas check by hand
    F = lam @ A
    print('   sum lam_j A_j  (must vanish on z for a valid Farkas vector): max |.| on z = %.3e'
          % np.abs(F[:NZ]).max())
    print('   lam . b = %+.6e   (positive with A-lambda = 0 gives a contradiction)'
          % float(lam @ b))
    # which rows matter
    idx = np.where(lam > 1e-9)[0]
    print('   rows used: %s' % [int(j) for j in idx[:12]])
    for j in idx[:8]:
        print('      row %3d factor %2d  lam %.6f   h %+.6e' % (j, rows[j][0], lam[j], h[j]))


if __name__ == '__main__':
    main()
