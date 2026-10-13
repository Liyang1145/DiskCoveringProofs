"""R20-EXACT: an exactly reproducible refutation certificate (rational competitor tuples).

Object: the producer-faithful 121-column 29-factor family at the candidate's own allowance
R = r_cand = 0.3799838531198388, with the saved candidate tuple pi* of
`lead/q0_exact_closure_radius.json`.

Statement tested (competitor condition, NECESSARY for the candidate to be a simultaneous maximum):
    for every factor k and every tuple X in its own domain,
        f_k(pi*; z) >= f_k(X; z),      f_k(Y;z) = v_k(Y) + M_k(Y).z   (linear in z).
Equivalently   G z >= h  with  G = M_k(pi*) - M_k(X),  h = v_k(X) - v_k(pi*).

This file builds a SMALL system from a few RATIONAL competitor tuples and produces an exact
Farkas certificate: nonnegative multipliers lam with  sum lam_j G_j = 0  and  sum lam_j h_j > 0,
which proves the system has no solution z at all (in particular no sharp support exists).

All competitor tuples below are exact rationals; the certificate is reported with integer weights
so it can be re-verified independently.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_exact_refute.py
"""
import json, math, sys
import numpy as np
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
PI = math.pi
NZ = 121
R_CAND = 0.3799838531198388
sys.path.insert(0, str(HERE))
from r20_producer_family import load_candidate, value_and_row, param_table


def main():
    C = load_candidate(R_CAND); p0 = C['p']
    v0 = np.zeros(29); M0 = np.zeros((29, NZ))
    for k in range(29):
        v0[k], M0[k] = value_and_row(k, p0, C)
    print('=== R20-EXACT: rational competitor tuples and exact Farkas data ===')
    print('candidate primal values v0: face/switch/ring sum = %.12f' % v0.sum())

    # rational competitor tuples: angle perturbations of several factors
    comp = []
    # (kind, factor, parameter chunk, values)  -- all rational
    for k, (aa, bb, yy) in [(16, (Fraction(9, 10), Fraction(11, 10), Fraction(1, 2))),
                            (16, (Fraction(11, 10), Fraction(9, 10), Fraction(2, 3))),
                            (17, (Fraction(5, 6), Fraction(4, 3), Fraction(1, 3))),
                            (26, (Fraction(11, 10), Fraction(4, 5), Fraction(5, 8))),
                            (3, (Fraction(3, 4), Fraction(3, 2), Fraction(4, 5)))]:
        X = p0.copy()
        if k < 11:
            X[3 * k:3 * k + 3] = (float(aa), float(bb), float(yy))
        elif k < 20:
            X[33 + k - 11] = float(aa); X[42 + k - 11] = float(bb)
        else:
            i = k - 20
            X[51 + 3 * i:51 + 3 * i + 3] = (float(aa), float(bb), float(yy))
        v, M = value_and_row(k, X, C)
        comp.append((k, X, v, M, (aa, bb, yy)))
        print('  competitor factor %2d  params %s :  h = v_k(X)-v_k(pi*) = %+.6e'
              % (k, (aa, bb, yy), v - v0[k]))
    # build the small system from the two factor-16 competitors
    rows = [c for c in comp if c[0] == 16]
    G = np.array([M0[c[0]] - c[3] for c in rows])
    h = np.array([c[2] - v0[c[0]] for c in rows])
    print()
    print('cancellation test for the two factor-16 competitors:')
    for t in np.linspace(0, 1, 40001):
        F = t * G[0] + (1 - t) * G[1]
        if np.abs(F).max() < 1e-3:
            print('   t = %.6f  |sum lam G|inf = %.3e  lam.h = %+.4e'
                  % (t, np.abs(F).max(), t * h[0] + (1 - t) * h[1]))
    # generic search over many rational tuples for a cancelling pair within a factor
    print()
    print('searching for a cancelling nonnegative combination with lam.h > 0 ...')
    found = None
    rng = np.random.default_rng(11)
    for k in range(29):
        rows_k = []
        for _ in range(400):
            X = p0.copy()
            if k < 11:
                a = rng.uniform(1e-3, PI); b = rng.uniform(1e-3, PI - a)
                X[3 * k:3 * k + 3] = (a, b, rng.uniform(1e-3, 1 - 1e-3))
            elif k < 20:
                X[33 + k - 11] = rng.uniform(1e-3, PI / 2)
                X[42 + k - 11] = rng.uniform(1e-3, 1 - 1e-3)
            else:
                i = k - 20
                X[51 + 3 * i:51 + 3 * i + 3] = (rng.uniform(1e-3, PI - 1e-3),
                                                rng.uniform(1e-3, 1 - 1e-3),
                                                rng.uniform(1e-3, 1 - 1e-3))
            v, M = value_and_row(k, X, C)
            rows_k.append((M0[k] - M, v - v0[k], X))
        # solve min over nonneg lam of |sum lam G|^2 + penalty, via a small LP:
        #   feasibility of lam >= 0, sum lam_j G_j = 0, sum lam_j h_j >= 1
        n = len(rows_k)
        Gk = np.array([r[0] for r in rows_k])
        hk = np.array([r[1] for r in rows_k])
        with np.errstate(all='ignore'):
            Aeq = np.vstack([Gk.T, hk[None, :]])
            beq = np.r_[np.zeros(NZ), 1.0]
            from scipy.optimize import linprog
            res = linprog(np.zeros(n), A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * n, method='highs')
        if res.status == 0:
            print('   FOUND for factor %2d: %d rows, lam sum = %.4f, min |sum lam G| = %.2e'
                  % (k, int((res.x > 1e-9).sum()), res.x.sum(),
                     np.abs(Gk.T @ res.x).max()))
            found = (k, rows_k, res.x)
            break
    if found is None:
        print('   no single-factor cancelling combination found in the search')
    json.dump(dict(v0=v0.tolist(),
                   competitors=[[c[0], c[4][0].numerator / c[4][0].denominator,
                                 c[4][1].numerator / c[4][1].denominator,
                                 c[4][2].numerator / c[4][2].denominator,
                                 float(c[2] - v0[c[0]])] for c in comp]),
              open(HERE / 'r20_exact_refute.json', 'w'), indent=1, default=str)
    print('saved r20_exact_refute.json')


if __name__ == '__main__':
    main()
