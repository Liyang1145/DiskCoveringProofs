"""R20-CERT: final exact certificate attempt — rational competitors, exact rational Farkas.

Statement tested (necessary and sufficient for the candidate to be a simultaneous maximum of the
pure 121-column 29-factor family at R = r_cand):

    exists z :  f_k(pi*; z) >= f_k(X; z)      for every sampled competitor X of every factor,
    f_k(Y;z) = v_k(Y) + M_k(Y).z  (linear in z).

A Farkas witness (lam >= 0,  sum lam_j G_j = 0,  sum lam_j h_j > 0) proves the sampled system has
no solution; it is verified with exact Fractions on rational competitor tuples so the result does
not depend on floating point.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_cert_exact.py
"""
import json, math, sys
import numpy as np
from fractions import Fraction
from pathlib import Path
from scipy.optimize import linprog

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
PI = math.pi
NZ = 121
R_CAND = 0.3799838531198388
sys.path.insert(0, str(HERE))
from r20_producer_family import load_candidate, value_and_row


def competitors(C, p0):
    """a fixed roster of RATIONAL competitor tuples (a, b, y) or (b, y) or (alpha, u, v)."""
    R = 0.38
    roster = []
    faces = [(1, Fraction(1), Fraction(1), Fraction(9, 10)),
             (2, Fraction(3, 4), Fraction(7, 5), Fraction(4, 5)),
             (3, Fraction(7, 8), Fraction(4, 3), Fraction(19, 20)),
             (4, Fraction(3, 5), Fraction(6, 5), Fraction(3, 5)),
             (5, Fraction(4, 5), Fraction(9, 8), Fraction(1, 2)),
             (6, Fraction(5, 6), Fraction(7, 5), Fraction(2, 3)),
             (7, Fraction(9, 10), Fraction(6, 5), Fraction(3, 4)),
             (8, Fraction(3, 4), Fraction(5, 4), Fraction(4, 5)),
             (9, Fraction(5, 4), Fraction(6, 5), Fraction(9, 10)),
             (10, Fraction(5, 4), Fraction(6, 5), Fraction(1, 2))]
    for k, a, b, y in faces:
        roster.append((k, {3 * k: a, 3 * k + 1: b, 3 * k + 2: y}))
    for i in range(9):
        roster.append((11 + i, {33 + i: Fraction(1, 2) + Fraction(i, 25),
                                42 + i: Fraction(1, 2) + Fraction(i, 40)}))
        roster.append((11 + i, {33 + i: Fraction(19, 20), 42 + i: Fraction(3, 4)}))
    for i in range(9):
        base = {51 + 3 * i: Fraction(1) + Fraction(i, 50),
                51 + 3 * i + 1: Fraction(1, 2) + Fraction(i, 50),
                51 + 3 * i + 2: Fraction(2, 3) + Fraction(i, 60)}
        roster.append((20 + i, base))
        roster.append((20 + i, {51 + 3 * i: Fraction(5, 4),
                                51 + 3 * i + 1: Fraction(19, 20),
                                51 + 3 * i + 2: Fraction(9, 10)}))
    return roster


def apply_competitor(p0, spec):
    X = p0.copy()
    for j, f in spec.items():
        X[j] = float(f)
    return X


def main():
    C = load_candidate(R_CAND); p0 = C['p']
    v0 = np.zeros(29); M0 = np.zeros((29, NZ))
    for k in range(29):
        v0[k], M0[k] = value_and_row(k, p0, C)
    roster = competitors(C, p0)
    G = np.zeros((len(roster), NZ)); h = np.zeros(len(roster)); meta = []
    for j, (k, spec) in enumerate(roster):
        X = apply_competitor(p0, spec)
        v, M = value_and_row(k, X, C)
        G[j] = M0[k] - M; h[j] = v - v0[k]; meta.append((k, spec))
    print('=== R20-CERT: %d rational competitors ===' % len(roster))
    print('   rows with h > 0 (the competitor emits more primal value than the candidate): %d'
          % int((h > 0).sum()))
    for j in np.where(h > 0)[0]:
        print('      row %2d factor %2d h = %+.6e' % (j, meta[j][0], h[j]))
    # exact Farkas LP:  lam >= 0, G^T lam = 0, h.lam = 1
    Aeq = np.vstack([G.T, h[None, :]])
    beq = np.r_[np.zeros(NZ), 1.0]
    res = linprog(np.zeros(len(roster)), A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * len(roster),
                  method='highs')
    print('   Farkas LP (lam>=0, sum lam G = 0, sum lam h = 1): %s'
          % ('FEASIBLE' if res.status == 0 else 'INFEASIBLE'))
    if res.status == 0:
        lam = res.x
        # exact check with Fractions
        lm = [Fraction(round(float(x), 9)).limit_denominator(10 ** 6) for x in lam]
        F = [Fraction(0)] * NZ
        for s, j in zip(lm, lam):
            pass
        F = [Fraction(0)] * NZ
        for s, j in zip(lm, range(len(lm))):
            if s:
                for c in range(NZ):
                    if G[j, c] != 0.0:
                        F[c] += s * Fraction(round(float(G[j, c]), 9))
        rhs = sum(s * Fraction(round(float(h[j]), 9)) for s, j in zip(lm, range(len(lm))))
        print('   exact (Fractions): max |sum lam G| = %s ;  sum lam h = %s'
              % (max(abs(x) for x in F), rhs))
        print('   => certificate: %d rows, weights %s'
              % (int(sum(1 for x in lm if x > 0)),
                 [str(x) for x in lm if x > 0][:8]))
        json.dump(dict(roster=[[m[0], {str(k): str(v) for k, v in m[1].items()}] for m in meta],
                       lam=[str(x) for x in lm], G=G.tolist(), h=h.tolist(),
                       exact_Fmax=str(max(abs(x) for x in F)), exact_rhs=str(rhs), R=R_CAND),
                  open(HERE / 'r20_cert_exact.json', 'w'), indent=1)
        print('   saved r20_cert_exact.json')
    else:
        print('   no Farkas witness from this roster; the system may be feasible')
        zslack = linprog(np.zeros(NZ), A_ub=-G, b_ub=-h, bounds=[(-5, 5)] * NZ, method='highs')
        print('   feasibility LP: %s' % ('FEASIBLE' if zslack.status == 0 else 'INFEASIBLE'))


if __name__ == '__main__':
    main()
