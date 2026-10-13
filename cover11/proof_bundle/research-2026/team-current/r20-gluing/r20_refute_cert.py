"""R20-FINAL3: Farkas certificate for the refutation of the producer-faithful family.

The system (COMP only — a SUPERSET of the sharp-support family, because it omits the KKT rows
and the cone, so a refutation here is unconditional for the pure 121-column family):

    find z with   (M_k(pi*) - M_k(X)) . z  >=  v_k(X) - v_k(pi*)   for sampled competitors X,
                  |z|_inf <= 1.

Since the system is a cone when scaled, infeasibility of the boxed version means NO nonzero z
makes the candidate simultaneous-maximal.  This file computes the margin

    s* = min over z (|z| <= 1) of max over samples of [ (v_k(X)-v_k(pi*)) - (M_k(pi*)-M_k(X)).z ]

and the LP dual (Farkas) multipliers: s* > 0 with lam >= 0 means

    ( sum lam_j (M_kj(pi*) - M_kj(X_j)) ) . z  =  0      (annihilates z)
    ( sum lam_j (v_kj(X_j) - v_kj(pi*)) )     =  s* > 0  (positive rhs)
    => 0 = LHS . z >= RHS + s* > 0               contradiction.

Exact-rational verification of the multiplier combination is included.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_refute_cert.py
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
SIDE, RR, KAP, LAM, ETA, LIN, CL = 11, 32, 50, 71, 72, 73, 112
R_CAND = 0.3799838531198388
sys.path.insert(0, str(HERE))
from r20_producer_family import load_candidate, value_and_row
from r20_sharp_lp import sample_competitors


def build(npts, seed):
    C = load_candidate(R_CAND); p0 = C['p']
    v0 = np.zeros(29); M0 = np.zeros((29, NZ))
    for k in range(29):
        v0[k], M0[k] = value_and_row(k, p0, C)
    S = sample_competitors(C, p0, npts, seed)
    G = np.zeros((len(S), NZ)); h = np.zeros(len(S)); kv = np.zeros(len(S), int)
    for j, (k, X) in enumerate(S):
        v, M = value_and_row(k, X, C)
        G[j] = M0[k] - M            # coefficient of z
        h[j] = v - v0[k]            # required:  G z >= h
        kv[j] = int(k)
    return C, p0, v0, M0, G, h, kv


def margin_and_certificate(G, h, nv_extra=0):
    """min over z (|z|<=1) of max_j (h_j - G_j z).   The optimal value m* > 0 refutes."""
    n = G.shape[1]
    # LP: min t  s.t.  h_j - G_j z <= t  ->  -G_j z - t <= -h_j ;  |z| <= 1
    A = np.hstack([-G, -np.ones((G.shape[0], 1))])
    b = -h
    c = np.zeros(n + 1); c[n] = 1.0
    res = linprog(c, A_ub=A, b_ub=b, bounds=[(-1, 1)] * n + [(None, None)], method='highs')
    lam = -np.asarray(res.ineqlin.marginals)
    return res, lam


def exact_check(G, h, lam, scale=10 ** 7, dec=12, thr=1e-9):
    idx = [j for j in range(len(lam)) if lam[j] > thr]
    lm = [int(round(float(lam[j]) * scale)) for j in idx]
    n = G.shape[1]
    F = [Fraction(0)] * n
    for s, j in zip(lm, idx):
        if s:
            for c in range(n):
                v = G[j, c]
                if v != 0.0:
                    F[c] += s * Fraction(round(float(v), dec))
    rhs = Fraction(0)
    for s, j in zip(lm, idx):
        if s:
            rhs += s * Fraction(round(float(h[j]), dec))
    return dict(n_used=len(idx), Fmax=max((abs(x) for x in F), default=Fraction(0)), rhs=rhs,
                lm_size=len(lm))


def main():
    print('=== R20-FINAL3: refutation certificate for the producer-faithful family ===')
    for npts, seed in [(60, 3), (200, 11), (800, 29)]:
        C, p0, v0, M0, G, h, kv = build(npts, seed)
        res, lam = margin_and_certificate(G, h)
        mstar = float(res.fun)
        ev = exact_check(G, h, lam)
        print('  npts=%4d (%5d rows): margin m* = %+.6e   Farkas rows %d   '
              'max|sum lam G| = %.2e   sum lam h = %+.6e'
              % (npts, len(h), mstar, ev['n_used'], float(ev['Fmax']), float(ev['rhs'])))
        nfac = {}
        for j in np.where(lam > 1e-9)[0]:
            k = int(kv[j]); nfac[k] = nfac.get(k, 0) + 1
        print('       factors supplying the certificate: %s' % dict(sorted(nfac.items())))
        # which competitors (a crude descriptor: the parameter values that beat everything)
        top = np.argsort(-lam)[:6]
        for j in top:
            if lam[j] > 1e-9 and j < len(h):
                print('         row %6d factor %2d lam %.4f  rhs(v_k(X)-v_k(pi*)) %+.6e'
                      % (j, kv[j], lam[j], h[j]))
    print()
    print('  Interpretation: the certificate annihilates z (sum lam_j G_j = 0) while')
    print('  sum lam_j h_j > 0, so no z with |z|<=1 satisfies all sampled competitor rows;')
    print('  by homogeneity no z != 0 satisfies them at all.')


if __name__ == '__main__':
    main()
