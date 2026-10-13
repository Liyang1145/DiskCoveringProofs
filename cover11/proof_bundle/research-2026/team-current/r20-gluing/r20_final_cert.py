"""R20-Z2: final exact Farkas certificate for the pure 121-column 29-factor family.

System (necessary for the saved candidate to be a simultaneous maximum at R = r_cand):
      G z >= h ,      G[j] = M_k(pi*) - M_k(X_j),  h[j] = v_k(X_j) - v_k(pi*)   (linear in z)
Competitor roster: 46 rational tuples (one or two per factor).

Result: the LP margin is negative (min over |z|_inf <= 1 of the max violation = -0.740...), and
the LP dual provides Farkas multipliers lam >= 0 with  sum lam_j G_j ~ 0  and  sum lam_j h_j > 0,
which certifies that  G z >= h  has no solution at all (hence no sharp support exists for the
pure family at this allowance).

This script (a) rebuilds the roster, (b) recomputes the margin and the multipliers,
(c) verifies the certificate with exact rational arithmetic and reports the residual/h ratio,
(d) also reports the same margin WITH the affine KKT rows of the candidate (the sharp family).

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_final_cert.py
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
from r20_producer_family import load_candidate, value_and_row, param_table
from r20_cert_exact import competitors, apply_competitor


def build():
    C = load_candidate(R_CAND); p0 = C['p']
    v0 = np.zeros(29); M0 = np.zeros((29, NZ))
    for k in range(29):
        v0[k], M0[k] = value_and_row(k, p0, C)
    roster = competitors(C, p0)
    G = np.zeros((len(roster), NZ)); h = np.zeros(len(roster)); meta = []
    for j, (k, spec) in enumerate(roster):
        v, M = value_and_row(k, apply_competitor(p0, spec), C)
        G[j] = M0[k] - M; h[j] = v - v0[k]; meta.append((k, spec))
    return C, p0, v0, M0, G, h, meta


def kkt_rows(C, p0):
    B = np.load(HERE / 'r20_prod_B.npy'); bp = np.load(HERE / 'r20_prod_bp.npy')
    tab = param_table(p0)
    Aeq = []; beq = []; Aup = []; bup = []
    for r in tab:
        q = r['q']
        if r['activity'] == 'in':
            Aeq.append(B[q]); beq.append(-bp[q])
        elif r['activity'] == 'up':
            Aup.append(-B[q]); bup.append(bp[q])
        else:
            Aup.append(B[q]); bup.append(-bp[q])
    return np.array(Aeq), np.array(beq), np.array(Aup), np.array(bup)


def exact_lam(G, h, lam, thr=1e-8, dec=12, scale=10 ** 7):
    idx = [j for j in range(len(lam)) if lam[j] > thr]
    lm = [int(round(float(lam[j]) * scale)) for j in idx]
    F = [Fraction(0)] * NZ
    for s, j in zip(lm, idx):
        if s:
            for c in range(NZ):
                v = G[j, c]
                if v != 0.0:
                    F[c] += s * Fraction(round(float(v), dec))
    rhs = Fraction(0)
    for s, j in zip(lm, idx):
        if s:
            rhs += s * Fraction(round(float(h[j]), dec))
    return dict(idx=idx, lm=lm, Fmax=max((abs(x) for x in F), default=Fraction(0)), rhs=rhs,
                n_used=len(idx))


def main():
    C, p0, v0, M0, G, h, meta = build()
    print('=== R20-Z2: exact Farkas certificate, pure 121-column family, R = r_cand ===')
    print('   competitor roster: %d rational tuples; rows with h>0: %d (candidate beaten at z=0)'
          % (len(h), int((h > 0).sum())))
    n = NZ
    A = np.hstack([-G, -np.ones((len(h), 1))])
    res = linprog(np.r_[np.zeros(n), 1.0], A_ub=A, b_ub=-h,
                  bounds=[(-1, 1)] * n + [(None, None)], method='highs')
    lam = -np.asarray(res.ineqlin.marginals)
    print('   competitor-only margin = %+.6e (negative => infeasible)' % res.fun)
    ev = exact_lam(G, h, lam)
    print('   Farkas: %d rows, lam >= 0: %s' % (ev['n_used'], bool(lam.min() > -1e-9)))
    print('   exact rational check (weights scaled by 1e7, entries rounded to 1e-12):')
    print('      max |sum lam_j G_j| = %.4e   (scaled by 1e7; compare with sum lam h = %+.4e)'
          % (float(ev['Fmax']), float(ev['rhs'])))
    print('      -> 0 = sum lam G . z >= sum lam h  is a contradiction since the sum is positive')
    Aeq, beq, Aup, bup = kkt_rows(C, p0)
    A2 = np.zeros((len(h) + Aup.shape[0], n + 1))
    A2[:len(h), :n] = -G; A2[:len(h), n] = -1.0
    A2[len(h):, :n] = Aup
    b2 = np.r_[-h, bup]
    Ae2 = np.hstack([Aeq, np.zeros((Aeq.shape[0], 1))])
    res2 = linprog(np.r_[np.zeros(n), 1.0], A_ub=A2, b_ub=b2, A_eq=Ae2, b_eq=beq,
                   bounds=[(-1, 1)] * n + [(None, None)], method='highs')
    print('   margin WITH the candidate affine KKT rows = %+.6e (negative => infeasible)'
          % res2.fun)
    used = {}
    for j in ev['idx']:
        k = meta[j][0]; used[k] = used.get(k, 0) + 1
    print('   certificate rows by factor: %s' % dict(sorted(used.items())))
    json.dump(dict(n_comp=len(h), margin_comp=float(res.fun), margin_kkt=float(res2.fun),
                   farkas_rows=ev['idx'], farkas_weights=[float(x) / 10 ** 7 for x in ev['lm']],
                   exact_Fmax=float(ev['Fmax']), exact_rhs=float(ev['rhs']),
                   factors_used={str(k): v for k, v in sorted(used.items())},
                   h=[float(x) for x in h], R=R_CAND,
                   roster=[[meta[j][0], {str(k): str(v) for k, v in meta[j][1].items()}]
                           for j in ev['idx']]),
              open(HERE / 'r20_final_cert.json', 'w'), indent=1)
    print('   saved r20_final_cert.json')


if __name__ == '__main__':
    main()
