"""R20-U: differential diagnosis + Farkas certificate at the correct caliber.

Question: of the three ingredient groups
   (CONE)  z[0:11] <= 0, z[50:71] >= 0, z[112:121] >= 0
   (KKT)   42 two-sided rows (interior parameters) + 27 one-sided rows (the active radius copies)
   (VAL)   validity rows  f_k(pi^*;z) >= f_k(X;z)  sampled in every factor's own domain
which group causes the infeasibility of {z != 0} — and what is the exact Farkas certificate?

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_kkt_diag.py
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
from r20_kkt_lp import load_candidate, lin_form, const_of
from r20_kkt_active import build
from r20_kkt_lp_final import sample_tuples


def setup(npts=60, seed=5):
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    B, meta = build(C, p0)
    a_c = {}; b_c = {}
    for k in range(29):
        a, b = lin_form(k, p0, C); a_c[k] = a; b_c[k] = b
    S = sample_tuples(C, p0, npts, seed)
    Rv = np.zeros((len(S), NZ)); bv = np.zeros(len(S))
    for j, (k, X) in enumerate(S):
        a, b = lin_form(k, X, C)
        Rv[j] = a_c[k] - a; bv[j] = b - b_c[k]
    eq = []; ineq = []
    for m in meta:
        if m['activity'] == 'in':
            eq.append(B[m['q']])
        elif m['activity'] == 'lo':
            ineq.append(-B[m['q']])
        else:
            ineq.append(B[m['q']])
    eq = np.array(eq); ineq = np.array(ineq)
    cone = []
    for i in range(11):
        r = np.zeros(NZ); r[i] = 1.0; cone.append(r)
    for i in range(21):
        r = np.zeros(NZ); r[KAP + i] = -1.0; cone.append(r)
    for i in range(9):
        r = np.zeros(NZ); r[CL + i] = -1.0; cone.append(r)
    cone = np.array(cone)
    return dict(C=C, p0=p0, R=R, B=B, meta=meta, a_c=a_c, b_c=b_c, Rv=Rv, bv=bv,
                eq=eq, ineq=ineq, cone=cone)


def feas(d, use_cone=True, use_kkt=True, use_val=True, idx=112):
    A_ub = []; b_ub = []
    if use_cone:
        A_ub.append(d['cone']); b_ub.append(np.zeros(d['cone'].shape[0]))
    if use_kkt:
        A_ub.append(d['ineq']); b_ub.append(np.zeros(d['ineq'].shape[0]))
    if use_val:
        A_ub.append(d['Rv']); b_ub.append(d['bv'])
    A_ub = np.vstack(A_ub) if A_ub else np.zeros((0, NZ))
    b_ub = np.concatenate([np.asarray(x, float).ravel() for x in b_ub]) if b_ub else np.zeros(0)
    A_eq = np.vstack([d['eq'], np.eye(1, NZ, idx)]) if use_kkt else np.eye(1, NZ, idx)
    b_eq = np.r_[np.zeros(d['eq'].shape[0]), 1.0] if use_kkt else np.r_[1.0]
    res = linprog(np.zeros(NZ), A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                  bounds=[(-20, 20)] * NZ, method='highs')
    return res


def farkas(d, idx=112, scale=1e7, thr=1e-8):
    """Farkas certificate for the full system (cone + kkt + validity)."""
    A_ub = np.vstack([d['cone'], d['ineq'], d['Rv']])
    b_ub = np.r_[np.zeros(d['cone'].shape[0] + d['ineq'].shape[0]), d['bv']]
    A_eq = np.vstack([d['eq'], np.eye(1, NZ, idx)])
    b_eq = np.r_[np.zeros(d['eq'].shape[0]), 1.0]
    # find a direction in the cone of the (A_ub, A_eq) system proving emptiness:
    # solve the aux LP  min s  s.t.  A_ub z <= b_ub + s,  A_eq z = b_eq, |z| <= 20
    nv = NZ + 1
    Aub = np.hstack([A_ub, -np.ones((A_ub.shape[0], 1))])
    Aeq = np.hstack([A_eq, np.zeros((A_eq.shape[0], 1))])
    c = np.zeros(nv); c[NZ] = 1.0
    res = linprog(c, A_ub=Aub, b_ub=b_ub, A_eq=Aeq, b_eq=b_eq,
                  bounds=[(-20, 20)] * NZ + [(None, None)], method='highs')
    return res


def main():
    d = setup(60, 5)
    print('=== differential diagnosis (normalisation z[112] = 1) ===')
    for tag, kw in [('CONE+KKT only        ', dict(use_cone=True, use_kkt=True, use_val=False)),
                    ('CONE+VAL only        ', dict(use_cone=True, use_kkt=False, use_val=True)),
                    ('KKT+VAL only         ', dict(use_cone=False, use_kkt=True, use_val=True)),
                    ('CONE+KKT+VAL         ', dict(use_cone=True, use_kkt=True, use_val=True)),
                    ('CONE+KKT+wider bounds', dict(use_cone=True, use_kkt=True, use_val=True))]:
        res = feas(d, **kw)
        print('   %-22s -> %s' % (tag, 'FEASIBLE' if res.status == 0 else 'INFEASIBLE'))
    print()
    print('=== Farkas certificate for CONE+KKT+VAL ===')
    res = farkas(d)
    print('   aux LP (min max-violation): status %d, value %.6e' % (res.status, res.fun))
    if res.status == 0:
        lam = -np.asarray(res.ineqlin.marginals)
        # verify: sum lam_j A_j must be 0 on z-columns and the s-column coefficient negative
        A_ub = np.vstack([d['cone'], d['ineq'], d['Rv']])
        F = lam @ A_ub
        print('   certificate rows used: %d ; |sum lam A|_inf on z = %.3e ; lam.b = %.6e'
              % (int((lam > 1e-8).sum()), np.abs(F).max(), float(lam @ np.r_[
                  np.zeros(d['cone'].shape[0] + d['ineq'].shape[0]), d['bv']])))
    # store
    json.dump(dict(diag={t: int(feas(d, **kw).status) for t, kw in
                        [('cone_kkt', dict(use_cone=True, use_kkt=True, use_val=False)),
                         ('cone_val', dict(use_cone=True, use_kkt=False, use_val=True)),
                         ('kkt_val', dict(use_cone=False, use_kkt=True, use_val=True)),
                         ('all', dict(use_cone=True, use_kkt=True, use_val=True))]}),
              open(HERE / 'r20_kkt_diag.json', 'w'), indent=1)
    print('   saved r20_kkt_diag.json')


if __name__ == '__main__':
    main()
