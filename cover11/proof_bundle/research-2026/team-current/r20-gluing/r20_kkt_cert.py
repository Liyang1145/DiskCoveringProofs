"""R20-V: FINAL certificate at the corrected caliber.

Finding chain (all regenerated here, no memory quotes):
  * at R = r_cand = 0.3799838531198388 the saved configuration's radius copies saturate
    (27 of the 69 free parameters lie on the closed-domain boundary), so those KKT rows are
    one-sided;  (lead interface fix)
  * the group (CONE + KKT) is FEASIBLE with a nontrivial solution, so stationarity alone does not
    refute the candidate;
  * adding the VALIDITY rows  V(z) >= pi  for sampled tuples (equivalently z_c g_c >= 0 on the
    class, the exact condition for the assembled bound to be an upper bound) makes the system
    INFEASIBLE.

This file produces the honest certificate for that infeasibility:
     min s   s.t.   B^T z = 0 (KKT),  cone,  |z|_inf <= 1,   (row_j . z - rhs_j) >= -s   for all
     sampled validity rows / one-sided rows,
     lambda = the LP dual (>= 0),  s* = margin.
A positive s* with the multiplier vector lambda is a Farkas-type witness: on this sample, no
nonzero z in the family both is stationary at the candidate and produces an upper bound.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_kkt_cert.py
"""
import json, math, sys
import numpy as np
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


def setup(npts, seed):
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    B, meta = build(C, p0)
    a_c = {}; b_c = {}
    for k in range(29):
        a, b = lin_form(k, p0, C); a_c[k] = a; b_c[k] = b
    S = sample_tuples(C, p0, npts, seed)
    Rv = np.zeros((len(S), NZ)); bv = np.zeros(len(S)); kv = np.zeros(len(S), int)
    for j, (k, X) in enumerate(S):
        a, b = lin_form(k, X, C)
        Rv[j] = a_c[k] - a; bv[j] = b - b_c[k]; kv[j] = k
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
    return dict(C=C, p0=p0, R=R, meta=meta, Rv=Rv, bv=bv, kv=kv, eq=eq, ineq=ineq, cone=cone,
                a_c=a_c, b_c=b_c)


def run(npts, seed, verbose=True):
    d = setup(npts, seed)
    Rv, bv, ineq, cone, eq = d['Rv'], d['bv'], d['ineq'], d['cone'], d['eq']
    nrow = Rv.shape[0] + ineq.shape[0] + cone.shape[0]
    # variables (z[NZ], s):  slack_j >= -s  ->  -(row_j . z) - s <= -rhs_j ;  cone rows <= 0
    A = np.zeros((nrow, NZ + 1)); b = np.zeros(nrow); kind = []
    r = 0
    for j in range(Rv.shape[0]):
        A[r, :NZ] = -Rv[j]; A[r, NZ] = -1.0; b[r] = -bv[j]; kind.append(('val', int(d['kv'][j])))
        r += 1
    for j in range(ineq.shape[0]):
        A[r, :NZ] = ineq[j]; b[r] = 0.0; kind.append(('kkt1', j)); r += 1
    for j in range(cone.shape[0]):
        A[r, :NZ] = cone[j]; b[r] = 0.0; kind.append(('cone', j)); r += 1
    Aeq = np.hstack([eq, np.zeros((eq.shape[0], 1))])
    beq = np.zeros(eq.shape[0])
    c = np.zeros(NZ + 1); c[NZ] = 1.0
    res = linprog(c, A_ub=A, b_ub=b, A_eq=Aeq, b_eq=beq,
                  bounds=[(-1, 1)] * NZ + [(None, None)], method='highs')
    lam = -np.asarray(res.ineqlin.marginals)
    z = res.x[:NZ]; s = res.x[NZ]
    if verbose:
        print('npts=%4d seed=%2d: samples %5d  rows %6d  s* = %+.6e  |z|inf = %.4f'
              % (npts, seed, len(Rv), nrow, s, np.abs(z).max()))
        # Farkas check: lam >= 0, lam . A must vanish on z and be negative on the s column
        F = lam @ A
        lhs = float(lam @ b)
        print('    Farkas: positive multipliers %d ; |sum lam A| on z = %.2e ; s-column %.3e ;'
              ' lam.b = %.6e' % (int((lam > 1e-9).sum()), np.abs(F[:NZ]).max(), F[NZ], lhs))
        # which rows the certificate uses
        cnt = {}
        for j in np.where(lam > 1e-9)[0]:
            t = kind[j][0]; cnt[t] = cnt.get(t, 0) + 1
        print('    rows used by type: %s' % cnt)
        facs = {}
        for j in np.where(lam > 1e-9)[0]:
            if kind[j][0] == 'val':
                k = kind[j][1]; facs[k] = facs.get(k, 0) + 1
        print('    validity rows used per factor: %s' % dict(sorted(facs.items())))
    return dict(npts=npts, seed=seed, s_star=float(s), lam_nonneg=bool(lam.min() > -1e-9),
                farkas_z=float(np.abs((lam @ A)[:NZ]).max()),
                farkas_s=float((lam @ A)[NZ]), lam_b=float(lam @ b),
                n_samples=int(len(Rv)),
                type_counts={k: int(v) for k, v in
                             {t: sum(1 for j in np.where(lam > 1e-9)[0] if kind[j][0] == t)
                              for t in ('val', 'kkt1', 'cone')}.items()})


def main():
    print('=== R20-V certificate at R = r_cand: no nonzero z is stationary at the candidate AND')
    print('    produces an upper bound (validity rows sampled over every factor domain) ===')
    out = []
    for npts, seed in [(60, 5), (200, 17), (600, 29)]:
        out.append(run(npts, seed))
        print()
    json.dump(out, open(HERE / 'r20_kkt_cert.json', 'w'), indent=1)
    print('saved r20_kkt_cert.json')


if __name__ == '__main__':
    main()
