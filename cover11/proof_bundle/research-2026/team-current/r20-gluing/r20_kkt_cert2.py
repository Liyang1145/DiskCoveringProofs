"""R20-Y: FINAL certificate with the corrected (affine) stationarity instrument.

Chain of results at the candidate's own allowance R = r_cand = 0.3799838531198388:

  A. Caliber (lead fix): at R = r_cand the saved configuration's radius copies saturate, so
     27 of the 69 parameter rows are ONE-SIDED.  At R = 19/50 they would not be, and a strict
     cover exists there, so no sharp-area support is expected at 19/50.
  B. Affine stationarity (lead fix 2): f_k(pi;z) = b_k(pi) + a_k(pi).z, so the necessary condition
     is  b'_k + a'_k.z = 0  (interior) and, at the upper end of a closed domain,
     b'_k + a'_k.z >= 0  (inward = decreasing).  The homogeneous version (a'_k.z = 0) and the
     reversed boundary signs are both wrong; both are calibrated on toys in r20_toy_calibration.
  C. Complementarity: the Delaunay slack (kappa), eta and the non-tight radius copies are not
     tight at the candidate, so for V(z;pi*) = pi their multipliers must vanish.
  D. The corrected system (affine KKT + complementarity + cone) is FEASIBLE and gives
     V(z;pi*) = pi exactly.
  E. Adding the VALIDITY rows (V(z) >= pi on sampled tuples of every factor domain, i.e. the
     exact condition that z is a valid upper bound at R = r_cand) makes it INFEASIBLE on every
     sample size tried.

This file computes the certificate for (E): the optimal margin s* of the LP
     max s   s.t.  affine KKT, complementarity, cone, |z|_inf <= 1,
                   sampled validity/one-sided rows slack >= s
and reports the LP dual multipliers as the Farkas-type witness, with row provenance.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_kkt_cert2.py
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
from r20_kkt_lp_final import sample_tuples
from r20_kkt_affine import param_rows


def setup(npts, seed):
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    rows = param_rows(C, p0)
    a_c = {}; b_c = {}
    for k in range(29):
        a, b = lin_form(k, p0, C); a_c[k] = a; b_c[k] = b
    S = sample_tuples(C, p0, npts, seed)
    Rv = np.zeros((len(S), NZ)); bv = np.zeros(len(S)); kv = np.zeros(len(S), int)
    for j, (k, X) in enumerate(S):
        a, b = lin_form(k, X, C)
        Rv[j] = a_c[k] - a; bv[j] = b - b_c[k]; kv[j] = int(k)
    return dict(C=C, p0=p0, R=R, rows=rows, Rv=Rv, bv=bv, kv=kv, a_c=a_c, b_c=b_c)


def build_LP(d):
    rows = d['rows']; NZl = NZ
    A_eq = []; b_eq = []; A_ub = []; b_ub = []; prov = []
    for r in rows:
        if r['activity'] == 'in':
            A_eq.append(r['a_prime']); b_eq.append(-r['b_prime']); prov.append(('eq', r['name']))
        elif r['activity'] == 'lo':
            A_ub.append(r['a_prime']); b_ub.append(-r['b_prime']); prov.append(('lo', r['name']))
        else:
            A_ub.append(-r['a_prime']); b_ub.append(r['b_prime']); prov.append(('up', r['name']))
    # complementarity pins
    for c in list(range(KAP, KAP + 21)) + [ETA]:
        e = np.zeros(NZl); e[c] = 1.0
        A_eq.append(e); b_eq.append(0.0); prov.append(('pin', str(c)))
    # cone
    for i in range(11):
        e = np.zeros(NZl); e[i] = 1.0
        A_ub.append(e); b_ub.append(0.0); prov.append(('cone-site', str(i)))
    for i in range(9):
        e = np.zeros(NZl); e[CL + i] = -1.0
        A_ub.append(e); b_ub.append(0.0); prov.append(('cone-closure', str(i)))
    return np.array(A_eq), np.array(b_eq), np.array(A_ub), np.array(b_ub), prov


def run(npts, seed, verbose=True):
    d = setup(npts, seed)
    A_eq, b_eq, A_ub, b_ub, prov = build_LP(d)
    Rv, bv = d['Rv'], d['bv']
    # variables (z, s): validity rows  -(Rv z) - s <= -bv ; other rows homogeneous in (z, s)
    nv = NZ + 1
    A = np.zeros((A_ub.shape[0] + Rv.shape[0], nv)); b = np.zeros(A.shape[0])
    r = 0
    for j in range(A_ub.shape[0]):
        A[r, :NZ] = A_ub[j]; b[r] = b_ub[j]; r += 1
    for j in range(Rv.shape[0]):
        A[r, :NZ] = -Rv[j]; A[r, NZ] = -1.0; b[r] = -bv[j]; r += 1
    Aeq = np.hstack([A_eq, np.zeros((A_eq.shape[0], 1))])
    c = np.zeros(nv); c[NZ] = -1.0
    res = linprog(c, A_ub=A, b_ub=b, A_eq=Aeq, b_eq=b_eq,
                  bounds=[(-1, 1)] * NZ + [(None, None)], method='highs')
    lam = -np.asarray(res.ineqlin.marginals)
    z = res.x[:NZ]; s = res.x[NZ]
    if verbose:
        print('npts=%4d seed=%2d: validity samples %5d   s* = %+.6e   |z|inf = %.4f'
              % (npts, seed, len(Rv), s, np.abs(z).max()))
        F = lam @ A
        print('    Farkas: multipliers >= 0 : %s ; |sum lam A| on z = %.2e ; s-col %.4f ; lam.b = %+.4e'
              % (bool(lam.min() > -1e-9), np.abs(F[:NZ]).max(), F[NZ], float(lam @ b)))
        cnt = {}
        for j in np.where(lam > 1e-9)[0]:
            t = ('val', int(d['kv'][j - A_ub.shape[0]])) if j >= A_ub.shape[0] else (prov[j][0], prov[j][1])
            cnt[str(t)] = cnt.get(str(t), 0) + 1
        print('    rows used: %s' % cnt)
    return dict(npts=npts, seed=seed, s_star=float(s),
                n_val=int(len(Rv)), farkas_z=float(np.abs((lam @ A)[:NZ]).max()),
                farkas_s=float((lam @ A)[NZ]), lam_b=float(lam @ b),
                lam_nonneg=bool(lam.min() > -1e-9))


def main():
    print('=== R20-Y: certificate for "no valid dual support at R = r_cand" (affine instrument) ===')
    out = []
    for npts, seed in [(60, 5), (200, 17), (600, 29)]:
        out.append(run(npts, seed))
        print()
    json.dump(out, open(HERE / 'r20_kkt_cert2.json', 'w'), indent=1)
    print('saved r20_kkt_cert2.json')


if __name__ == '__main__':
    main()
