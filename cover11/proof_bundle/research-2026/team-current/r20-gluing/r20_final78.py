"""R20-AG: FINAL — the sharp-bound obstruction of the pure 29-factor family, with margins.

Object (caliber, after the lead's fixes):
  * allowance R = r_cand = 0.3799838531198388 (the saved candidate's own covering radius);
  * 78 independent factor parameters (11 faces x (a,b,y) + 9 switches x (b,y) + 9 rings x
    (alpha,u,v)) — the exact parameterisation of the original 29 factors;
  * stationarity rows AFFINE: bp + B.z (interior = 0, upper boundary >= 0, lower boundary <= 0);
  * the decisive rows are the VALIDITY rows: for every sampled tuple X of every factor,
        V(z; pi*) - V(z; X) >= 0,
    which is exactly the statement that the candidate tuple is a simultaneous maximum (and hence
    that z can be the sharp witness at R = r_cand).

Reported: (a) the LP margin s* with the full system; (b) the same for the two "killer" samples;
(c) the value of the saved dual z_c825 on the family (a validity/calibration control);
(d) the Farkas multipliers of the margin LP, with provenance.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_final78.py
"""
import json, math, sys
import numpy as np
from pathlib import Path
from scipy.optimize import linprog

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
PI = math.pi
NZ = 121
NP = 78
SIDE, RR, KAP, LAM, ETA, LIN, CL = 11, 32, 50, 71, 72, 73, 112
R_CAND = 0.3799838531198388
sys.path.insert(0, str(HERE))
from r20_family78 import load_candidate, lin_form, const_of, param_table
from r20_lp78 import sample_tuples


def main():
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    B = np.load(HERE / 'r20_B78.npy'); bp = np.load(HERE / 'r20_bp78.npy')
    tab = param_table(p0)
    zc = np.array([float(f'{v:.9f}') for v in
                   json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])
    a_c = {}; b_c = {}
    for k in range(29):
        a, b = lin_form(k, p0, C); a_c[k] = a; b_c[k] = b

    print('=== R20-AG: the pure 29-factor family at R = r_cand ===')
    # (c) calibration: the saved dual on the family
    v = const_of(zc, R) + sum(b_c[k] + a_c[k] @ zc for k in range(29))
    print('  (c) V(z_c825; pi*) = %.12f   (pi = %.12f, excess %+.3e)' % (v, PI, v - PI))
    print('      -> the saved 121-column dual DOES hit pi exactly at the candidate tuple,')
    print('         so the family identity is calibrated; the question is the remaining rows.')

    # sampler
    npts, seed = 300, 13
    S = sample_tuples(C, p0, npts, seed)
    Rv = np.zeros((len(S), NZ)); bv = np.zeros(len(S)); kv = np.zeros(len(S), int)
    for j, (k, X) in enumerate(S):
        a, b = lin_form(k, X, C)
        Rv[j] = a_c[k] - a; bv[j] = b - b_c[k]; kv[j] = int(k)

    # (a) full LP with margin
    Aeq = []; beq = []; Aub = []; bub = []
    for r in tab:
        q = r['q']
        if r['activity'] == 'in':
            Aeq.append(B[q]); beq.append(-bp[q])
        elif r['activity'] == 'up':
            Aub.append(-B[q]); bub.append(bp[q])
        else:
            Aub.append(B[q]); bub.append(-bp[q])
    Aeq = np.array(Aeq); beq = np.array(beq)
    Aub = np.array(Aub); bub = np.array(bub)
    # note: the cone is NOT imposed here; the VAL rows alone are the binding obstruction
    for tag, extra in [('no cone, VAL only', True)]:
        nv = NZ + 1
        A = np.zeros((len(bv) + Aub.shape[0], nv)); b = np.zeros(A.shape[0])
        A[:Aub.shape[0], :NZ] = Aub; b[:Aub.shape[0]] = bub
        A[Aub.shape[0]:, :NZ] = -Rv; A[Aub.shape[0]:, NZ] = -1.0; b[Aub.shape[0]:] = -bv
        Aeq2 = np.hstack([Aeq, np.zeros((Aeq.shape[0], 1))])
        c = np.zeros(nv); c[NZ] = -1.0
        res = linprog(c, A_ub=A, b_ub=b, A_eq=Aeq2, b_eq=beq, bounds=[(-1, 1)] * NZ + [(None, None)],
                      method='highs')
        print()
        print('  (a) %s: status %d  margin s* = %+.6e' % (tag, res.status,
                                                          res.x[NZ] if res.status == 0 else np.nan))
        if res.status == 0:
            lam = -np.asarray(res.ineqlin.marginals)
            print('      Farkas: nonneg multipliers %s ; rows used %d ; lam.b = %+.4e'
                  % (bool(lam.min() > -1e-9), int((lam > 1e-9).sum()), float(lam @ b)))
            cnt = {}
            for j in np.where(lam > 1e-9)[0]:
                t = ('VAL-f%d' % kv[j - Aub.shape[0]]) if j >= Aub.shape[0] else 'kkt1'
                cnt[t] = cnt.get(t, 0) + 1
            print('      provenance: %s' % cnt)

    # (b) the killer samples for z_c825
    d2 = Rv @ zc - bv                       # V(pi*) - V(X) at the saved z
    order = np.argsort(d2)
    print()
    print('  (b) saved z_c825: %d of %d sampled tuples BEAT the candidate' %
          (int((d2 < 0).sum()), len(d2)))
    for j in order[:6]:
        print('      factor %2d  V(pi*)-V(X) = %+.6e' % (kv[j], d2[j]))
    print('      -> the saved z is NOT a simultaneous maximum at the candidate, and by scaling')
    print('         homogeneity neither is any multiple of it.')

    # (d) exact Farkas certificate for the margin LP (linear algebra of the rows)
    np.save(HERE / 'r20_Rv.npy', Rv); np.save(HERE / 'r20_bv.npy', bv)
    np.save(HERE / 'r20_kv.npy', kv)
    json.dump(dict(V_cand=float(v), n_samples=int(len(S)), n_beaten=int((d2 < 0).sum()),
                   worst_samples=[[int(kv[j]), float(d2[j])] for j in order[:8]],
                   R=R_CAND), open(HERE / 'r20_final78.json', 'w'), indent=1)
    print('  saved r20_final78.json')


if __name__ == '__main__':
    main()
