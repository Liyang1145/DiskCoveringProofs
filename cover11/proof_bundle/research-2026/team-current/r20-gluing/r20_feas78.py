"""R20-AI: FINAL, properly posed at the 78-parameter caliber — feasibility + margin + Farkas.

Two equivalent ways to ask "can the pure 29-factor family make the candidate a simultaneous
maximum at R = r_cand":

  FEAS:   exists z with   |z|_inf <= 1,      (a_k(pi*)-a_k(X)).z >= b_k(X)-b_k(pi*)   for all X,
                          and the affine KKT rows of the candidate.
          (If FEAS is empty, the family cannot do it: the candidate is beaten by some sampled X for
           every z, and by homogeneity for every multiple of z.)
  MARGIN: max s  s.t. the same rows with slack >= s;  s* > 0 feasible, s* < 0 infeasible.
          With s bounded below to keep the LP finite.

Everything is reported with the calibration controls on the saved z_c825 and on z = 0.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_feas78.py
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
from r20_family78 import load_candidate, lin_form, const_of, param_table
from r20_lp78 import sample_tuples, cone_variant


def build(npts, seed):
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    B = np.load(HERE / 'r20_B78.npy'); bp = np.load(HERE / 'r20_bp78.npy')
    tab = param_table(p0)
    a_c = {}; b_c = {}
    for k in range(29):
        a, b = lin_form(k, p0, C); a_c[k] = a; b_c[k] = b
    S = sample_tuples(C, p0, npts, seed)
    Rv = np.zeros((len(S), NZ)); bv = np.zeros(len(S)); kv = np.zeros(len(S), int)
    for j, (k, X) in enumerate(S):
        a, b = lin_form(k, X, C)
        Rv[j] = a_c[k] - a; bv[j] = b - b_c[k]; kv[j] = int(k)
    Aeq = []; beq = []; Aub = []; bub = []
    for r in tab:
        q = r['q']
        if r['activity'] == 'in':
            Aeq.append(B[q]); beq.append(-bp[q])
        elif r['activity'] == 'up':
            Aub.append(-B[q]); bub.append(bp[q])
        else:
            Aub.append(B[q]); bub.append(-bp[q])
    return dict(C=C, p0=p0, R=R, Rv=Rv, bv=bv, kv=kv, Aeq=np.array(Aeq), beq=np.array(beq),
                Aub=np.array(Aub), bub=np.array(bub), tab=tab, a_c=a_c, b_c=b_c)


def rows_full(d, use_kkt=True, use_cone=0, slack_form=False, sbound=100.0):
    """returns (A_ub, b_ub, provenance) with an optional slack variable s."""
    nv = NZ + (1 if slack_form else 0)
    A = []; b = []; prov = []
    for j in range(len(d['bv'])):
        r = np.zeros(nv); r[:NZ] = -d['Rv'][j]
        if slack_form:
            r[NZ] = -1.0
        A.append(r); b.append(-d['bv'][j]); prov.append(('VAL', int(d['kv'][j])))
    if use_kkt:
        for j in range(d['Aub'].shape[0]):
            r = np.zeros(nv); r[:NZ] = d['Aub'][j]
            A.append(r); b.append(d['bub'][j]); prov.append(('kkt1', j))
    if use_cone:
        cA, _ = cone_variant(use_cone)
        for j in range(cA.shape[0]):
            r = np.zeros(nv); r[:NZ] = cA[j]
            A.append(r); b.append(0.0); prov.append(('cone', j))
    return np.array(A), np.array(b), prov


def main():
    print('=== R20-AI: feasibility and margin at the 78-parameter caliber ===')
    for npts, seed in [(300, 13), (1000, 31)]:
        d = build(npts, seed)
        for tag, kw in [('VAL+KKT', dict(use_kkt=True, use_cone=0)),
                        ('VAL+KKT+coneV3', dict(use_kkt=True, use_cone=3))]:
            A, b, prov = rows_full(d, slack_form=False, **kw)
            res = linprog(np.zeros(NZ), A_ub=A, b_ub=b, A_eq=d['Aeq'], b_eq=d['beq'],
                          bounds=[(-1, 1)] * NZ, method='highs')
            feas = (res.status == 0)
            z = res.x if feas else None
            out = '' if not feas else '  |z|inf=%.3f  V(pi*)=%.9f' % (
                np.abs(z).max(),
                const_of(z, d['R']) + sum(d['b_c'][k] + d['a_c'][k] @ z for k in range(29)))
            print('  npts=%4d %-14s: %s%s' % (npts, tag, 'FEASIBLE' if feas else 'INFEASIBLE', out))
            # margin with bounded s
            A2, b2, prov2 = rows_full(d, slack_form=True, **kw)
            nv = NZ + 1
            Aeq2 = np.hstack([d['Aeq'], np.zeros((d['Aeq'].shape[0], 1))])
            c = np.zeros(nv); c[NZ] = -1.0
            res2 = linprog(c, A_ub=A2, b_ub=b2, A_eq=Aeq2, b_eq=d['beq'],
                           bounds=[(-1, 1)] * NZ + [(-100.0, 100.0)], method='highs')
            s = res2.x[NZ] if res2.status == 0 else float('nan')
            print('      margin s* = %+.6e   (s*>0 <=> the candidate can be a simultaneous max)'
                  % s)
            if res2.status == 0 and s < 0:
                lam = -np.asarray(res2.ineqlin.marginals)
                F = lam @ A2
                cnt = {}
                for j in np.where(lam > 1e-9)[0]:
                    t = prov2[j][0]; cnt[t] = cnt.get(t, 0) + 1
                print('      Farkas: nonneg lam %s ; rows %d ; |sum lam A| on z = %.2e ;'
                      ' lam.b = %+.4e ; types %s'
                      % (bool(lam.min() > -1e-9), int((lam > 1e-9).sum()),
                         np.abs(F[:NZ]).max(), float(lam @ b2), cnt))
        zc = np.array([float(f'{v:.9f}') for v in
                       json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])
        sl = d['Rv'] @ zc - d['bv']
        print('  controls: z=0 gives min slack %+.4e ; z_c825 gives %+.4e (beaten samples %d)'
              % (float(np.min(-d['bv'])), sl.min(), int((sl < 0).sum())))
        print()


if __name__ == '__main__':
    main()
