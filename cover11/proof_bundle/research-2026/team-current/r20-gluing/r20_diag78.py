"""R20-AF: differential diagnosis on the validated 78-parameter instrument.

Groups:
  CONE   z[0:11] <= 0 (vertex angle sums)
  KKT    affine stationary rows of the Lagrangian at the candidate
  VAL    sampled rows  V(z; pi*) - V(z; X) >= 0, i.e. the candidate beats every sampled X
         (this is the exact condition for the candidate to be a simultaneous maximum, and for
          the bound to be tight at R = r_cand)

Reported: feasibility of every subset, then the margin/Farkas certificate for the full system.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_diag78.py
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
from r20_lp78 import sample_tuples, cone_variant


def build(npts=60, seed=5):
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    B = np.load(HERE / 'r20_B78.npy'); bp = np.load(HERE / 'r20_bp78.npy')
    tab = param_table(p0)
    Aeq = []; beq = []; Aub = []; bub = []
    for r in tab:
        q = r['q']
        if r['activity'] == 'in':
            Aeq.append(B[q]); beq.append(-bp[q])
        elif r['activity'] == 'up':
            Aub.append(-B[q]); bub.append(bp[q])
        else:
            Aub.append(B[q]); bub.append(-bp[q])
    S = sample_tuples(C, p0, npts, seed)
    a_c = {}; b_c = {}
    for k in range(29):
        a, b = lin_form(k, p0, C); a_c[k] = a; b_c[k] = b
    Rv = np.zeros((len(S), NZ)); bv = np.zeros(len(S)); kv = np.zeros(len(S), int)
    for j, (k, X) in enumerate(S):
        a, b = lin_form(k, X, C)
        Rv[j] = a_c[k] - a; bv[j] = b - b_c[k]; kv[j] = int(k)
    return dict(C=C, p0=p0, R=R, Aeq=np.array(Aeq), beq=np.array(beq), Aub=np.array(Aub),
                bub=np.array(bub), Rv=Rv, bv=bv, kv=kv, tab=tab, a_c=a_c, b_c=b_c)


def feas(d, use_cone, use_kkt, use_val, cone_v=0):
    AU = []; bU = []; AE = []; bE = []
    if use_cone:
        cA, _ = cone_variant(cone_v)
        AU.append(cA); bU.append(np.zeros(cA.shape[0]))
    if use_kkt:
        AU.append(d['Aub']); bU.append(d['bub'])
        AE.append(d['Aeq']); bE.append(d['beq'])
    if use_val:
        AU.append(d['Rv']); bU.append(d['bv'])
    AU = np.vstack(AU) if AU else np.zeros((0, NZ))
    bU = np.concatenate([np.asarray(x, float).ravel() for x in bU]) if bU else np.zeros(0)
    AE = np.vstack(AE) if AE else np.zeros((0, NZ))
    bE = np.concatenate([np.asarray(x, float).ravel() for x in bE]) if bE else np.zeros(0)
    # nonzero requirement: normalise the largest component via a box and ask for feasibility
    res = linprog(np.zeros(NZ), A_ub=AU, b_ub=bU, A_eq=AE, b_eq=bE,
                  bounds=[(-1, 1)] * NZ, method='highs')
    return res


def main():
    d = build(60, 5)
    print('=== R20-AF: subset feasibility (box |z|<=1) ===')
    tests = [('CONE only           ', True, False, False, 0),
             ('KKT only            ', False, True, False, 0),
             ('CONE+KKT            ', True, True, False, 0),
             ('VAL only            ', False, False, True, 0),
             ('CONE+VAL            ', True, False, True, 0),
             ('KKT+VAL             ', False, True, True, 0),
             ('CONE+KKT+VAL        ', True, True, True, 0)]
    for tag, uc, uk, uv, cv in tests:
        res = feas(d, uc, uk, uv, cv)
        print('   %-20s %s' % (tag, 'FEASIBLE' if res.status == 0 else 'INFEASIBLE'))
    print()
    print('=== the degenerate direction: cone in which family? ===')
    for cv in (0, 1, 2, 3):
        res = feas(d, True, True, True, cv)
        print('   CONE variant V%d + KKT + VAL: %s' % (cv, 'FEASIBLE' if res.status == 0
                                                        else 'INFEASIBLE'))
    # margin LP for the full system
    print()
    print('=== margin LP (max s, all groups) ===')
    Aeq, beq = d['Aeq'], d['beq']
    cA, _ = cone_variant(3)
    nv = NZ + 1
    AU = np.zeros((d['Aub'].shape[0] + cA.shape[0] + d['Rv'].shape[0], nv))
    bU = np.zeros(AU.shape[0])
    r = 0
    AU[r:r + d['Aub'].shape[0], :NZ] = d['Aub']; bU[r:r + d['Aub'].shape[0]] = d['bub']
    r += d['Aub'].shape[0]
    AU[r:r + cA.shape[0], :NZ] = cA; r += cA.shape[0]
    AU[r:, :NZ] = -d['Rv']; AU[r:, NZ] = -1.0; bU[r:] = -d['bv']
    AE = np.hstack([Aeq, np.zeros((Aeq.shape[0], 1))])
    c = np.zeros(nv); c[NZ] = -1.0
    res = linprog(c, A_ub=AU, b_ub=bU, A_eq=AE, b_eq=beq, bounds=[(-1, 1)] * NZ + [(None, None)],
                  method='highs')
    print('   status %d  margin s* = %+.6e' % (res.status, res.x[NZ] if res.status == 0 else np.nan))
    if res.status == 0:
        z = res.x[:NZ]
        V = const_of(z, d['R'])
        for k in range(29):
            V += d['b_c'][k] + d['a_c'][k] @ z
        print('   V(z;pi*) = %.9f   |z|inf = %.4f' % (V, np.abs(z).max()))
    json.dump(dict(tests=[[t[0], int(feas(d, t[1], t[2], t[3], t[4]).status)] for t in tests]),
              open(HERE / 'r20_diag78.json', 'w'), indent=1)
    print('   saved r20_diag78.json')


if __name__ == '__main__':
    main()
