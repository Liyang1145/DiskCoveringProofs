"""R20-DEC: decisive combined LP (producer-faithful family, candidate allowance).

Find z with
  (COMP)  G z >= h              46 rational competitors (necessary: the candidate must beat them)
  (KKT)   affine stationarity at the candidate (42 two-sided + 36 one-sided rows)
  (CONE)  producer cone: z[KAP:KAP+21] >= 0, z[ETA] = 0, z[LAM] >= 0
  (BND)   V(z; pi*) <= pi       (the tightness requirement: f_k are the SUPREMUM values, so a
                                 valid sharp certificate has V = pi exactly at the candidate)
and minimise V(z; pi*) = sum_k (v_k(pi*) + M_k(pi*).z)  (linear in z).

* If the minimum is > pi the system is infeasible  => the pure 121-column 29-factor family cannot
  support the saved candidate as a sharp simultaneous maximum at R = r_cand.
* If the minimum is <= pi, a witness exists and the remaining obligation is rigor
  (interval enclosure of the competitor rows).

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_decisive.py
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
    return dict(C=C, p0=p0, v0=v0, M0=M0, G=G, h=h, meta=meta,
                Aeq=np.array(Aeq), beq=np.array(beq), Aup=np.array(Aup), bup=np.array(bup))


def cone():
    A = []; b = []
    for i in range(21):
        r = np.zeros(NZ); r[KAP + i] = -1.0; A.append(r); b.append(0.0)
    r = np.zeros(NZ); r[LAM] = -1.0; A.append(r); b.append(0.0)
    r = np.zeros(NZ); r[ETA] = 1.0; A.append(r); b.append(0.0)
    r = np.zeros(NZ); r[ETA] = -1.0; A.append(r); b.append(0.0)
    return np.array(A), np.array(b)


def main():
    d = build()
    Vc = np.zeros(NZ)
    for k in range(29):
        Vc += d['M0'][k]
    Vconst = float(d['v0'].sum())
    print('=== R20-DEC: decisive combined LP ===')
    print('   V(z;pi*) = %.12f + Vc . z   (at z_c825 the value is pi)' % Vconst)

    def solve(with_kkt, with_cone, with_bnd, tag):
        AU = [-d['G']]; bU = [-d['h']]
        AE = [d['Aeq']]; bE = [d['beq']]
        if with_kkt:
            AU.append(d['Aup']); bU.append(d['bup'])
        if with_cone:
            cA, cb = cone(); AU.append(cA); bU.append(cb)
        if with_bnd:
            AU.append(Vc[None, :]); bU.append(np.array([PI - Vconst]))
        AU = np.vstack(AU); bU = np.concatenate([np.asarray(x, float).ravel() for x in bU])
        AE = np.vstack(AE); bE = np.concatenate([np.asarray(x, float).ravel() for x in bE])
        res = linprog(Vc, A_ub=AU, b_ub=bU, A_eq=AE, b_eq=bE,
                      bounds=[(None, None)] * NZ, method='highs')
        if res.status == 0:
            z = res.x
            print('   %-28s FEASIBLE  min V = %.9f   (pi = %.9f)  |z|inf = %.4g'
                  % (tag, Vconst + Vc @ z, PI, np.abs(z).max()))
        else:
            print('   %-28s INFEASIBLE (%s)' % (tag, res.message.split('.')[0]))
        return res

    solve(False, False, True, 'COMP + V<=pi')
    solve(True, False, True, 'COMP + KKT + V<=pi')
    solve(True, True, True, 'COMP + KKT + CONE + V<=pi')
    solve(True, True, False, 'COMP + KKT + CONE (no bound)')
    json.dump(dict(Vconst=Vconst, R=R_CAND, n_comp=int(len(d['h'])),
                   h=[float(x) for x in d['h']]),
              open(HERE / 'r20_decisive.json', 'w'), indent=1)
    print('   saved r20_decisive.json')


if __name__ == '__main__':
    main()
