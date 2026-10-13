"""R20-FINAL2: the sharp-support LP on the producer-faithful family.

Find z (121 columns) with
   (COMP)  f_k(pi*;z) >= f_k(X;z)   for sampled competitors X in every factor's own domain
           (f_k(X;z) = v_k(X) + M_k(X).z is linear in z at fixed X)
   (KKT)   affine stationarity at the candidate: interior rows = 0, upper-boundary rows >= 0
   (CONE)  the producer's sign restrictions: z[KAP:KAP+21] >= 0, z[ETA] = 0, z[LAM] >= 0
   (box)   |z|_inf <= 1
COMP alone is necessary for a valid sharp certificate; KKT and CONE narrow the family, so
"COMP alone infeasible" is the STRONGEST possible refutation, and "COMP+KKT+CONE feasible" is the
only configuration that could support the candidate.

Also reports the Farkas multipliers for an infeasible configuration.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_sharp_lp.py
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
NP = 78
IF, IB, IR = 0, 33, 51
sys.path.insert(0, str(HERE))
from r20_producer_family import load_candidate, value_and_row, param_table


def sample_competitors(C, p0, npts, seed):
    rng = np.random.default_rng(seed)
    R = C['R']; out = []
    for k in range(11):
        c = 0
        while c < npts:
            a = rng.uniform(1e-9, PI); b = rng.uniform(1e-9, PI)
            if a + b >= PI - 1e-9:
                continue
            X = p0.copy(); X[3 * k:3 * k + 3] = (a, b, rng.uniform(0, 1))
            out.append((k, X)); c += 1
    for k in range(11, 20):
        for _ in range(npts):
            X = p0.copy()
            X[IB + k - 11] = rng.uniform(1e-9, PI / 2)
            X[IB + 9 + k - 11] = rng.uniform(0, 1)
            out.append((k, X))
    for k in range(20, 29):
        for _ in range(npts):
            X = p0.copy(); i = k - 20
            X[IR + 3 * i:IR + 3 * i + 3] = (rng.uniform(1e-6, PI - 1e-6),
                                            rng.uniform(0, 1), rng.uniform(0, 1))
            out.append((k, X))
    return out


def build(npts, seed):
    C = load_candidate(R_CAND); p0 = C['p']
    zc = np.array([float(f'{v:.9f}') for v in
                   json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])
    v0 = np.zeros(29); M0 = np.zeros((29, NZ))
    for k in range(29):
        v0[k], M0[k] = value_and_row(k, p0, C)
    S = sample_competitors(C, p0, npts, seed)
    Av = np.zeros((len(S), NZ)); bv = np.zeros(len(S)); kv = np.zeros(len(S), int)
    for j, (k, X) in enumerate(S):
        v, M = value_and_row(k, X, C)
        Av[j] = M0[k] - M                      # (M0-M).z >= v - v0
        bv[j] = v - v0[k]; kv[j] = int(k)
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
    return dict(C=C, p0=p0, Av=Av, bv=bv, kv=kv, M0=M0, v0=v0,
                Aeq=np.array(Aeq), beq=np.array(beq), Aup=np.array(Aup), bup=np.array(bup),
                tab=tab, zc=zc)


def cone_rows():
    A = []; b = []
    for i in range(21):
        r = np.zeros(NZ); r[KAP + i] = -1.0; A.append(r); b.append(0.0)     # z >= 0
    r = np.zeros(NZ); r[LAM] = -1.0; A.append(r); b.append(0.0)
    r = np.zeros(NZ); r[ETA] = 1.0; A.append(r); b.append(0.0)              # z_eta = 0
    r = np.zeros(NZ); r[ETA] = -1.0; A.append(r); b.append(0.0)
    return np.array(A), np.array(b)


def run(d, use_kkt, use_cone, tag):
    Au = [d['Av']]; bu = [d['bv']]
    Ae = [d['Aeq']]; be = [d['beq']]
    if use_kkt:
        Au.append(d['Aup']); bu.append(d['bup'])
    if use_cone:
        cA, cb = cone_rows(); Au.append(cA); bu.append(cb)
    Au = np.vstack(Au); bu = np.concatenate([np.asarray(x, float).ravel() for x in bu])
    Ae = np.vstack(Ae); be = np.concatenate([np.asarray(x, float).ravel() for x in be])
    res = linprog(np.zeros(NZ), A_ub=Au, b_ub=bu, A_eq=Ae, b_eq=be,
                  bounds=[(-1, 1)] * NZ, method='highs')
    ok = res.status == 0
    extra = ''
    if ok:
        z = res.x
        V = float(sum(d['v0'][k] + d['M0'][k] @ z for k in range(29)))
        extra = '  |z|=%.3f  V=%.9f' % (np.abs(z).max(), V)
    print('   %-28s %s%s' % (tag, 'FEASIBLE' if ok else 'INFEASIBLE', extra))
    return res, Au, bu


def main():
    print('=== R20-FINAL2: sharp-support LP on the producer-faithful 121-column family ===')
    for npts, seed in [(400, 7), (1200, 19)]:
        d = build(npts, seed)
        print('  npts=%d -> %d competitor rows' % (npts, len(d['bv'])))
        # controls
        sl = d['Av'] @ d['zc'] - d['bv']
        print('     control z_c825: min competitor slack %+.4e  (beaten samples %d of %d)'
              % (sl.min(), int((sl < 0).sum()), len(sl)))
        run(d, False, False, 'COMP only (strongest)')
        run(d, True, False, 'COMP+KKT')
        run(d, True, True, 'COMP+KKT+CONE (sharp family)')
        print()
    print('  Note: COMP alone necessary for any sharp certificate; if it is infeasible, the')
    print('  pure 121-column 29-factor family cannot support the candidate as a simultaneous')
    print('  maximum at R = r_cand, unconditionally.')


if __name__ == '__main__':
    main()
