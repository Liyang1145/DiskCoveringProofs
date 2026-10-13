"""R20-AE: the affine LP on the validated 78-parameter instrument, cone variants.

Instrument (validated in r20_instrument78.py):
    B (78 x 121), bp (78) with  B[q] = d a_k/dxi, bp[q] = d b_k/dxi,
    V2 control: bp[q] + B[q].z matches a full numeric derivative to 1.2e-10,
    V3 control: sum_k f_k(pi*;z_c825) = pi.
Stationarity for the candidate being maximal: interior  bp + B z = 0 ; at an UPPER boundary
(inward = decreasing)  bp + B z >= 0 ; at a LOWER boundary  bp + B z <= 0.

Cone variants (the sign of each multiplier family, per the "multiplier >= 0" rule):
   V0: only z[0:11] <= 0 (vertex angle sums), everything else free
   V1: V0 + z[KAP], z[LAM], z[ETA] >= 0 (they enter as negative constraint terms)
   V2: V1 + z[CL] >= 0
   V3: V2 + z[RR] >= 0 and z[LIN+21:] >= 0 (the copy families)
   V4: V3 + z[SIDE], z[LIN] free (difference forms) -- same as V3
For each variant we ask: is there a nonzero z satisfying (cone + stationarity + sampled validity
rows V(z) >= pi)?  Reported with the LP margin and the Farkas row provenance.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_lp78.py
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
I_FACE, I_BSW, I_RNG = 0, 33, 51
sys.path.insert(0, str(HERE))
from r20_family78 import load_candidate, lin_form, const_of, param_table


def sample_tuples(C, p0, npts, seed):
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
            X[I_BSW + k - 11] = rng.uniform(1e-9, PI / 2)
            X[I_BSW + 9 + k - 11] = rng.uniform(0, 1)
            out.append((k, X))
    qmin = 4 * math.sin(PI - 8 * math.asin(R)) ** 2 / R ** 2
    for k in range(20, 29):
        c = 0
        while c < npts:
            a = rng.uniform(1e-6, PI - 1e-6); u = rng.uniform(0, 1); v = rng.uniform(0, 1)
            if (u - v) ** 2 + 4 * u * v * math.sin(a / 2) ** 2 < qmin:
                continue
            X = p0.copy(); i = k - 20
            X[I_RNG + 3 * i:I_RNG + 3 * i + 3] = (a, u, v)
            out.append((k, X)); c += 1
    return out


def cone_variant(v):
    A = []; prov = []
    def add(col, sgn, name):
        r = np.zeros(NZ); r[col] = sgn; A.append(r); prov.append(name)
    for i in range(11):
        add(i, 1.0, 'site%d' % i)             # z_i <= 0
    if v >= 1:
        for i in range(21):
            add(KAP + i, -1.0, 'kap%d' % i)   # z >= 0
        add(LAM, -1.0, 'lam'); add(ETA, -1.0, 'eta')
    if v >= 2:
        for i in range(9):
            add(CL + i, -1.0, 'cl%d' % i)     # z >= 0
    if v >= 3:
        for i in range(18):
            add(RR + i, -1.0, 'rr%d' % i)     # z >= 0
        for i in range(18):
            add(LIN + 21 + i, -1.0, 'cp%d' % i)
    return np.array(A) if A else np.zeros((0, NZ)), prov


def run(npts, seed, cone_v, verbose=True):
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    B = np.load(HERE / 'r20_B78.npy'); bp = np.load(HERE / 'r20_bp78.npy')
    tab = param_table(p0)
    Aeq = []; beq = []; Aub = []; bub = []; names = []
    for r in tab:
        q = r['q']
        if r['activity'] == 'in':
            Aeq.append(B[q]); beq.append(-bp[q]); names.append(('eq', r['name']))
        elif r['activity'] == 'up':
            Aub.append(-B[q]); bub.append(bp[q]); names.append(('up', r['name']))
        else:
            Aub.append(B[q]); bub.append(-bp[q]); names.append(('lo', r['name']))
    coneA, cprov = cone_variant(cone_v)
    Aeq = np.array(Aeq); beq = np.array(beq)
    Aub = np.vstack([np.array(Aub), coneA]) if Aub else coneA
    bub = np.r_[np.array(bub), np.zeros(coneA.shape[0])]
    # validity rows
    S = sample_tuples(C, p0, npts, seed)
    a_c = {}; b_c = {}
    for k in range(29):
        a, b = lin_form(k, p0, C); a_c[k] = a; b_c[k] = b
    Rv = np.zeros((len(S), NZ)); bv = np.zeros(len(S)); kv = np.zeros(len(S), int)
    for j, (k, X) in enumerate(S):
        a, b = lin_form(k, X, C)
        Rv[j] = a_c[k] - a; bv[j] = b - b_c[k]; kv[j] = int(k)
    nv = NZ + 1
    A = np.zeros((Aub.shape[0] + Rv.shape[0], nv)); b = np.zeros(A.shape[0])
    A[:Aub.shape[0], :NZ] = Aub; b[:Aub.shape[0]] = bub
    A[Aub.shape[0]:, :NZ] = -Rv; A[Aub.shape[0]:, NZ] = -1.0; b[Aub.shape[0]:] = -bv
    Aeq2 = np.hstack([Aeq, np.zeros((Aeq.shape[0], 1))])
    c = np.zeros(nv); c[NZ] = -1.0
    res = linprog(c, A_ub=A, b_ub=b, A_eq=Aeq2, b_eq=beq, bounds=[(-1, 1)] * NZ + [(None, None)],
                  method='highs')
    if verbose:
        tag = 'FEASIBLE' if res.status == 0 else 'INFEASIBLE'
        extra = ''
        if res.status == 0:
            z = res.x[:NZ]
            V = const_of(z, R)
            for k in range(29):
                V += b_c[k] + a_c[k] @ z
            extra = '  s*=%+.4e  V(z)=%.9f  |z|inf=%.3f' % (res.x[NZ], V, np.abs(z).max())
        print('   cone V%d npts=%4d rows(%d eq/%d ineq + %d VAL): %s%s'
              % (cone_v, npts, Aeq.shape[0], Aub.shape[0], len(S), tag, extra))
    return res, (Aeq, beq, Aub, bub, Rv, bv, tab)


def main():
    print('=== R20-AE: affine LP, 78-parameter instrument, R = r_cand ===')
    for cv in (0, 1, 2, 3):
        run(60, 5, cv)
    print()
    print('--- with the full cone (V3), grid refinement ---')
    for npts, seed in [(60, 5), (300, 13), (1000, 31)]:
        run(npts, seed, 3)


if __name__ == '__main__':
    main()
