"""R20-AA: affine LP on the rebuilt 78-parameter instrument.

System at R = r_cand = 0.3799838531198388 (lead caliber fix):
  (KT)  interior parameter rows:   b'_r + a'_r . z = 0            (AFFINE stationarity)
  (one) upper-boundary rows (36 of them, the saturated radius copies): inward direction decreases
        the parameter, so the necessary condition is  b'_r + a'_r . z >= 0
  (cone) per-constraint multiplier signs, taken as the rule "each multiplier >= 0":
        z[0:11] <= 0 for the vertex angle sums (they enter as -theta_i),
        z[KAP], z[LAM], z[ETA] >= 0, z[CL] >= 0 (closure is an inequality family),
        the side-match and radius-copy columns are differences of two copies -> free.
  (VAL) validity rows  V(z) >= pi  sampled over every factor's own domain (this is the exact
        statement that z is an upper-bound witness at R = r_cand),
  (norm) |z|_inf <= 1.

The file reports: feasibility of (KT)+(one)+(cone), then with (VAL); if infeasible, the margin and
the Farkas multipliers with row provenance.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_affine_lp.py
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
I_FACE, I_BSW, I_RNG = 0, 33, 51
sys.path.insert(0, str(HERE))
from r20_rebuild import load_candidate, lin_form, const_of, param_table


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
            X = p0.copy(); X[I_BSW + k - 11] = rng.uniform(1e-9, PI / 2)
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


def build_all(C, p0, npts, seed):
    tab = param_table(p0)
    h = 1e-6
    B = np.zeros((NP, NZ)); bp = np.zeros(NP)
    for r in tab:
        q = r['q']; k = r['k']
        pp = p0.copy(); pm = p0.copy(); pp[q] += h; pm[q] -= h
        ap, b1 = lin_form(k, pp, C); am, b2 = lin_form(k, pm, C)
        B[q] = (ap - am) / (2 * h); bp[q] = (b1 - b2) / (2 * h)
    a_c = {}; b_c = {}
    for k in range(29):
        a, b = lin_form(k, p0, C); a_c[k] = a; b_c[k] = b
    S = sample_tuples(C, p0, npts, seed)
    Rv = np.zeros((len(S), NZ)); bv = np.zeros(len(S)); kv = np.zeros(len(S), int)
    for j, (k, X) in enumerate(S):
        a, b = lin_form(k, X, C)
        Rv[j] = a_c[k] - a; bv[j] = b - b_c[k]; kv[j] = int(k)
    return dict(tab=tab, B=B, bp=bp, Rv=Rv, bv=bv, kv=kv, a_c=a_c, b_c=b_c, S=S)


def cone_matrix():
    A = []; prov = []
    for i in range(11):
        r = np.zeros(NZ); r[i] = 1.0; A.append(r); prov.append(('site', i))
    for i in range(21):
        r = np.zeros(NZ); r[KAP + i] = -1.0; A.append(r); prov.append(('kappa', i))
    r = np.zeros(NZ); r[LAM] = -1.0; A.append(r); prov.append(('lam', 0))
    r = np.zeros(NZ); r[ETA] = -1.0; A.append(r); prov.append(('eta', 0))
    for i in range(9):
        r = np.zeros(NZ); r[CL + i] = -1.0; A.append(r); prov.append(('closure', i))
    return np.array(A), prov


def solve(npts, seed, with_val=True, verbose=True):
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    D = build_all(C, p0, npts, seed)
    tab, B, bp, Rv, bv = D['tab'], D['B'], D['bp'], D['Rv'], D['bv']
    Aeq = []; beq = []; Aub = []; bub = []; prov = []
    for r in tab:
        q = r['q']
        if r['activity'] == 'in':
            Aeq.append(B[q]); beq.append(-bp[q]); prov.append(('eq', r['name']))
        elif r['activity'] == 'up':
            Aub.append(-B[q]); bub.append(bp[q]); prov.append(('up', r['name']))
        else:
            Aub.append(B[q]); bub.append(-bp[q]); prov.append(('lo', r['name']))
    cone, cprov = cone_matrix()
    Aeq = np.array(Aeq); beq = np.array(beq)
    Aub = np.vstack([np.array(Aub), cone]); bub = np.r_[np.array(bub), np.zeros(cone.shape[0])]
    prov = prov + [('cone', cprov[i][0] + str(cprov[i][1])) for i in range(len(cprov))]
    if with_val:
        A = np.hstack([-Rv, -np.ones((Rv.shape[0], 1))])
        Aeq2 = np.hstack([Aeq, np.zeros((Aeq.shape[0], 1))])
        bb = np.r_[bub, bv]
        Aub2 = np.vstack([np.hstack([Aub, np.zeros((Aub.shape[0], 1))]), A])
        beq2 = beq
        c = np.zeros(NZ + 1); c[NZ] = 1.0
        res = linprog(c, A_ub=Aub2, b_ub=bb, A_eq=Aeq2, b_eq=beq2,
                      bounds=[(-1, 1)] * NZ + [(None, None)], method='highs')
    else:
        res = linprog(np.zeros(NZ), A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq,
                      bounds=[(-1, 1)] * NZ, method='highs')
    if verbose:
        print('   npts=%4d seed=%2d  KT rows %d, one-sided %d, cone %d, VAL %d: %s'
              % (npts, seed, Aeq.shape[0], len(bub) - cone.shape[0], cone.shape[0],
                 Rv.shape[0] if with_val else 0,
                 'FEASIBLE' if res.status == 0 else 'INFEASIBLE'))
        if with_val:
            s = res.x[NZ]
            print('      margin s* = %+.6e (s<0 means: no z satisfies all sampled validity rows)'
                  % s)
            lam = -np.asarray(res.ineqlin.marginals)
            cnt = {}
            for j in np.where(lam > 1e-9)[0]:
                if j >= len(bub):
                    t = 'VAL-f%d' % D['kv'][j - len(bub)] if with_val else 'x'
                else:
                    t = prov[j][0]
                cnt[t] = cnt.get(t, 0) + 1
            print('      Farkas multipliers used: %s' % cnt)
    return res, D


def main():
    print('=== R20-AA: affine LP, 78 independent parameters, R = r_cand ===')
    res, D = solve(60, 5, with_val=False)
    print()
    res2, D2 = solve(60, 5, with_val=True)
    print()
    for npts, seed in [(200, 17), (600, 29)]:
        solve(npts, seed, with_val=True)
    print('    done')


if __name__ == '__main__':
    main()
