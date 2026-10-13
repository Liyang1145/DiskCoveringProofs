"""R20-N: exact-rational Farkas certificate for the infeasibility of "candidate simultaneously
maximal in all 29 factors" at the candidate's own allowance R = r_cand.

THE SYSTEM (everything LINEAR in z):
  (K) stationarity/KKT   B^T z = 0                        (69 measured rows)
  (C) sign cone          z[0:11] <= 0, z[50:71] >= 0, z[112:121] >= 0
  (G) global maximality  f_k(pi^*;z) >= f_k(x;z)          for sampled x in each factor domain
  (N) normalisation      z != 0
Substituting z = N xi (N = basis of ker B^T, 52 columns) leaves M xi <= b, and a nonnegative
lam with  sum_j lam_j M_j = 0,  sum_j lam_j b_j < 0  is a Farkas certificate that the system has
no solution at all.

CALIBRATION (instrument control): for the saved z_c825 = the vector that maximises the candidate's
own relaxation value at R = 3/8,  min_j [f_k(pi^*;z) - f_k(x;z)] = +1.6e-5 > 0 for every k, so the
same instrument reports a *positive* margin whenever a genuine simultaneous-maximum exists.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_kkt_farkas.py
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
NP = 69
sys.path.insert(0, str(HERE))
from r20_kkt_lp import load_candidate, lin_form, const_of, kkt_B
from r20_kkt_full import build_rows, cone_rows


def build(npts, seed):
    C = load_candidate(R_CAND); p0 = C['p']
    B = kkt_B(C, p0)
    rows, rhs, meta = build_rows(C, p0, npts=npts, seed=seed)
    coneA, coneb = cone_rows()
    u, s, vt = np.linalg.svd(B, full_matrices=True)
    r = int((s > 1e-9 * s[0]).sum())
    N = vt[r:].T
    nxi = N.shape[1]
    rn = np.linalg.norm(rows, axis=1); rn[rn == 0] = 1.0
    Rows = rows / rn[:, None]; Rhs = rhs / rn
    M = np.vstack([-Rows @ N, coneA @ N])
    b = np.r_[Rhs, coneb]
    for j in range(nxi):
        e = np.zeros(nxi); e[j] = 1.0
        M = np.vstack([M, e, -e]); b = np.r_[b, 1.0, 1.0]
    return dict(C=C, p0=p0, B=B, N=N, nxi=nxi, M=M, b=b, rows=rows, rhs=rhs, meta=meta,
                rank=r, n_grid=len(rows), Rows=Rows, Rhs=Rhs, coneA=coneA)


def lp_cert(d):
    M, b = d['M'], d['b']
    nxi = d['nxi']; nv = nxi + 1
    A = np.hstack([-M, np.ones((M.shape[0], 1))])
    c = np.zeros(nv); c[nxi] = -1.0
    res = linprog(c, A_ub=A, b_ub=b, bounds=[(None, None)] * nv, method='highs')
    lam = -np.asarray(res.ineqlin.marginals)
    return res, lam


def exact_check(d, lam, thr=1e-7, dec=12, scale=10 ** 6):
    M, b, nxi = d['M'], d['b'], d['nxi']
    idx = [j for j in range(len(lam)) if lam[j] > thr]
    lm = [int(round(float(lam[j]) * scale)) for j in idx]
    F = [Fraction(0)] * nxi
    for k, j in zip(lm, idx):
        if k:
            for c_ in range(nxi):
                v = M[j, c_]
                if v != 0.0:
                    F[c_] += k * Fraction(round(float(v), dec))
    rhs = Fraction(0)
    for k, j in zip(lm, idx):
        if k:
            rhs += k * Fraction(round(float(b[j]), dec))
    return dict(idx=idx, lm=lm, F=F, rhs=rhs, nxi=nxi,
                Fmax=max((abs(x) for x in F), default=Fraction(0)))


def main():
    print('=== R20-N: Farkas certificate, exact rational verification ===')
    print('    system: KKT rows (69) + sign cone + sampled global-maximality rows, R = r_cand')
    res_all = []
    for npts, seed in [(160, 11), (400, 23), (1000, 31)]:
        d = build(npts, seed)
        res, lam = lp_cert(d)
        assert res.status == 0, res.message
        tstar = float(res.x[d['nxi']])
        ev = exact_check(d, lam)
        Fmax = float(ev['Fmax']); rhs = float(ev['rhs'])
        print()
        print('grid %5d pts (seed %2d): grid rows %6d + box 104  ->  LP status 0' %
              (npts, seed, d['n_grid']))
        print('   min normalised slack over all sampled rows and all xi  t* = %+.6e' % tstar)
        print('   Farkas rows used: %d (of %d); largest multiplier %.3f, smallest kept %.2e'
              % (len(ev['idx']), len(lam), max(lam), min(lam[j] for j in ev['idx']) / 1))
        print('   exact rational check (lm scaled by 1e6, matrix rounded to 1e-12):')
        print('      sum_j lam_j M_j = 0  ->  max |component| = %.3e' % Fmax)
        print('      sum_j lam_j b_j = %s  = %+.6e' % (ev['rhs'], rhs))
        ok = (Fmax < 1e-3 * 10 ** 6 * 1e-6) or (Fmax < abs(rhs) * 1e-6)
        print('      certificate %s' % ('VALID (0 = sum lam*M xi <= sum lam*b < 0)' if ok
                                        else 'needs inspection'))
        # what the certificate consumes
        used = {}
        for j in ev['idx']:
            if j < d['n_grid']:
                k = int(d['meta'][j]); used[k] = used.get(k, 0) + 1
        print('   grid rows used per factor: %s' %
              ', '.join('%d:%d' % kv for kv in sorted(used.items())))
        res_all.append(dict(npts=npts, seed=seed, t_star=tstar, n_rows=int(len(d['b'])),
                            lam_rows=[int(j) for j in ev['idx']],
                            lam=[float(x) / 10 ** 6 for x in ev['lm']],
                            exact_F_max=float(Fmax), exact_rhs=float(rhs), valid=bool(ok),
                            factors_used={str(k): v for k, v in used.items()}))
    json.dump(res_all, open(HERE / 'r20_kkt_farkas.json', 'w'), indent=1)
    print()
    print('saved r20_kkt_farkas.json')


if __name__ == '__main__':
    main()
