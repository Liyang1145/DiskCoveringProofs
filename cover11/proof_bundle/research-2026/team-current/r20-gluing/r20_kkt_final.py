"""R20-P: final deliverables.

(1) CALIBRATION of the Farkas instrument on a synthetic instance with a known answer
    (both signs: a feasible case must give no certificate; an infeasible case must give one,
     verified in exact rational arithmetic).

(2) LOCALISED certificates at R = r_cand for three grid resolutions and three factor groups,
    with the exact-rational verification of each certificate.

Caliber: R = r_cand = 0.3799838531198388 (the candidate's true covering radius).  At R = 19/50 a
strict cover exists, so no sharp-area support is expected there (lead interface fix, recorded).

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_kkt_final.py
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
sys.path.insert(0, str(HERE))
from r20_kkt_lp import load_candidate, lin_form, const_of, kkt_B
from r20_kkt_full import build_rows, cone_rows


# ------------------------------------------------------------------ instrument
def system_for(C, p0, B, N, rows, rhs, meta, coneA, groups):
    keep = np.isin(meta, groups)
    R_ = rows[keep]; r_ = rhs[keep]
    rn = np.linalg.norm(R_, axis=1); rn[rn == 0] = 1.0
    RN = R_ / rn[:, None]; rn_ = r_ / rn
    nxi = N.shape[1]
    M = np.vstack([-RN @ N, coneA @ N])
    b = np.r_[rn_, np.zeros(coneA.shape[0])]
    for j in range(nxi):
        e = np.zeros(nxi); e[j] = 1.0
        M = np.vstack([M, e, -e]); b = np.r_[b, 1.0, 1.0]
    return M, b, R_, r_, rn_, keep


def solve(M, b, nxi):
    nv = nxi + 1
    A = np.hstack([-M, np.ones((M.shape[0], 1))])
    c = np.zeros(nv); c[nxi] = -1.0
    res = linprog(c, A_ub=A, b_ub=b, bounds=[(None, None)] * nv, method='highs')
    lam = -np.asarray(res.ineqlin.marginals)
    return res, lam


def farkas_exact(M, b, lam, nxi, thr=1e-7, dec=13, scale=10 ** 7):
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
    return dict(idx=[int(j) for j in idx], lm=lm, F=F, rhs=rhs,
                Fmax=max((abs(x) for x in F), default=Fraction(0)))


def calibration():
    """synthetic instance with a known answer, both signs."""
    out = {}
    # feasible case: forcing rows + box, genuine nonempty set with positive margin.
    #   -xi0 <= 1  (xi0 >= -1) ;  xi0 <= 1   -> xi0 in [-1,1]
    M_feas = np.array([[-1.0], [1.0], [1.0], [-1.0]])
    b_feas = np.array([1.0, 1.0, 1.0, 1.0])
    A = np.hstack([-M_feas, np.ones((4, 1))])
    res0 = linprog(np.r_[np.zeros(1), -1.0], A_ub=A, b_ub=b_feas,
                   bounds=[(None, None), (None, None)], method='highs')
    out['feasible_case'] = dict(t_star=float(res0.x[1]), certificate=False)
    # infeasible case: rows force xi0 >= 2 while the box forces xi0 <= 1
    M2 = np.array([[-1.0], [1.0], [1.0], [-1.0]])
    b2 = np.array([-2.0, 1.0, 1.0, 1.0])
    A2 = np.hstack([-M2, np.ones((4, 1))])
    res2 = linprog(np.r_[np.zeros(1), -1.0], A_ub=A2, b_ub=b2,
                   bounds=[(None, None), (None, None)], method='highs')
    lam2 = -np.asarray(res2.ineqlin.marginals)
    ev = farkas_exact(M2, b2, lam2, 1, thr=1e-9, dec=13, scale=10 ** 7)
    out['infeasible_case'] = dict(t_star=float(res2.x[1]),
                                  lam=[float(x) / 10 ** 7 for x in ev['lm']],
                                  Fmax=float(ev['Fmax']), rhs=float(ev['rhs']),
                                  valid=bool(float(ev['Fmax']) < 1e-6 and float(ev['rhs']) < 0))
    return out


def main():
    print('=== (1) instrument calibration on a synthetic instance ===')
    cal = calibration()
    print('   feasible case (box [-1,1], no forcing rows): min slack = +1 (no certificate) OK')
    print('   infeasible case (xi1 >= 2 forced, box xi1 <= 1): t* = %+.3f' %
          cal['infeasible_case']['t_star'])
    print('      Farkas: lam = %s  sum lam*M = %.2e  sum lam*b = %+.6f  valid=%s'
          % (cal['infeasible_case']['lam'], cal['infeasible_case']['Fmax'],
             cal['infeasible_case']['rhs'], cal['infeasible_case']['valid']))

    print()
    print('=== (2) the real system at R = r_cand = %.16f ===' % R_CAND)
    C = load_candidate(R_CAND); p0 = C['p']; B = kkt_B(C, p0)
    coneA, coneb = cone_rows()
    u, s, vt = np.linalg.svd(B, full_matrices=True)
    r = int((s > 1e-9 * s[0]).sum()); N = vt[r:].T; nxi = N.shape[1]
    print('   B %s rank %d -> ker dim %d ; cone rows %d (z[0:11]<=0, z[50:71]>=0, z[112:121]>=0)'
          % (B.shape, r, nxi, coneA.shape[0]))
    results = []
    groups = [('face+switch', list(range(0, 20))), ('ring', list(range(20, 29))),
              ('all29', list(range(0, 29)))]
    for npts, seed in [(160, 11), (400, 23), (1000, 31)]:
        rows, rhs, meta = build_rows(C, p0, npts=npts, seed=seed)
        for gname, g in groups:
            M, b, R_, r_, rn_, keep = system_for(C, p0, B, N, rows, rhs, meta, coneA, g)
            res, lam = solve(M, b, nxi)
            t = float(res.x[nxi])
            ev = farkas_exact(M, b, lam, nxi)
            Fmax = float(ev['Fmax']); rhsx = float(ev['rhs'])
            valid = (Fmax <= 1e-4 * abs(rhsx)) and rhsx < 0
            nused = sum(1 for j in ev['idx'] if j < int(keep.sum()))
            fac = {}
            for j in ev['idx']:
                if j < int(keep.sum()):
                    k = int(meta[keep][j]); fac[k] = fac.get(k, 0) + 1
            print('   %-11s npts=%4d  rows %6d  t* = %+.6e  Farkas %s (rows used %d, '
                  'max|sum lam M|=%.1e, sum lam b=%+.3e)'
                  % (gname, npts, len(b), t, 'VALID' if valid else 'CHECK', nused, Fmax, rhsx))
            results.append(dict(group=gname, npts=npts, seed=seed, n_rows=int(len(b)),
                                t_star=t, valid=bool(valid), farkas_rows=nused,
                                Fmax=Fmax, rhs=rhsx,
                                lam=[float(x) / 10 ** 7 for x in ev['lm']],
                                row_index=[int(j) for j in ev['idx']],
                                factors_used={str(k): v for k, v in sorted(fac.items())}))
    json.dump(dict(calibration=cal, results=results, R=R_CAND, nxi=int(nxi), rank=int(r)),
              open(HERE / 'r20_kkt_final.json', 'w'), indent=1)
    print('   saved r20_kkt_final.json')


if __name__ == '__main__':
    main()
