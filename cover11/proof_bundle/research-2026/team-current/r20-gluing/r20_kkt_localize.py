"""R20-O: instrument control + localisation of the obstruction.

CONTROL (must be positive):  run the same LP machinery with the saved z_c825, which is the vector
that maximises the candidate's own relaxation value at R = 3/8.  There the candidate IS a
simultaneous maximum of all 29 factors (min deficit 1.6e-5 > 0), so the instrument must report a
positive margin.  A negative reading there would mean the instrument is broken.

LOCALISATION:  split the 29 factors into the face+switch group (k = 0..19) and the ring group
(k = 20..28) and run the same system for each group separately, which says which group fails.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_kkt_localize.py
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
from r20_kkt_lp import load_candidate, lin_form, const_of, kkt_B
from r20_kkt_full import build_rows, cone_rows


def system(d, groups, zc):
    """build M xi <= b for the given factor groups; also return the margin of zc."""
    C = d['C']; p0 = d['p0']; B = d['B']
    rows, rhs, meta = d['rows'], d['rhs'], d['meta']
    coneA = d['coneA']
    keep = np.isin(meta, groups)
    R_ = rows[keep]; r_ = rhs[keep]
    rn = np.linalg.norm(R_, axis=1); rn[rn == 0] = 1.0
    RN = R_ / rn[:, None]; rn_ = r_ / rn
    N = d['N']; nxi = d['nxi']
    M = np.vstack([-RN @ N, coneA @ N])
    b = np.r_[rn_, np.zeros(coneA.shape[0])]
    for j in range(nxi):
        e = np.zeros(nxi); e[j] = 1.0
        M = np.vstack([M, e, -e]); b = np.r_[b, 1.0, 1.0]
    # margin of a given z (unscaled rows):
    zN = None
    if zc is not None:
        zz = zc - N @ (N.T @ zc)
        zN = float(np.min(R_ @ zz + r_) / max(1e-30, 1.0))
    return M, b, N, nxi, R_, r_, rn_, zN


def lp_margin(M, b, nxi):
    nv = nxi + 1
    A = np.hstack([-M, np.ones((M.shape[0], 1))])
    c = np.zeros(nv); c[nxi] = -1.0
    res = linprog(c, A_ub=A, b_ub=b, bounds=[(None, None)] * nv, method='highs')
    if res.status != 0:
        return None, None
    lam = -np.asarray(res.ineqlin.marginals)
    return float(res.x[nxi]), lam


def factor_deficits(C, p0, z):
    """min over the factor domain of  f_k(pi*;z) - f_k(x;z), sampled."""
    R = C['R']
    from r20_factor_probe import Model
    m = Model('q0_lower375_dual_0_4.json', R, 'z'); m.z = z
    out = []
    for k in range(29):
        a, b = lin_form(k, p0, C); mine = b + a @ z
        mx = -1e18
        if k < 11:
            t = k
            for a1 in np.linspace(1e-9, PI, 200):
                for b1 in np.linspace(1e-9, PI - a1, 200):
                    v = m.face_val(t, a1, b1)[0]
                    if v > mx:
                        mx = v
        elif k < 20:
            bi = k - 11
            for b1 in np.linspace(1e-9, PI / 2, 4000):
                v = m.switch_val(bi, b1)[0]
                if v > mx:
                    mx = v
        else:
            i = k - 20
            qmin = 4 * math.sin(PI - 8 * math.asin(R)) ** 2 / R ** 2
            for a1 in np.linspace(1e-6, PI - 1e-6, 60):
                for u1 in np.linspace(0, 1, 30):
                    for v1 in np.linspace(0, 1, 30):
                        q = (u1 - v1) ** 2 + 4 * u1 * v1 * math.sin(a1 / 2) ** 2
                        if q < qmin:
                            continue
                        v = m.ring_val(i, a1, u1, v1)
                        if v > mx:
                            mx = v
        out.append(mx - mine)
    return out


def main():
    d = {}
    C = load_candidate(R_CAND); p0 = C['p']; B = kkt_B(C, p0)
    rows, rhs, meta = build_rows(C, p0, npts=140, seed=41)
    coneA, coneb = cone_rows()
    u, s, vt = np.linalg.svd(B, full_matrices=True)
    r = int((s > 1e-9 * s[0]).sum())
    d = dict(C=C, p0=p0, B=B, N=vt[r:].T, nxi=121 - r, rows=rows, rhs=rhs, meta=meta, coneA=coneA)

    print('=== CONTROL: z_c825 (a genuine simultaneous-maximum at R = 3/8) ===')
    zc = np.array([float(f'{v:.9f}') for v in
                   json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])
    # the candidate's own radii make the 18 copies tight at R = 3/8?  use the R=3/8 calibration
    Cr = load_candidate(3 / 8)
    defs = factor_deficits(Cr, Cr['p'], zc)
    print('   factor deficits at R=3/8: min %+.3e over 29 factors (all must be > 0)'
          % min(defs))
    print('   worst three: %s' % [round(v, 8) for v in sorted(defs)[:3]])

    print()
    print('=== LOCALISATION at R = r_cand ===')
    for name, groups in [('face+switch (k=0..19)', list(range(0, 20))),
                         ('ring only  (k=20..28)', list(range(20, 29))),
                         ('all 29', list(range(0, 29)))]:
        M, b, N, nxi, R_, r_, rn_, _ = system(d, groups, None)
        t, lam = lp_margin(M, b, nxi)
        print('   %-24s rows %6d  min normalised slack t* = %+.6e  (Farkas rows used %d)'
              % (name, len(b), t, int((lam > 1e-7).sum())))
    json.dump(dict(control_min_deficit=float(min(defs)), R_cand=R_CAND),
              open(HERE / 'r20_kkt_localize.json', 'w'), indent=1)
    print('   saved r20_kkt_localize.json')


if __name__ == '__main__':
    main()
