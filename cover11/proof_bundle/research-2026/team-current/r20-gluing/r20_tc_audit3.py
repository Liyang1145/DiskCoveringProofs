"""R20-TC-AUDIT 3/3: full Hessian audit for all 5 residuals + Jacobian rank + independence test.

Extends audit 2/2 from the sqrt-circle residual to every residual, and checks that the 5 rows are
functionally independent at the threshold point (the KKT system claims 5 independent
representatives of C366).

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_audit3.py
"""
import json, math, sys
from pathlib import Path

import numpy as np
import sympy as sp

HERE = Path(__file__).parent
TC = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\session2\n11tc\py')


def main():
    sys.path.insert(0, str(TC))
    from mpmath import mp, mpf
    mp.dps = 60
    import tc_core as CORE
    import tc_s32_kraw as K32
    import tc_s33_kkt as S33

    # ---------- symbolic model (same as audit 1/2, re-derived here for all 5 residuals)
    a0, a1, a2, a3, y0, y1, R = sp.symbols('a0 a1 a2 a3 y0 y1 R', real=True)
    a4 = sp.pi - 2 * (a0 + a1 + a2 + a3)
    a = [a0, a1, a2, a3, a4, a3, a2, a1, a0]
    rho = [sp.cos(ak) - sp.sqrt(R ** 2 - sp.sin(ak) ** 2) for ak in a]
    th = [None] * 9
    th[4] = sp.Integer(0)
    for k in range(5, 9):
        th[k] = th[k - 1] + a[k - 1] + a[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (a[k] + a[k + 1])
    Cx = [rho[k] * sp.cos(th[k]) for k in range(9)]
    Cy = [rho[k] * sp.sin(th[k]) for k in range(9)]
    U = []
    for k in range(9):
        k2 = (k + 1) % 9
        U.append((Cx[k] + Cx[k2] - sp.cos(th[k] + a[k]),
                  Cy[k] + Cy[k2] - sp.sin(th[k] + a[k])))
    exprs = []
    for (k, l) in [(1, 1), (2, 0), (3, 0), (8, 1)]:
        c = y1 if l == 1 else y0
        dx = U[k][0] - c
        dy = U[k][1]
        exprs.append(sp.sqrt(dx ** 2 + dy ** 2) - R)
    m = (y0 + y1) / 2
    d = (y1 - y0) / 2
    h = sp.sqrt(R ** 2 - d ** 2)
    dx = m - Cx[6]
    dy = h - Cy[6]
    exprs.append(sp.sqrt(dx ** 2 + dy ** 2) - R)
    vs = (a0, a1, a2, a3, y0, y1, R)

    zc = [mpf(v) for v in CORE.xC] + [mpf(CORE.RSTAR)]
    subs = dict(zip(vs, [sp.Float(v, 50) for v in zc]))

    print('=== R20-TC-AUDIT 3/3: all 5 residuals, Grad/Hess vs nested dual ===')
    Jsym = np.zeros((5, 7)); Hsym = np.zeros((5, 7, 7))
    for m_ in range(5):
        for i in range(7):
            Jsym[m_, i] = float(sp.N(sp.diff(exprs[m_], vs[i]).subs(subs), 40))
            for j in range(7):
                Hsym[m_, i, j] = float(sp.N(sp.diff(exprs[m_], vs[i], vs[j]).subs(subs), 40))
    # nested dual
    J_ad = np.zeros((5, 7)); H_ad = np.zeros((5, 7, 7))
    for i in range(7):
        xd = [K32.Dual(zc[k], [mpf(int(j == k)) for j in range(7)]) for k in range(7)]
        f = K32.res5(xd[0:4], xd[4], xd[5], xd[6], K32.BK_DMPF)
        for m_ in range(5):
            J_ad[m_, i] = float(f[m_].d[i])
    for i in range(7):
        for j in range(7):
            f = S33.f5_nested(zc, i, j)
            for m_ in range(5):
                H_ad[m_, i, j] = float(f[m_].d[i].d[j])
    print('   gradient  : max |sympy - AD| over all 5x7 = %.3e' % np.abs(Jsym - J_ad).max())
    print('   Hessian   : max |sympy - AD| over all 5x7x7 = %.3e' % np.abs(Hsym - H_ad).max())
    print('   Hessian symmetry per residual: %s'
          % [float(np.abs(Hsym[m_] - Hsym[m_].T).max()) for m_ in range(5)])

    # ---------- rank / independence
    rJ = np.linalg.matrix_rank(Jsym, tol=1e-10)
    print('   rank of the symbolic 5x7 Jacobian at the TC point = %d (expect 5)' % rJ)
    sv = np.linalg.svd(Jsym, compute_uv=False)
    print('   singular values: %s' % ['%.6e' % v for v in sv])
    print('   a3-column norms (the symmetric direction): %s'
          % ['%.3e' % abs(Jsym[m_, 3]) for m_ in range(5)])
    # ---------- symmetry structure
    print()
    print('   a0<->a1 symmetry check per residual: max|J[:,0]-J[:,1]| = %s'
          % ['%.2e' % abs(Jsym[m_, 0] - Jsym[m_, 1]) for m_ in range(5)])
    print('   a3 row/column vanishing per residual: max|J[:,3]| = %s'
          % ['%.2e' % max(abs(Jsym[m_, 3]), np.abs(Hsym[m_, 3]).max()) for m_ in range(5)])
    out = dict(J_sympy=Jsym.tolist(), J_ad=J_ad.tolist(),
               max_grad_diff=float(np.abs(Jsym - J_ad).max()),
               max_hess_diff=float(np.abs(Hsym - H_ad).max()),
               H_sympy=Hsym.tolist(), rank=int(rJ), sv=[float(v) for v in sv])
    (HERE / 'r20_tc_audit3.json').write_text(json.dumps(out, indent=1))
    print('   saved r20_tc_audit3.json')


if __name__ == '__main__':
    main()
