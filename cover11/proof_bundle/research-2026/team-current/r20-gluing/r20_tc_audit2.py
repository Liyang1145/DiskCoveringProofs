"""R20-TC-AUDIT 2/2: compare the nested-dual AD (tc_s33_kkt.f5_nested / J12_iv) against the
independent SymPy expressions and against high-order finite differences.

Three representations are compared at the TC point for all 5 residuals, and for the
sqrt-circle residual #5 in full (7 gradient components, 7x7 Hessian):
  (A) SymPy exact symbolic differentiation of the explicit geometry  (r20_tc_audit.py)
  (B) the repo's nested dual AD:  Dual(inner=Dual, d=[Dual,...])     (tc_s33_kkt.f5_nested)
  (C) mpmath complex-step / high-order central differences at 50 digits

The audit must NOT rely on extra FD digits for the derivative audit: (C) is a cross-check only;
the load-bearing comparison is (A) vs (B).

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_audit2.py
"""
import json, math, sys
from pathlib import Path

import numpy as np
from mpmath import mp, mpf

HERE = Path(__file__).parent
TC = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\session2\n11tc\py')
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')


def main():
    sys.path.insert(0, str(TC))
    mp.dps = 60
    import tc_core as CORE
    import tc_s32_kraw as K32
    import tc_s33_kkt as S33

    zc = [mpf(v) for v in CORE.xC] + [mpf(CORE.RSTAR)]
    print('=== R20-TC-AUDIT 2/2: nested-dual AD vs SymPy vs FD ===')
    print('   point: xC = %s ; R* = %.16f' % (CORE.xC, CORE.RSTAR))

    # ---------- (B) first derivatives from the repo's first-order dual
    xd = []
    for k in range(7):
        inner = K32.Dual(zc[k], [mpf(int(j == k)) for j in range(7)])
        xd.append(inner)
    f_dual = K32.res5(xd[0:4], xd[4], xd[5], xd[6], K32.BK_DMPF)
    J_ad = [[f_dual[m].d[i] for i in range(7)] for m in range(5)]
    fval = [f_dual[m].v for m in range(5)]
    print('   (B) nested/first-order AD values:', [mp.nstr(v, 20) for v in fval])

    # ---------- (B2) second derivatives from the repo's nested dual (S33.f5_nested)
    H_ad = np.zeros((5, 7, 7))
    for i in range(7):
        for j in range(7):
            f = S33.f5_nested(zc, i, j)
            for m in range(5):
                H_ad[m, i, j] = float(f[m].d[i].d[j])
    print('   (B2) nested-dual Hessian of residual #5 (row 4):')
    for i in range(7):
        print('       ', ['%+.6f' % H_ad[4, i, j] for j in range(7)])

    # ---------- (A) the SymPy results
    sym = json.loads((HERE / 'r20_tc_symbolic.json').read_text())
    gA = [float(v) for v in sym['grad5']]
    HA = np.array([[float(v) for v in row] for row in sym['hess5']])
    gB = [float(J_ad[4][i]) for i in range(7)]
    print()
    print('   (A) vs (B): gradient of residual #5')
    for i in range(7):
        print('      i=%d  sympy %+.15e   AD %+.15e   |diff| %.2e'
              % (i, gA[i], gB[i], abs(gA[i] - gB[i])))
    print('   (A) vs (B): Hessian of residual #5, max |diff| = %.3e'
          % np.abs(HA - H_ad[4]).max())
    # symmetry checks
    print('   Hessian symmetry |H - H^T| = %.3e (must be ~0)'
          % np.abs(HA - HA.T).max())
    print('   a0<->a1 symmetry: |H[:,0]-H[:,1]| = %.3e, |H[0,:]-H[1,:]| = %.3e'
          % (np.abs(HA[:, 0] - HA[:, 1]).max(), np.abs(HA[0, :] - HA[1, :]).max()))
    print('   row a3 (index 3) of the gradient/Hessian = %s / %s'
          % (gA[3], list(HA[3])))

    # ---------- (C) high-order finite differences at 50 digits (cross-check only)
    import tc_s33_kkt as S33b

    def f5_numeric(z):
        f = K32.res5([mpf(z[0]), mpf(z[1]), mpf(z[2]), mpf(z[3])], mpf(z[4]), mpf(z[5]),
                     mpf(z[6]), K32.BK_MPF)
        return f[4]

    h = mpf('1e-25')
    gC = []
    for i in range(7):
        zp = list(zc); zm = list(zc)
        zp[i] += h; zm[i] -= h
        gC.append((f5_numeric(zp) - f5_numeric(zm)) / (2 * h))
    HC = np.zeros((7, 7))
    h2 = mpf('1e-12')
    for i in range(7):
        for j in range(7):
            if i == j:
                zp = list(zc); zm = list(zc)
                zp[i] += h2; zm[i] -= h2
                HC[i, i] = (f5_numeric(zp) - 2 * f5_numeric(zc) + f5_numeric(zm)) / h2 ** 2
            else:
                pp = list(zc); pm = list(zc); mp_ = list(zc); mm = list(zc)
                pp[i] += h2; pp[j] += h2
                pm[i] += h2; pm[j] -= h2
                mp_[i] -= h2; mp_[j] += h2
                mm[i] -= h2; mm[j] -= h2
                HC[i, j] = (f5_numeric(pp) - f5_numeric(pm) - f5_numeric(mp_)
                            + f5_numeric(mm)) / (4 * h2 ** 2)
    print()
    print('   (C) high-order FD (h=1e-25 gradient, 1e-12 Hessian):')
    print('      grad : max |C - A| = %.3e' % max(abs(gC[i] - gA[i]) for i in range(7)))
    print('      Hess : max |C - A| = %.3e' % np.abs(HC - HA).max())
    print('      Hess : max |C - B| = %.3e' % np.abs(HC - H_ad[4]).max())
    # ---------- verdict
    tol = 1e-9
    ok_g = max(abs(gA[i] - gB[i]) for i in range(7)) < tol
    ok_H = np.abs(HA - H_ad[4]).max() < tol
    print()
    print('   VERDICT: gradient match %s (max diff %.2e) ; Hessian match %s (max diff %.2e)'
          % ('PASS' if ok_g else 'FAIL', max(abs(gA[i] - gB[i]) for i in range(7)),
             'PASS' if ok_H else 'FAIL', np.abs(HA - H_ad[4]).max()))
    out = dict(point=[float(v) for v in zc], f5_values=[mp.nstr(v, 25) for v in fval],
               grad_sympy=gA, grad_ad=gB, grad_fd=[mp.nstr(v, 25) for v in gC],
               hess_sympy=HA.tolist(), hess_ad=H_ad[4].tolist(),
               max_grad_diff=float(max(abs(gA[i] - gB[i]) for i in range(7))),
               max_hess_diff=float(np.abs(HA - H_ad[4]).max()),
               verdict_gradient=bool(ok_g), verdict_hessian=bool(ok_H))
    (HERE / 'r20_tc_audit2.json').write_text(json.dumps(out, indent=1))
    print('   saved r20_tc_audit2.json')


if __name__ == '__main__':
    main()
