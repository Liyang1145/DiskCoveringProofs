"""R20-TC-AUDIT 1/2: independent SymPy/analytic re-derivation of `tc_s32_kraw.res5`.

Source under audit (read-only):
  * `research-2026/session2/n11tc/py/tc_s32_kraw.py` lines 121-154   (res5)
  * `research-2026/session2/n11tc/py/tc_s33_kkt.py` lines 130-160    (nested dual, J12_iv)
  * `research-2026/team-current/lead/repair_tc_krawczyk.py`          (Krawczyk wrapper)

WHAT IS CHECKED
  The 5 residuals of `res5` are re-derived from the explicit geometry (9 angle copies, angular
  layout, `rho_k = cos(a_k) - sqrt(R^2 - sin^2 a_k)`, centre walk, and the last
  "sqrt-circle" residual built from the midpoint (m, h) of the two pinned radii).  Each residual
  is differentiated SYMBOLICALLY (different representation: SymPy exact expressions) to obtain
  the gradient and Hessian as symbolic expressions, which are then evaluated to 50 digits.

  The audit target is the LAST residual f5 (the sqrt-circle one, `B.Q(...) - R` with
  `h = sqrt(R^2 - d^2)`), for its full 7-gradient and 7x7 Hessian.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_audit.py
"""
import json, math, sys
from pathlib import Path

import sympy as sp

HERE = Path(__file__).parent
TC = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\session2\n11tc\py')

# ----------------------------------------------------------------- independent symbolic model
a0, a1, a2, a3, y0, y1, R = sp.symbols('a0 a1 a2 a3 y0 y1 R', real=True)


def residual_exprs():
    """the 5 residuals of `res5`, written independently from the explicit construction."""
    a4 = sp.pi - 2 * (a0 + a1 + a2 + a3)
    a = [a0, a1, a2, a3, a4, a3, a2, a1, a0]
    # rho_k = cos(a_k) - sqrt(R^2 - sin^2(a_k))
    rho = [sp.cos(ak) - sp.sqrt(R ** 2 - sp.sin(ak) ** 2) for ak in a]
    # theta walk: theta_4 = 0 ; theta_k = theta_{k-1} + a_{k-1} + a_k (k=5..8)
    #              theta_k = theta_{k+1} - (a_k + a_{k+1})      (k=3..0)
    th = [None] * 9
    th[4] = sp.Integer(0)
    for k in range(5, 9):
        th[k] = th[k - 1] + a[k - 1] + a[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (a[k] + a[k + 1])
    Cx = [rho[k] * sp.cos(th[k]) for k in range(9)]
    Cy = [rho[k] * sp.sin(th[k]) for k in range(9)]
    # U_k = C_k + C_{k+1} - (cos, sin)(th_k + a_k)
    U = []
    for k in range(9):
        k2 = (k + 1) % 9
        U.append((Cx[k] + Cx[k2] - sp.cos(th[k] + a[k]),
                  Cy[k] + Cy[k2] - sp.sin(th[k] + a[k])))
    # the four symmetric residuals: factors (k, l) with c = y1 if l==1 else y0
    out = []
    for (k, l) in [(1, 1), (2, 0), (3, 0), (8, 1)]:
        c = y1 if l == 1 else y0
        dx = U[k][0] - c
        dy = U[k][1]
        out.append(sp.sqrt(dx ** 2 + dy ** 2) - R)
    # the sqrt-circle residual
    m = (y0 + y1) / 2
    d = (y1 - y0) / 2
    h = sp.sqrt(R ** 2 - d ** 2)
    dx = m - Cx[6]
    dy = h - Cy[6]
    out.append(sp.sqrt(dx ** 2 + dy ** 2) - R)
    return out


def main():
    exprs = residual_exprs()
    print('=== R20-TC-AUDIT 1/2: symbolic re-derivation of res5 ===')
    print('   5 residuals built from explicit geometry (SymPy); target = residual #5 (sqrt-circle)')
    f5 = exprs[4]
    # sanity: the symbolic residual must reduce to the numeric pipeline's value at the TC point
    sys.path.insert(0, str(TC))
    import tc_core as CORE
    pt = [sp.Float(CORE.xC[0], 50), sp.Float(CORE.xC[1], 50), sp.Float(CORE.xC[2], 50),
          sp.Float(CORE.xC[3], 50), sp.Float(CORE.xC[4], 50), sp.Float(CORE.xC[5], 50),
          sp.Float(CORE.RSTAR, 50)]
    print('   TC point xC = %s, RSTAR = %.16f' % (CORE.xC, CORE.RSTAR))
    for i, e in enumerate(exprs):
        print('   residual %d at the TC point = %s' % (i + 1, sp.N(e.subs(dict(zip(
            [a0, a1, a2, a3, y0, y1, R], pt))), 25)))
    # ---- symbolic gradient and Hessian of the target residual
    print()
    print('   computing the symbolic gradient (7) and Hessian (7x7) of residual #5 ...')
    g = [sp.diff(f5, v) for v in (a0, a1, a2, a3, y0, y1, R)]
    H = [[sp.diff(g[i], v) for v in (a0, a1, a2, a3, y0, y1, R)] for i in range(7)]
    subs = dict(zip([a0, a1, a2, a3, y0, y1, R], pt))
    gnum = [sp.N(x.subs(subs), 40) for x in g]
    Hnum = [[sp.N(x.subs(subs), 40) for x in row] for row in H]
    print('   gradient of residual #5 at the TC point:')
    for i, v in enumerate(gnum):
        print('      d/da%d = %s' % (i, v) if i < 4 else
              ('      d/dy0 = %s' % v if i == 4 else
               ('      d/dy1 = %s' % v if i == 5 else '      d/dR  = %s' % v)))
    print('   Hessian diagonal:')
    for i in range(7):
        print('      H[%d][%d] = %s' % (i, i, Hnum[i][i]))
    # dump the required audit payload
    out = dict(TC_point=[float(v) for v in CORE.xC] + [float(CORE.RSTAR)],
               symbolic_residual_5=str(f5),
               residual_values_at_TC=[str(sp.N(e.subs(subs), 30)) for e in exprs],
               grad5=[str(v) for v in gnum],
               hess5=[[str(v) for v in row] for row in Hnum])
    (HERE / 'r20_tc_symbolic.json').write_text(json.dumps(out, indent=1))
    print('   saved r20_tc_symbolic.json')


if __name__ == '__main__':
    main()
