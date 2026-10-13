"""R20-TC-IV 1/2: interval evaluation of the INDEPENDENT SymPy model of `res5` over the lead's
repaired Krawczyk box, and an entry-by-entry overlap control against the lead's own J12.

Framing correction (lead audit): the earlier SymPy-vs-nested-dual comparison was a POINT
comparison at 50-60 digits, not an identity proof; "0 diff" there is numerical agreement at a
point.  This file replaces that claim with an interval statement.

Construction:
  * the 5 residuals are re-derived independently in SymPy (explicit geometry; source-independent
    from tc_s32_kraw.res5), together with their exact symbolic gradient (5x7) and Hessian (5x7x7);
  * every expression is compiled with `sympy.lambdify(..., modules=<own interval backend>)`, i.e. a
    hand-written mapping of sin/cos/sqrt/pi onto `mpmath.iv` (no repo AD is imported);
  * evaluated over the closed box  [center - rad, center + rad]  with center/rad taken from
    `lead/repaired_tc_krawczyk.json` (hex floats, reused as-is);
  * the assembled independent J12 is compared entry-by-entry with the lead's J12 for OVERLAP
    (overlap is a control only; equality of intervals is neither expected nor claimed).

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_iv1.py
"""
import json, math, sys
from pathlib import Path

import numpy as np
import sympy as sp
from mpmath import iv, mp, mpf

HERE = Path(__file__).parent
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
TC = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\session2\n11tc\py')


# ------------------------------------------------------------------ independent symbolic model
def symbolic_res5():
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
    out = []
    for (k, l) in [(1, 1), (2, 0), (3, 0), (8, 1)]:
        c = y1 if l == 1 else y0
        dx = U[k][0] - c
        dy = U[k][1]
        out.append(sp.sqrt(dx ** 2 + dy ** 2) - R)
    m = (y0 + y1) / 2
    d = (y1 - y0) / 2
    h = sp.sqrt(R ** 2 - d ** 2)
    dx = m - Cx[6]
    dy = h - Cy[6]
    out.append(sp.sqrt(dx ** 2 + dy ** 2) - R)
    return out, (a0, a1, a2, a3, y0, y1, R)


def iv_modules():
    """own interval backend for lambdify: sin/cos/sqrt/pi on mpmath.iv (mpmath.iv is a module
    attribute of mpmath, not a submodule -- access it via the imported object)."""
    def _sin(x):
        return iv.sin(x)

    def _cos(x):
        return iv.cos(x)

    def _sqrt(x):
        return iv.sqrt(x)

    def _pi():
        return iv.pi
    return {'sin': _sin, 'cos': _cos, 'sqrt': _sqrt, 'pi': _pi}


def to_iv(v):
    """lambdify may fold constant subexpressions to plain python numbers; wrap them."""
    if isinstance(v, (int, float)):
        return iv.mpf(v)
    return v


def main():
    iv.dps = 40
    exprs, vs = symbolic_res5()
    mods = iv_modules()
    # compile residuals, gradient, Hessian
    ffun = [sp.lambdify(vs, e, modules=mods) for e in exprs]
    gfun = [[sp.lambdify(vs, sp.diff(exprs[m], vs[i]), modules=mods) for i in range(7)]
            for m in range(5)]
    hfun = [[[sp.lambdify(vs, sp.diff(exprs[m], vs[i], vs[j]), modules=mods) for j in range(7)]
             for i in range(7)] for m in range(5)]

    # ---- the lead's repaired center/radius (hex floats reused)
    d = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text())
    ch = d['certificate']['center_hex']; rh = d['certificate']['radius_hex']
    center = [float.fromhex(h) for h in ch]
    rad = float.fromhex(rh)
    print('=== R20-TC-IV 1/2: interval evaluation over the lead repaired box ===')
    print('   box center (12 coords) = %s' % ['%.17g' % v for v in center])
    print('   radius = %.17g' % rad)
    print('   residuals at the CENTER as intervals (independent SymPy + iv backend):')
    fcenter = []
    z = center[:7]
    for m in range(5):
        v = to_iv(ffun[m](*[iv.mpf(float(x)) for x in z]))
        fcenter.append(v)
        print('      f%d = %s' % (m + 1, iv.nstr(v, 20)))

    # ---- interval gradient (5x7) over the closed box
    lo = [iv.mpf([float(z[i]) - rad, float(z[i]) + rad]) for i in range(7)]
    print()
    print('   interval gradient entries (independent model) over the box:')
    Jiv = [[None] * 7 for _ in range(5)]
    for m in range(5):
        row = []
        for i in range(7):
            Jiv[m][i] = to_iv(gfun[m][i](*lo))
            row.append(iv.nstr(Jiv[m][i], 12))
        print('      row %d: %s' % (m + 1, row))
    # ---- interval Hessian: report norms only
    print()
    print('   interval Hessian (5x7x7) consistency checks:')
    worst_sym = mpf(0)
    for m in range(5):
        for i in range(7):
            for j in range(7):
                a = to_iv(hfun[m][i][j](*lo))
                b = to_iv(hfun[m][j][i](*lo))
                # mixed partials must be the same expression; enclosure must be nonempty
                if not (a.b < b.a or b.b < a.a):
                    worst_sym = max(worst_sym, abs(a.a - b.a), abs(a.b - b.b))
                else:
                    print('      NONOVERLAP at (%d,%d,%d)' % (m, i, j))
    print('      mixed-partial self-consistency (same expression): max endpoint spread %.3e'
          % worst_sym)
    hnorm = [[max(abs(v.a), abs(v.b)) for v in [to_iv(hfun[m][i][j](*lo)) for j in range(7)]]
             for m in range(5) for i in range(7)]
    print('      max |Hessian| entry over the box = %.6f'
          % max(max(r) for r in hnorm))

    # ---- build the independent J12 and compare with the lead's coefficients (overlap control)
    print()
    print('   assembling the independent J12 over the box and comparing with the lead code:')
    sys.path.insert(0, str(TC))
    mp.dps = 50
    iv.dps = 30
    import tc_core as CORE
    import tc_s32_kraw as K32
    import tc_s33_kkt as S33
    # the lead's own interval J12 on the same box
    U = [iv.mpf([float(z[i]) - rad, float(z[i]) + rad]) for i in range(7)]
    lam = [mpf(v) for v in d['numeric_root'][7:]]
    lam_iv = [iv.mpf(float(v)) for v in lam]
    M = S33.J12_iv(U, lam_iv)
    # independent first-order block
    ov_first = 0; sep_first = 0
    for m in range(5):
        for i in range(7):
            L = M[m][i]; Rv = Jiv[m][i]
            if L.b < Rv.a or Rv.b < L.a:
                sep_first += 1
            else:
                ov_first += 1
    print('      first-order block 5x7: %d/%d entries overlap with the lead interval J12'
          % (ov_first, ov_first + sep_first))
    # independent second-order block: -sum lam_m H_m
    worst = 0.0
    for i in range(7):
        for j in range(7):
            acc = iv.mpf(0)
            for m in range(5):
                acc -= iv.mpf(float(lam[m])) * to_iv(hfun[m][i][j](*lo))
            L = M[5 + i][j]
            if L.b < acc.a or acc.b < L.a:
                print('      second-order entry (%d,%d) does NOT overlap the lead' % (i, j))
                worst += 1
    print('      second-order block: %d entries fail overlap (0 expected)' % worst)
    out = dict(center_hex=ch, radius_hex=rh,
               f_center=[iv.nstr(v, 25) for v in fcenter],
               J_first_overlap=int(ov_first), J_first_sep=int(sep_first),
               hess_second_nonoverlap=int(worst),
               hess_max_entry=float(max(max(r) for r in hnorm)))
    (HERE / 'r20_tc_iv1.json').write_text(json.dumps(out, indent=1, default=str))
    print('   saved r20_tc_iv1.json')


if __name__ == '__main__':
    main()
