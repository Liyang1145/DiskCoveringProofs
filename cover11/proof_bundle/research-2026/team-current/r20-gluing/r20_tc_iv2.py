"""R20-TC-IV2 (corrected): full-12D interval Krawczyk enclosure, independent `res5` source.

FIXES over the previous version (lead audit, both load-bearing):
  (1) the box is now  U_i = iv.mpf(c_hex_i) + iv.mpf([-rad, rad])  for ALL 12 coordinates -- the
      previous version built the value box from `float(z +- rad)`, whose outward-rounded endpoints
      do not enclose the true box;
  (2) the Hessian block is multiplied by the BOX variables U[7+m] (the lambda coordinates), not by
      the point values numeric_root[7:]; the previous J was therefore not a full-12D enclosure.

Also:
  * F(center) uses the exact dyadic center coordinates (c_hex), not a re-parsed numeric_root;
  * the containment comparison is done on  K - c  against  (-rad, rad), avoiding any float
    endpoint arithmetic;
  * full hex output + source hashes are recorded;
  * NO verification of Y is attempted: any fixed dyadic Y is legal here -- ||I - Y J(U)||_inf < 1
    already yields Y J invertible and hence Y invertible, so an extra inverse-enclosure step would
    be useless.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_iv2.py
"""
import hashlib
import json
import sys
from pathlib import Path

import numpy as np
import sympy as sp
from mpmath import iv, mp, mpf

HERE = Path(__file__).parent
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
TC = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\session2\n11tc\py')
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(TC))
from r20_tc_iv1 import symbolic_res5, iv_modules, to_iv

N = 12


def exact_mpf(hexstr):
    """exact mpf of a dyadic hex float: hex -> float (exact) -> Fraction -> exact decimal -> mpf
    (mpf parsing is correctly rounded at the current dps, and the decimal is exact)."""
    from fractions import Fraction
    f = Fraction(float.fromhex(hexstr))
    return mpf(f.numerator) / mpf(f.denominator)


def main():
    iv.dps = 40
    exprs, vs = symbolic_res5()
    mods = iv_modules()
    ffun = [sp.lambdify(vs, e, modules=mods) for e in exprs]
    gfun = [[sp.lambdify(vs, sp.diff(exprs[m], vs[i]), modules=mods) for i in range(7)]
            for m in range(5)]
    hfun = [[[sp.lambdify(vs, sp.diff(exprs[m], vs[i], vs[j]), modules=mods) for j in range(7)]
             for i in range(7)] for m in range(5)]

    d = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text())
    c_hex = d['certificate']['center_hex']
    r_hex = d['certificate']['radius_hex']
    c = [float.fromhex(h) for h in c_hex]
    rad = float.fromhex(r_hex)

    print('=== R20-TC-IV2 (corrected): full-12D interval Krawczyk enclosure ===')
    print('   radius hex: %s (rad = %.17g)' % (r_hex, rad))
    iv.dps = 40
    print('   iv.dps = %d' % iv.dps)

    # ---- (1) the true box for ALL 12 coordinates
    U = [iv.mpf([exact_mpf(c_hex[i]) - mpf(rad), exact_mpf(c_hex[i]) + mpf(rad)])
         for i in range(N)]
    print('   box = [exact_mpf(center_hex_i) - rad, exact_mpf(center_hex_i) + rad], all 12')
    for i in (0, 6, 7):
        print('      U[%d] = [%s, %s]' % (i, iv.nstr(U[i].a, 18), iv.nstr(U[i].b, 18)))
    print('   all coordinates nonempty: %s' % all(U[i].a <= U[i].b for i in range(N)))

    iv.dps = 40          # re-set after all backend imports (tc_s33_kkt sets iv.dps=30 at import)
    U7 = U[:7]
    # ---- (2) interval Jacobian: first-order block + Hessian block with BOX lambda multipliers
    J = [[iv.mpf(0) for _ in range(N)] for _ in range(N)]
    for m in range(5):
        for i in range(7):
            J[m][i] = to_iv(gfun[m][i](*U7))
    for i in range(7):
        for j in range(7):
            acc = iv.mpf(0)
            for m in range(5):
                acc -= U[7 + m] * to_iv(hfun[m][i][j](*U7))   # box multipliers
            J[5 + i][j] = acc
    for i in range(7):
        for m in range(5):
            J[5 + i][7 + m] = -J[m][i]
    # ---- F(center) with the exact dyadic center
    c7 = [iv.mpf(exact_mpf(c_hex[i])) for i in range(7)]
    fc = [to_iv(ffun[m](*c7)) for m in range(5)]
    fp = []
    for i in range(7):
        acc = iv.mpf(1) if i == 6 else iv.mpf(0)
        for m in range(5):
            acc -= iv.mpf(exact_mpf(c_hex[7 + m])) * to_iv(gfun[m][i](*c7))
        fp.append(acc)
    F0 = fc + fp
    print()
    print('   F(center) intervals (exact dyadic center):')
    for i in range(N):
        print('      F[%2d] = %s' % (i, iv.nstr(F0[i], 14)))
    # ---- Y: fixed dyadic float inverse of the midpoint Jacobian (any fixed dyadic Y is legal)
    c7f = [mpf(v) for v in c[:7]]
    import tc_s32_kraw as K32
    import tc_s33_kkt as S33
    xd = [K32.Dual(c7f[k], [mpf(int(j == k)) for j in range(7)]) for k in range(7)]
    fr = K32.res5(xd[0:4], xd[4], xd[5], xd[6], K32.BK_DMPF)
    Jm = np.zeros((N, N))
    for m in range(5):
        for i in range(7):
            Jm[m, i] = float(fr[m].d[i])
    for i in range(7):
        for j in range(7):
            Jm[5 + i, j] = -sum(c[7 + m] * float(S33.f5_nested(c7f, i, j)[m].d[i].d[j])
                                for m in range(5))
    for i in range(7):
        for m in range(5):
            Jm[5 + i, 7 + m] = -Jm[m, i]
    Y = [[iv.mpf(float(v)) for v in row] for row in np.linalg.inv(Jm)]
    print()
    print('   Y = fixed dyadic float inverse of the midpoint Jacobian (no enclosure attempted;')
    print('   ||I - Y J(U)|| < 1 alone yields Y J invertible and hence Y invertible).')
    # ---- E = I - Y J(U), Q, K - c
    E = [[iv.mpf(int(i == j)) - sum(Y[i][k] * J[k][j] for k in range(N)) for j in range(N)]
         for i in range(N)]
    Q = max(sum(max(abs(v.a), abs(v.b)) for v in row) for row in E)
    print()
    print('   contraction infinity norm  Q = max_i sum_j |(I - Y J(U))_ij| = %s' % iv.nstr(Q, 22))
    print('   Q < 1 : %s' % (Q < 1))
    D = [iv.mpf([-rad, rad]) for _ in range(N)]
    Kc = []
    for i in range(N):
        acc = -sum(Y[i][k] * F0[k] for k in range(N))
        acc += sum(E[i][j] * D[j] for j in range(N))
        Kc.append(acc)
    print()
    print('   K - c  vs the box (-rad, rad)   [comparison on the shifts, no float endpoints]')
    ok = True
    for i in range(N):
        inside = (Kc[i].a > -rad) and (Kc[i].b < rad)
        ok = ok and inside
        print('      i=%2d  K-c = [%s, %s]   strict-inside %s'
              % (i, iv.nstr(Kc[i].a, 14), iv.nstr(Kc[i].b, 14), inside))
    print()
    print('   VERDICT: strict inclusion K(U) subset int(U): %s ; Q < 1 : %s' % (ok, Q < 1))
    lead = d['certificate']
    diff = max(abs(float(mpf(F0[i].a if s == 0 else F0[i].b) - mpf(lead['F_center'][i][s])))
               for i in range(N) for s in (0, 1))
    print('   control vs lead certificate: max |F_center diff| = %.3e ; lead Q = %s'
          % (diff, lead['contraction_inf']))
    print('   control: lead inclusion %s ; lead negative control %s'
          % (lead['pass_inclusion'], d['negative_control']['pass_inclusion']))

    def sh(p):
        return hashlib.sha256(Path(p).read_bytes()).hexdigest()
    hashes = {'r20_tc_iv2.py': sh(HERE / 'r20_tc_iv2.py'),
              'r20_tc_iv1.py': sh(HERE / 'r20_tc_iv1.py'),
              'lead/repair_tc_krawczyk.py': sh(LEAD / 'repair_tc_krawczyk.py'),
              'lead/repaired_tc_krawczyk.json': sh(LEAD / 'repaired_tc_krawczyk.json'),
              'tc_s32_kraw.py': sh(TC / 'tc_s32_kraw.py'),
              'tc_s33_kkt.py': sh(TC / 'tc_s33_kkt.py')}
    print()
    print('   source hashes:')
    for k, v in hashes.items():
        print('      %-34s %s' % (k, v))
    out = dict(center_hex=c_hex, radius_hex=r_hex, iv_dps=int(iv.dps),
               F_center=[iv.nstr(v, 20) for v in F0],
               Q=iv.nstr(Q, 25), Q_lt_1=bool(Q < 1), inclusion=bool(ok),
               K_minus_c=[(iv.nstr(v.a, 20), iv.nstr(v.b, 20)) for v in Kc],
               lead_Q=lead['contraction_inf'], lead_inclusion=lead['pass_inclusion'],
               lead_negative_control=d['negative_control']['pass_inclusion'],
               F_center_maxdiff_vs_lead=float(diff), source_hashes=hashes)
    (HERE / 'r20_tc_iv2.json').write_text(json.dumps(out, indent=1, default=str))
    print('   saved r20_tc_iv2.json')


if __name__ == '__main__':
    main()
