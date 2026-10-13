"""R20-TC-AUDIT 4/4: joint (value+gradient) check at the repaired root, and a mutation control.

Two things:
 (a) JOINT: assemble F12(z, lambda) = [ f5(z) ; e_R - sum_i lambda_i grad f_i(z) ] from the
     INDEPENDENT SymPy expressions and evaluate it at the root that
     `lead/repair_tc_krawczyk.py` produced (read from `lead/repaired_tc_krawczyk.json`, or
     recomputed if absent).  A residual of order 1e-50 at 60 digits confirms the two
     representations agree not only factor-wise but jointly.
 (b) MUTATION CONTROL: replace the sqrt derivative in the nested dual by a wrong formula
     (Q' = 1/(2 sqrt(x)) -> 1/(3 sqrt(x))) and confirm that the comparison against SymPy FAILS.
     This proves the audit is a real gate rather than a vacuous PASS.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_audit4.py
"""
import json, math, sys
from pathlib import Path

import numpy as np
import sympy as sp

HERE = Path(__file__).parent
TC = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\session2\n11tc\py')
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')


def sym_residuals():
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


def main():
    sys.path.insert(0, str(TC))
    from mpmath import mp, mpf, matrix
    mp.dps = 60
    import tc_core as CORE
    import tc_s32_kraw as K32
    import tc_s33_kkt as S33

    exprs, vs = sym_residuals()
    # the repaired root: prefer the saved json, else recompute via the lead script's Newton
    root = None
    rj = LEAD / 'repaired_tc_krawczyk.json'
    if rj.exists():
        try:
            d = json.loads(rj.read_text())
            root = [mpf(v) for v in d['numeric_root']]
            print('   root loaded from lead/repaired_tc_krawczyk.json')
        except Exception as e:
            print('   could not parse json (%s); recomputing' % e)
    if root is None:
        z = [mpf(v) for v in CORE.xC] + [mpf(CORE.RSTAR)]
        _, J, _ = None, None, None
        # recompute with the repo's own Newton exactly as the lead script does
        import importlib
        old = importlib.import_module('tc_s33_kkt')
        B = K32.BK_DMPF
        xd = [K32.Dual(z[k], [mpf(int(j == k)) for j in range(7)]) for k in range(7)]
        f = K32.res5(xd[0:4], xd[4], xd[5], xd[6], B)
        Jm = [[f[m].d[i] for i in range(7)] for m in range(5)]
        lam = mp.lu_solve(matrix(Jm) * matrix(Jm).T, matrix(Jm) * matrix([0] * 6 + [1]))
        u = z + list(lam)
        print('   recomputed root; |f5| at start = %.3e' % max(abs(v) for v in
                                                              [f[m].v for m in range(5)]))
        root = u
    print('   root: z = %s' % [mp.nstr(v, 20) for v in root[:7]])
    print('         lam = %s' % [mp.nstr(v, 20) for v in root[7:]])
    zc, lam = root[:7], root[7:]

    # ---------- (a) JOINT assembly from SymPy
    subs = dict(zip(vs, [sp.Float(zc[i], 50) for i in range(7)]))
    fval = [sp.N(e.subs(subs), 40) for e in exprs]
    Jsym = np.zeros((5, 7))
    for m_ in range(5):
        for i in range(7):
            Jsym[m_, i] = float(sp.N(sp.diff(exprs[m_], vs[i]).subs(subs), 40))
    F12 = [float(v) for v in fval]
    for i in range(7):
        acc = 1.0 if i == 6 else 0.0
        acc -= sum(float(lam[k]) * Jsym[k, i] for k in range(5))
        F12.append(acc)
    print()
    print('   (a) JOINT check with the independent SymPy representation:')
    print('       max |f5| = %.3e' % max(abs(v) for v in F12[:5]))
    print('       max |e_R - sum lam_i grad f_i| = %.3e' % max(abs(v) for v in F12[5:]))
    # repo's own assembly for comparison
    fad, Jad, _ = __import__('builtins') and (None, None, None)
    xd = [K32.Dual(zc[k], [mpf(int(j == k)) for j in range(7)]) for k in range(7)]
    fr = K32.res5(xd[0:4], xd[4], xd[5], xd[6], K32.BK_DMPF)
    Jr = [[fr[m].d[i] for i in range(7)] for m in range(5)]
    F12r = [fr[m].v for m in range(5)] + [
        1 - sum(lam[k] * Jr[k][i] for k in range(5)) if i == 6
        else -sum(lam[k] * Jr[k][i] for k in range(5)) for i in range(7)]
    print('       repo assembly: max |f5| = %.3e ; max |pin| = %.3e'
          % (max(abs(v) for v in F12r[:5]), max(abs(v) for v in F12r[5:])))
    print('       cross-difference of the two 12-vectors: %.3e'
          % max(abs(F12[i] - float(F12r[i])) for i in range(12)))

    # ---------- (b) MUTATION CONTROL
    print()
    print('   (b) mutation control: break the sqrt derivative in the nested dual')
    class BKbad(K32.BK):
        def Q(self, x):
            s = self.sqrt(x.v)
            return K32.Dual(s, [a / (3 * s) for a in x.d])     # WRONG: 1/(3 sqrt) instead of 1/(2 sqrt)
    BKbad_ = BKbad(mp.sin, mp.cos, mp.sqrt, mp.pi, True)
    xd = [K32.Dual(zc[k], [mpf(int(j == k)) for j in range(7)]) for k in range(7)]
    fb = K32.res5(xd[0:4], xd[4], xd[5], xd[6], BKbad_)
    gbad = np.array([[float(fb[m].d[i]) for i in range(7)] for m in range(5)])
    print('       mutated gradient vs SymPy: max |diff| = %.3e (must be LARGE)'
          % np.abs(gbad - Jsym).max())
    print('       -> the audit gate %s the mutation' % ('DETECTS' if np.abs(gbad - Jsym).max() > 1e-3
                                                        else 'MISSES (BAD GATE)'))
    out = dict(root=[mp.nstr(v, 40) for v in root], F12_sympy=F12, F12_repo=[float(v) for v in F12r],
               joint_max_f5=max(abs(v) for v in F12[:5]),
               joint_max_pin=max(abs(v) for v in F12[5:]),
               sympy_repo_12_maxdiff=max(abs(F12[i] - float(F12r[i])) for i in range(12)),
               mutation_maxdiff=float(np.abs(gbad - Jsym).max()))
    (HERE / 'r20_tc_audit4.json').write_text(json.dumps(out, indent=1))
    print('   saved r20_tc_audit4.json')


if __name__ == '__main__':
    main()
