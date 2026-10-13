"""R20-AK: measure the TRUE z-dependence of each factor at the candidate, against the affine form.

Subtlety the lead flagged: the factor is  f_k(X;z) = base(X) + max_{y} [A(X_ang;z) y^2 + B(X_ang;z) y],
so it is PIECEWISE linear in z, not linear at a fixed tuple.  At the CANDIDATE the radius copy
saturates (y = 1 for all faces/switches; u = v = 1 for all rings), so on the active branch the
mapping IS affine and the coefficient is the derivative along that branch:

    face t   : a_k[j] = partial_j ( A(1) + B(1) ) = partial_j [ 2 R^2 prod sin + sum dd sin^2 ]
    switch i : a_k[j] = partial_j ( A(1) + B(1) )
    ring i   : a_k[j] = partial_j f_k(alpha,1,1)   (no max involved)

This script measures d f_k / d z_j by perturbing z IN THE KERNEL at the candidate and compares with
the coefficients of `lin_form`, which pins every index mapping (including the ETA term for
rings 3..8 and the switch RR copy pattern).

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_branch_calib.py
"""
import json, math, sys
import numpy as np
from pathlib import Path

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
sys.path.insert(0, str(HERE))
from r20_family78 import load_candidate, lin_form

R_CAND = 0.3799838531198388


def main():
    from r20_factor_probe import Model
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    m = Model('q0_lower375_dual_0_4.json', R, 'z')
    z0 = m.z.copy()
    print('=== measured kernel response at the CANDIDATE vs lin_form coefficients ===')
    worst = 0.0; report = {}
    for k in range(29):
        if k < 11:
            X = p0.copy()
            # measure the FULL kernel value (with its internal radius max) as z varies
            def kernel(zz):
                m.z = zz
                return m.face_val(k, X[3 * k], X[3 * k + 1])[0]
        elif k < 20:
            X = p0.copy(); bi = k - 11
            def kernel(zz):
                m.z = zz
                return m.switch_val(bi, X[33 + bi])[0]
        else:
            X = p0.copy(); i = k - 20
            def kernel(zz):
                m.z = zz
                return m.ring_val(i, X[51 + 3 * i], X[51 + 3 * i + 1], X[51 + 3 * i + 2])
        base = kernel(z0.copy())
        arow, bconst = lin_form(k, p0, C)
        dev = 0.0; arg = None
        for j in range(121):
            h = 1e-7
            zp = z0.copy(); zp[j] += h
            vp = kernel(zp)
            dd = (vp - base) / h - arow[j]
            if abs(dd) > abs(dev):
                dev = dd; arg = j
        report[k] = (float(dev), arg)
        if abs(dev) > 1e-6:
            print('  factor %2d: max coefficient deviation %+.3e at column %s' % (k, dev, arg))
        worst = max(worst, abs(dev))
    print('overall max deviation = %.3e' % worst)
    if worst > 1e-6:
        k = max(report, key=lambda t: abs(report[t][0]))
        j = report[k][1]
        print('worst factor %d, column %d: measured %.6f  lin_form %.6f'
              % (k, j, lin_form(k, p0, C)[0][j],
                 lin_form(k, p0, C)[0][j] + report[k][0]))
    # ETA spot check for rings 0..8
    print()
    print('ETA column (72) coefficient per ring factor, measured vs lin_form:')
    for i in range(9):
        k = 20 + i
        X = p0.copy()
        def kernel(zz):
            m.z = zz
            return m.ring_val(i, X[51 + 3 * i], X[51 + 3 * i + 1], X[51 + 3 * i + 2])
        h = 1e-7
        zp = z0.copy(); zp[LAM_ETA := 72] += h
        vp = kernel(zp)
        print('   ring%d: measured %+.6f   lin_form %+.6f' %
              (i, (vp - kernel(z0.copy())) / h, lin_form(k, p0, C)[0][72]))
    m.z = z0


if __name__ == '__main__':
    main()
