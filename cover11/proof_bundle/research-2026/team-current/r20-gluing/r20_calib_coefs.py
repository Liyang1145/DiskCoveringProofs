"""R20-AJ: per-factor calibration of the affine form against the lead kernel's factor formulas.

For each of the 29 factors and for a RANDOM (non-saturating) interior tuple we check
    d f_k / d z_j   measured on the kernel formula  ==  the j-th entry of lin_form(k,X)
for all 121 pressure columns.  The kernel formula is `r20_factor_probe.Model.{face,switch,ring}_val`,
which is a faithful re-implementation of the lead kernels' per-factor form.

This catches the coefficient bugs the lead flagged (missing b-terms are handled by the affine rows
separately; here the a_k coefficients must match exactly).

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_calib_coefs.py
"""
import json, math, sys
import numpy as np
from pathlib import Path

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
sys.path.insert(0, str(HERE))
from r20_family78 import load_candidate, lin_form

R_CAND = 0.3799838531198388


def kernel_val(m, k, X):
    if k < 11:
        return m.face_val(k, X[3 * k], X[3 * k + 1])[0]
    if k < 20:
        return m.switch_val(k - 11, X[33 + k - 11])[0]
    i = k - 20
    return m.ring_val(i, X[51 + 3 * i], X[51 + 3 * i + 1], X[51 + 3 * i + 2])


def main():
    from r20_factor_probe import Model
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    m = Model('q0_lower375_dual_0_4.json', R, 'z')
    z0 = m.z.copy()
    rng = np.random.default_rng(1)
    qmin = 4 * math.sin(math.pi - 8 * math.asin(R)) ** 2 / R ** 2
    worst = 0.0; per = {}
    for k in range(29):
        X = p0.copy()
        if k < 11:
            a = rng.uniform(0.2, 2.0); b = rng.uniform(0.2, 2.0); y = rng.uniform(0.2, 0.9)
            X[3 * k:3 * k + 3] = (a, b, y)
        elif k < 20:
            bi = k - 11
            X[33 + bi] = rng.uniform(0.2, 1.4); X[42 + bi] = rng.uniform(0.2, 0.9)
        else:
            i = k - 20
            while True:
                a = rng.uniform(0.5, 2.5); u = rng.uniform(0.2, 1.0); v = rng.uniform(0.2, 1.0)
                if (u - v) ** 2 + 4 * u * v * math.sin(a / 2) ** 2 >= qmin:
                    break
            X[51 + 3 * i:51 + 3 * i + 3] = (a, u, v)
        arow, bconst = lin_form(k, X, C)
        base = kernel_val(m, k, X)
        dev = 0.0
        for j in range(121):
            h = 1e-7
            zp = z0.copy(); zp[j] += h
            m.z = zp
            vp = kernel_val(m, k, X)
            m.z = z0
            d = (vp - base) / h - arow[j]
            dev = max(dev, abs(d))
        per[k] = float(dev); worst = max(worst, dev)
        if dev > 1e-7:
            print('  factor %2d: max coefficient deviation %.3e' % (k, dev))
    print('overall max |kernel d f_k/dz_j  -  lin_form coefficient| = %.3e' % worst)
    bad = sorted(per.items(), key=lambda kv: -kv[1])[:8]
    print('worst factors: %s' % [(k, '%.2e' % v) for k, v in bad])


if __name__ == '__main__':
    main()
