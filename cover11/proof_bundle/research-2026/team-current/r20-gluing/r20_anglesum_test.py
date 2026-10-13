"""R20-I: cheap test of the ANGLE-SUM (fan angular resource) coupling.

In the 29-factor relaxation the ring factor maximises over alpha freely, while in the primal
metric model alpha_i is DETERMINED by the neighbouring site triangles and switches:
    alpha_i = pi - sum_{faces at i} theta + b_{i-1} + b_i
(the 11 site angle-sum equations).  Imposing that relation is the "fan angular resource"
correlation that lead/FAN-DEFICIT-COORDINATES.md flags as discarded by independent-angle duals.

Measured quantity (upper bound on the coupling's gain, same direction as the other tests):
hold the argmax angles (theta,b) fixed, replace the ring's free alpha by the determined value,
re-optimise (u,v) per ring, and compare with the free ring maxima.
Diagnostic only.
"""
import json, math
import numpy as np
from pathlib import Path
from r20_factor_probe import Model, PI, maximize_all, pattern_search
from r20_residuals import assemble, residuals

HERE = Path(__file__).parent


def ring_max_uv(m, i, a, cf):
    f = lambda x: m.ring_val(i, a, x[0], x[1], cf)
    n = 61
    U = np.linspace(0, 1, n)
    A = a
    Q = (U[:, None] - U[None, :]) ** 2 + 4 * U[:, None] * U[None, :] * math.sin(A / 2) ** 2
    W = 2 * np.arcsin(np.clip(m.R * np.sqrt(np.maximum(Q, 1e-18)) / 2, 0, 1))
    beta = np.arctan2(U[None, :] * math.sin(A), U[:, None] - U[None, :] * math.cos(A))
    val = m.R2 * U[:, None] * U[None, :] * math.sin(A) / 2 + ((cf['C'] + 0.5) * W - np.sin(W) / 2)
    val = val - cf['mu'] * A - cf['d'] * U[:, None] ** 2 - cf['e'] * U[None, :] ** 2 \
          - cf['dl'] * U[:, None] - cf['el'] * U[None, :] \
          + (cf['hl'] - cf['hr']) * beta - cf['hr'] * A + cf['hr'] * PI + (cf['hl'] + cf['hr']) * W / 2
    val = np.where(Q >= m.qmin, val, -np.inf)
    i0, j0 = np.unravel_index(np.argmax(val), val.shape)
    x, fx = pattern_search(f, [U[i0], U[j0]], [0.0, 0.0], [1.0, 1.0], [0.01, 0.01])
    return float(fx), (float(x[0]), float(x[1])), float(val[i0, j0])


def main():
    R = 19 / 50
    m = Model('q0_lower375_dual_0_4.json', R)
    fac = maximize_all(m, 'c825_R38')
    F, ang, yface, bsw, ysw, rng = assemble(m, fac)
    G = residuals(m, ang, yface, bsw, ysw, rng)
    # determined alpha from the angle sums: R_i = sum_faces theta + alpha_i - b_{i-1} - b_i - pi = 0
    sum_faces = np.zeros(9)
    for t, f in enumerate(m.faces):
        for k, i in enumerate(f):
            if i < 9: sum_faces[i] += ang[t, k]
    adet = PI - sum_faces + np.roll(bsw, 1) + bsw
    free = 0.0; det = 0.0; rows = []
    for i in range(9):
        cf = m.ring_coefs(i)
        vf, (uf, vvf), _ = ring_max_uv(m, i, rng[i, 0], cf)
        vd, (ud, vd2), _ = ring_max_uv(m, i, adet[i], cf)
        free += vf; det += vd
        rows.append(dict(i=i, alpha_free=float(rng[i, 0]), alpha_det=float(adet[i]),
                         ring_free=vf, ring_det=vd, loss=vf - vd,
                         u_free=float(rng[i, 1]), v_free=float(rng[i, 2]),
                         u_det=ud, v_det=vd2))
    # free value recomputed on the same instrument for a fair comparison
    print(f'ring free (instrument) = {free:.9f}   ring with alpha determined = {det:.9f}')
    print(f'=> upper bound on gain of imposing the 11 site angle sums: {free - det:.6f}'
          f'   (gap V-pi = 0.047188)')
    for r in rows:
        print('  ring%d alpha_free=%.5f alpha_det=%.5f  loss=%+.6f' %
              (r['i'], r['alpha_free'], r['alpha_det'], r['loss']))
    print('max |site angle-sum residual| at argmax: %.6f rad' % np.abs(G['site']).max())
    (HERE / 'r20_anglesum_test.json').write_text(json.dumps(dict(
        R=R, ring_free=free, ring_det=det, gain_ub=free - det, total_gap=0.047188186,
        site_residual=G['site'].tolist(), rows=rows), indent=1))
    print('written', HERE / 'r20_anglesum_test.json')


if __name__ == '__main__':
    main()
