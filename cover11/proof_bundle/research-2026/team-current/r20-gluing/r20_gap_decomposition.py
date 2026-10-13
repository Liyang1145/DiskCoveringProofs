"""R20-F: causal decomposition of the duality gap at the saved candidate.

V(z*) - pi = sum_k [ sup_k(z*) - F_k(z*; x_cand,k) ]      (exact, since D(z*;x_cand) = pi:
every equality residual vanishes at the genuine candidate and the Delaunay multipliers are 0).

Reports, for the saved dual z* (C825 coefficients) at R = 19/50, the per-factor excess delta_k
of the independent relaxation over the value at the saved genuine candidate
(r = 0.3799838531198388 < R).  Large delta_k pinpoint which factors the relaxation lets
'cheat', i.e. where a coupling would have to act.
Diagnostic only.
"""
import json, math
import numpy as np
from pathlib import Path
from r20_factor_probe import Model, PI, maximize_all
from r20_mechanism import candidate_point

HERE = Path(__file__).parent


def main():
    R = 19 / 50
    m = Model('q0_lower375_dual_0_4.json', R)
    fac = maximize_all(m, 'c825_R38')
    ang, yface, bsw, ysw, rng, rc, rho = candidate_point(R)
    rows = []
    for r in fac:
        k = r['idx']; nm = r['name']
        if r['kind'] == 'face':
            t = r['idx']
            vc, yc = m.face_val(t, ang[t, 0], ang[t, 1])
            # value at candidate variables (quad evaluated at candidate y, same as factor def.)
            co, dd, ll, _ = m.face_coefs(t)
            a, b = ang[t, 0], ang[t, 1]; c = PI - a - b
            s = (math.sin(a), math.sin(b), math.sin(c))
            A = 2 * m.R2 * s[0] * s[1] * s[2] + sum(dd[q] * s[q] ** 2 for q in range(3))
            B = sum(ll[q] * s[q] for q in range(3))
            Fc = co[0] * a + co[1] * b + co[2] * c + A * yface[t] ** 2 + B * yface[t]
        elif r['kind'] == 'switch':
            i = r['idx'] - 11
            cc, d, ee, g, h, _ = m.switch_coefs(i)
            b = bsw[i]
            Fc = cc * b + (m.R2 * math.sin(2 * b) / 2 - d * math.sin(b) ** 2 + ee) * ysw[i] ** 2 \
                 + (g * math.sin(b) + h) * ysw[i]
        else:
            i = r['idx'] - 20
            a, u, v = rng[i]
            Fc = m.ring_val(i, a, u, v)
        rows.append(dict(name=nm, kind=r['kind'], sup=float(r['val']), at_candidate=float(Fc),
                         delta=float(r['val'] - Fc)))
    tot = sum(x['delta'] for x in rows)
    print(f'R={R}  sum delta_k = {tot:.9f}   (V - pi = {tot:.9f})')
    for x in sorted(rows, key=lambda x: -x['delta']):
        print('  %-8s %-7s sup=%.8f  at_cand=%.8f  delta=%+.8f' %
              (x['name'], x['kind'], x['sup'], x['at_candidate'], x['delta']))
    bykind = {}
    for x in rows: bykind[x['kind']] = bykind.get(x['kind'], 0.0) + x['delta']
    print('by kind:', {k: round(v, 6) for k, v in bykind.items()})
    (HERE / 'r20_gap_decomposition.json').write_text(json.dumps(
        dict(R=R, total=tot, rows=rows, by_kind=bykind), indent=1))


if __name__ == '__main__':
    main()
