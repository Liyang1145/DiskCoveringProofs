"""R20-E: first-order cost of the two candidate couplings at the saved dual.

(1) CLOSURE coupling (C820 sector-chain position closure): restrict the switch factor's b to the
    closure-determined value b_i^cl = (pi - T_i - L_{i+1} - (w_i+w_{i+1})/2)/2 built from the two
    adjacent sectors.  Then
        gain_closure = V_indep - V_closure  <=  sum_i [ F_sw,i(b_i^ind,y*) - F_sw,i(b_i^cl,y*) ]
    because the independent rings stay feasible.  Computed exactly (the switch factor is 1-D in b
    with an analytic y-max), so the bound is a rigorous upper bound for the gain of this
    ONE mechanism at this z, up to the accuracy of the factor maxima.

(2) SIDE-MATCHING families m2 (squared) and m1 (first moment): report the argmax residuals and
    the multiplier-weighted contributions (from r20_mechanism.json) -- these are the sizes of the
    corresponding 'missing glue' terms, not yet a gain bound.
Diagnostic only.
"""
import json, math
import numpy as np
from pathlib import Path
from r20_factor_probe import Model, PI, maximize_all
from r20_residuals import assemble, residuals

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'


def closure_b(alpha, u, v, bsw, R):
    """b_i^cl from sector i and sector i+1 (index i -> switch i)."""
    q = (u - v) ** 2 + 4 * u * v * np.sin(alpha / 2) ** 2
    w = 2 * np.arcsin(np.clip(R * np.sqrt(np.maximum(q, 1e-18)) / 2, 0, 1))
    L = np.arctan2(v * np.sin(alpha), u - v * np.cos(alpha))
    T = PI - alpha - L
    # G_i = T_i + L_{i+1} + 2 b_i + (w_i + w_{i+1})/2 - pi = 0
    b = (PI - T - np.roll(L, -1) - (w + np.roll(w, -1)) / 2) / 2
    return b, T, L, w


def main():
    rep = {}
    for tag, zf, R in [('c825_R375', 'q0_lower375_dual_0_4.json', 3 / 8),
                       ('c825_R38', 'q0_lower375_dual_0_4.json', 19 / 50)]:
        m = Model(zf, R)
        fac = maximize_all(m, tag)
        F, ang, yface, bsw, ysw, rng = assemble(m, fac)
        alpha, u, v = rng[:, 0], rng[:, 1], rng[:, 2]
        bcl, T, L, w = closure_b(alpha, u, v, bsw, R)
        lo = np.zeros(9); hi = np.full(9, PI / 2)
        loss = 0.0; rows = []
        # independent switch values (b free, y free)
        vind = np.zeros(9); vcl = np.zeros(9)
        for i in range(9):
            cf = m.switch_coefs(i)
            vi, yi = m.switch_val(i, bsw[i], cf)
            b = min(hi[i], max(lo[i], bcl[i]))
            vc, yc = m.switch_val(i, b, cf)
            vind[i] = vi; vcl[i] = vc
            loss += vi - vc
            rows.append(dict(i=i, b_ind=float(bsw[i]), b_cl=float(b), d_b=float(b - bsw[i]),
                             sw_ind=float(vi), sw_cl=float(vc), d_sw=float(vc - vi)))
        V = float(m.const + F.sum())
        print(f'[{tag}] V_indep={V:.9f}  closure-coupling gain <= {loss:.6f}')
        for r in rows:
            print('   sw%d b_ind=%.5f b_cl=%.5f db=%+.5f  F_ind=%.6f F_cl=%.6f dF=%+.6f'
                  % (r['i'], r['b_ind'], r['b_cl'], r['d_b'], r['sw_ind'], r['sw_cl'], r['d_sw']))
        G = residuals(m, ang, yface, bsw, ysw, rng)
        print(f'[{tag}] closure residuals |G|: max={np.abs(G["closure"]).max():.6f} '
              f'sum={np.abs(G["closure"]).sum():.6f}   (rad)')
        print(f'[{tag}] side-match residual |m2| max={np.abs(G["m2"]).max():.6f} '
              f'|m1| max={np.abs(G["m1"]).max():.6f}')
        rep[tag] = dict(V=V, gain_closure_ub=float(loss), rows=rows,
                        closure=[float(x) for x in G['closure']],
                        m2=[float(x) for x in G['m2']], m1=[float(x) for x in G['m1']])
    (HERE / 'r20_closure_coupling.json').write_text(json.dumps(rep, indent=1))
    print('written', HERE / 'r20_closure_coupling.json')


if __name__ == '__main__':
    main()
