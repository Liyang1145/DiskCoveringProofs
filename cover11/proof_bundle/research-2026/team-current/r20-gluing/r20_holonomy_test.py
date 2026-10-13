"""R20-H: decisive bounded test of the holonomy proposal P-R20-2.

Maximise the face+switch part of the frozen C825 dual objective (rings stay free and are
unaffected) subject to the two holonomy conditions of the shared-side system, starting from the
unconstrained argmax.  For ANY feasible point x_f one has

    V_holonomy >= V_at(x_f) = V_indep - Delta(x_f)   =>   gain = V_indep - V_holonomy <= Delta(x_f),

so a small Delta at a feasible point is an upper bound (up to factor-maximisation accuracy) on
the gain of imposing this coupling.  One constrained local solve, <= 3 starts.

Parameterisation (corrected): variables = 11 face pairs (a_t,b_t) + 9 switch half-angles
(= 31), the third face angle is DETERMINED by c = pi - a - b in BOTH objective and constraint.
(First version left the third angle free in the constraint while it was unused by the
objective, which made the constraint look free; that version is withdrawn.)
Diagnostic only.
"""
import json, math
import numpy as np
from pathlib import Path
from scipy.optimize import minimize
from r20_factor_probe import Model, PI, maximize_all
from r20_residuals import assemble
from r20_holonomy import build

HERE = Path(__file__).parent


def full_angles(th):
    """31 -> 33 face angles (a,b,c=pi-a-b)."""
    out = np.empty(33)
    for t in range(11):
        a, b = th[2 * t], th[2 * t + 1]
        out[3 * t:3 * t + 3] = (a, b, PI - a - b)
    return out


def rhs_of(m, rows, th):
    fa = full_angles(th)
    rhs = np.zeros(len(rows))
    for r, (ei, n1, n2, ad) in enumerate(rows):
        t1, v1 = ad[0]; a1 = fa[3 * t1 + m.faces[t1].index(v1)]
        if len(ad) == 2:
            t2, v2 = ad[1]; a2 = fa[3 * t2 + m.faces[t2].index(v2)]
        else:
            bi = n2 - 11; a2 = th[22 + bi]
        rhs[r] = math.log(math.sin(a2)) - math.log(math.sin(a1))
    return rhs


def main():
    R = 19 / 50
    m = Model('q0_lower375_dual_0_4.json', R)
    rows = build(m)
    fac = maximize_all(m, 'c825_R38')
    F, ang, yface, bsw, ysw, rng = assemble(m, fac)
    Mmat = np.zeros((len(rows), 20))
    for r, (ei, n1, n2, ad) in enumerate(rows):
        Mmat[r, n1] += 1.0; Mmat[r, n2] -= 1.0
    U, s, Vt = np.linalg.svd(Mmat)
    ns = int(np.sum(s > max(s[0] * 1e-12, 1e-14)))
    Unull = U[:, ns:]
    th0 = np.r_[ang[:, 0], ang[:, 1], bsw]           # interleave: 11 a's, 11 b's, 9 switch b
    th0 = np.zeros(31)
    for t in range(11): th0[2 * t], th0[2 * t + 1] = ang[t, 0], ang[t, 1]
    th0[22:] = bsw
    print('holonomy defect at the unconstrained argmax:', np.abs(Unull.T @ rhs_of(m, rows, th0)))

    def negobj(th):
        tot = 0.0
        for t in range(11):
            a, b = th[2 * t], th[2 * t + 1]
            if a <= 0 or b <= 0 or a + b >= PI: return 1e8
            v, _ = m.face_val(t, a, b)
            if not np.isfinite(v): return 1e8
            tot += v
        for i in range(9):
            bb = th[22 + i]
            if bb < 0 or bb > PI / 2: return 1e8
            tot += m.switch_val(i, bb)[0]
        return -tot

    def cons(th):
        return Unull.T @ rhs_of(m, rows, th)

    V_face_sw = sum(r['val'] for r in fac if r['kind'] in ('face', 'switch'))
    best = None
    for trial in range(3):
        seed = th0.copy()
        if trial:
            rr = np.random.default_rng(31415 + trial)
            seed = th0 + rr.normal(0, 2e-3 * trial, th0.size)
        seed[0:22:2] = np.clip(seed[0:22:2], 1e-4, PI - 1e-4)
        seed[1:22:2] = np.clip(seed[1:22:2], 1e-4, PI - 1e-4)
        seed[22:] = np.clip(seed[22:], 1e-4, PI / 2 - 1e-4)
        o = minimize(negobj, seed, method='SLSQP',
                     constraints=[{'type': 'eq', 'fun': cons}],
                     bounds=[(1e-4, PI - 1e-4)] * 22 + [(1e-4, PI / 2 - 1e-4)] * 9,
                     options={'maxiter': 600, 'ftol': 1e-13})
        val = -negobj(o.x); dev = float(np.abs(cons(o.x)).max())
        if best is None or val > best[0]: best = (val, o.x.copy(), dev)
        print(f'trial {trial}: success={o.success} value={val:.9f} holonomy_defect={dev:.3e}')
    val, xb, dev = best
    print(f'unconstrained face+switch max = {V_face_sw:.9f}')
    print(f'holonomy-feasible value       = {val:.9f} (|defect|_max = {dev:.3e})')
    print(f'=> upper bound on gain of imposing holonomy alone: {V_face_sw - val:.6f}'
          f'   (total gap V-pi = 0.047188)')
    (HERE / 'r20_holonomy_test.json').write_text(json.dumps(dict(
        R=R, unconstrained_face_switch=V_face_sw, holonomy_feasible_value=val,
        holonomy_defect=dev, gain_upper_bound=V_face_sw - val,
        total_gap=0.047188186, th_argmax=th0.tolist(), th_feasible=xb.tolist(),
        holonomy_defect_argmax=float(np.abs(Unull.T @ rhs_of(m, rows, th0)).max())), indent=1))
    print('written', HERE / 'r20_holonomy_test.json')


if __name__ == '__main__':
    main()
