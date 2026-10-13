"""Phase-3 helpers: high-precision (mpmath) re-implementation of the C839 angle model,
returning the 20 branch logs b_f = log gamma_f + log(q0/ell0) and the 8 nonlinear
constraint residuals c8 = (2 sine-cycle residuals, 6 circle-ratio residuals) as a function
of the 29 nullspace coordinates y  (a = a0 + Nr y ; the 13 linear angle equalities are exact).

Validated against the lead float64 model in test_mp_model() (called from __main__).
Writes only inside research-2026/team-current/r20-stress/out .
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp

mp.mp.dps = 50
W_DIR = Path(__file__).parent
LEAD = W_DIR.parent / 'lead'


def load():
    zz = {'__file__': str(LEAD / 'check_angle_only.py')}
    exec((LEAD / 'check_angle_only.py').read_text(encoding='utf-8').split("a=ns['x0'][:42]")[0], zz)
    ns, shape, radii = zz['ns'], zz['shape'], zz['radii']
    zz2 = {'__file__': str(LEAD / 'angle_stress_probe.py')}
    exec((LEAD / 'angle_stress_probe.py').read_text(encoding='utf-8').split('y0=np.zeros(29)')[0], zz2)
    Nr, a0 = zz2['N'], ns['x0'][:42]
    lam_saved, mu_saved, act, station = zz2['lam'], zz2['mu'], zz2['act'], float(zz2['station'])

    # incidence (same construction as check_angle_only.py)
    edge = []
    for k in range(21):
        f = int(np.argmax(ns['U'][k, 42:62])); g = int(np.argmax(ns['V'][k, 42:62]))
        edge.append((f, g))
    adj = {}
    for k, (f, g) in enumerate(edge):
        adj.setdefault(f, []).append((g, k, 1)); adj.setdefault(g, []).append((f, k, -1))
    tree = radii(a0, 0)[2]                     # spanning-tree edge indices (graph property)
    return dict(ns=ns, shape=shape, radii=radii, Nr=Nr, a0=a0, lam=lam_saved, mu=mu_saved,
                act=act, station=station, edge=edge, adj=adj, tree=tree)


def make_mp_model(M):
    ns = M['ns']
    A_m = [[mp.mpf(float(x)) for x in row] for row in np.asarray(ns['A'])[:, :42]]
    B_m = [[mp.mpf(float(x)) for x in row] for row in np.asarray(ns['B'])[:, :42]]
    al_m = [[mp.mpf(float(x)) for x in row] for row in np.asarray(ns['alpha'])[:, :42]]
    ac_m = [mp.mpf(float(x)) for x in np.asarray(ns['ac'])]
    Nr_m = [[mp.mpf(float(x)) for x in row] for row in M['Nr']]
    a0_m = [mp.mpf(float(x)) for x in M['a0']]
    edge, adj, tree = M['edge'], M['adj'], set(M['tree'])

    def bc(y):
        """y: list of 29 mpf -> (b (20 mpf), c8 (8 mpf))"""
        a = [a0_m[i] + mp.fsum([Nr_m[i][k] * y[k] for k in range(29)]) for i in range(42)]
        Aa = [mp.fsum([A_m[j][i] * a[i] for i in range(42)]) for j in range(21)]
        Ba = [mp.fsum([B_m[j][i] * a[i] for i in range(42)]) for j in range(21)]
        ls = [mp.log(mp.sin(Aa[j])) - mp.log(mp.sin(Ba[j])) for j in range(21)]
        logg = {0: mp.mpf(0)}; todo = [0]
        for f in todo:
            for (g, k, d) in adj[f]:
                if g not in logg:
                    logg[g] = logg[f] + d * ls[k]; todo.append(g)
        assert len(logg) == 20
        cy = [logg[f] - logg[g] + ls[k] for k, (f, g) in enumerate(edge)]
        gsw = [logg[11 + i] for i in range(9)]
        alv = [ac_m[i] + mp.fsum([al_m[i][j] * a[j] for j in range(42)]) for i in range(9)]
        ell = []
        for i in range(9):
            ui = mp.e ** gsw[(i - 1) % 9]; vi = mp.e ** gsw[i]
            ell.append(mp.sqrt(ui ** 2 + vi ** 2 - 2 * ui * vi * mp.cos(alv[i])))
        Lv = [mp.atan2(mp.e ** gsw[i] * mp.sin(alv[i]), mp.e ** gsw[(i - 1) % 9] - mp.e ** gsw[i] * mp.cos(alv[i]))
              for i in range(9)]
        w = []
        for i in range(9):
            s = mp.mpf(0)
            for j in range(9):
                s += (-1) ** ((j - i) % 9) * (mp.pi - (mp.pi - alv[j] - Lv[j]) - Lv[(j + 1) % 9] - 2 * a[33 + j])
            w.append(s)
        q = [2 * mp.sin(w[i] / 2) for i in range(9)]
        rat = [q[i] / ell[i] for i in range(9)]
        b = [logg[f] + mp.log(rat[0]) for f in range(20)]
        c8 = [cy[k] for k in range(21) if k not in tree] + [rat[i] / rat[0] - 1 for i in range(1, 7)]
        return b, c8

    return bc


def jac_mp(bc, h=None):
    """central-difference Jacobian at y=0 in 50-digit arithmetic: returns list of 28 rows (each 29 mpf)."""
    h = h if h is not None else mp.mpf('1e-20')
    y0 = [mp.mpf(0)] * 29
    cols = []
    for k in range(29):
        yp = list(y0); ym = list(y0)
        yp[k] = h; ym[k] = -h
        bp, cp = bc(yp); bm, cm = bc(ym)
        col = [(bp[i] - bm[i]) / (2 * h) for i in range(20)] + [(cp[i] - cm[i]) / (2 * h) for i in range(8)]
        cols.append(col)
    # cols[k][j] = d f_j / d y_k  -> transpose to 28 x 29
    return [[cols[k][j] for k in range(29)] for j in range(28)]


def test_mp_model():
    """Validation: mpmath b/c8 at the candidate and at two phase-2 points vs the lead float64 model."""
    import json
    M = load(); bc = make_mp_model(M)
    shape, a0, Nr = M['shape'], M['a0'], M['Nr']
    p2 = json.loads((W_DIR / 'out' / 'phase2_stress_domain.json').read_text())
    pts = {'candidate': a0,
           'P1': np.array(p2['raws']['boundary_R038_1']),
           'P2': np.array(min([r for r in p2['hessian_diag']['line_search'] if 'phi_minus_logTcert' in r],
                              key=lambda r: r['phi_minus_logTcert'])['a'])}
    out = {}
    for tag, a in pts.items():
        y = np.linalg.pinv(Nr) @ (a - a0)
        b, c8 = bc([mp.mpf(float(x)) for x in y])
        r, con, d = shape(a)
        b64 = d['logg'] + np.log(d['rat'][0])
        c64 = con[13:21]
        out[tag] = dict(max_abs_b_mp_minus_f64=float(max(abs(mp.mpf(float(b64[i])) - b[i]) for i in range(20))),
                        max_abs_c8_mp_minus_f64=float(max(abs(mp.mpf(float(c64[i])) - c8[i]) for i in range(8))))
        print(tag, out[tag])
    return out


if __name__ == '__main__':
    import time, json
    t0 = time.time()
    M = load()
    bc = make_mp_model(M)
    print('lead stationarity residual (float64 solve):', M['station'], ' |act| =', len(M['act']))
    print('validation:', test_mp_model())
    t1 = time.time()
    G = jac_mp(bc)
    print('jacobian(28x29) computed in %.1f s' % (time.time() - t1))
    G64 = np.array([[float(x) for x in row] for row in G])
    J8, Wg = G64[20:], G64[:20]
    sv = np.linalg.svd(J8, compute_uv=False)
    print('J8 singular values:', sv)
    (W_DIR / 'out' / 'phase3_jacobian.json').write_text(json.dumps(
        dict(scope='50-digit central-difference Jacobian of (b20, c8_8) wrt 29 nullspace coords; y=0 (candidate)',
             h='1e-20', J8=J8.tolist(), W=Wg.tolist(), J8_sv=sv.tolist(),
             validation=test_mp_model()), indent=2))
    print('written out/phase3_jacobian.json  total %.1f s' % (time.time() - t0))
