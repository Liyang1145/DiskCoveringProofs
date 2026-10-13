"""joint_oracle_attack_new4.py  (r20-alternative; sole write, no child; NUMERIC only)

Narrowed task (lead): FOUR new starts attacking the NEW low-envelope region -- reuse the old
source but do NOT repeat the twelve old seeds.  NOTE the old `joint_oracle_attack.py` supplied
y-gradients ONLY through the site/aux/r entries; the chain rule through U(theta(y)) was missing
(incomplete angular Jacobian).  Here the y-entries are implemented correctly:

  endpoint edge |c_s - U_a(theta)|:  theta_a = sum_{j<a} w_j = sum_{j<a} (L - D y_j)
      d/dy_k = -unit(d) . dU_a/dtheta * dtheta_a/dy_k = -unit(d).U'_a * (-D)   for k < a, else 0

Starts (4):
  1) adaptive_stellar_pilot node 20's y  (fallback: the node centroid / a legal vertex)
  2) adaptive_stellar_pilot node 26's y  (same fallback logic)
  3) root-game face {3,7,8}: y = barycentre of the three simplex vertices 3,7,8
  4) largest-width degeneracy: y = barycentre of the facet {k : y_k = 0} (the maximal-width face)
Candidate is NOT re-run (old results serve as calibration).
"""
import json
import time
import numpy as np
from fractions import Fraction as F
from pathlib import Path
from scipy.optimize import minimize

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
R_STAR = float(F(3799838531198387090485182, 10**25))
L_CAP = 2 * np.arcsin(0.38)
D_CAP = 9 * L_CAP - 2 * np.pi
NV = 53
IC, IZ = 8, 30
from fixed_oracle_force_proposal import FACES, load_centres, switches_from_centres


def widths_from_y(y8, free_last=True):
    y = np.concatenate([y8, [1.0 - np.sum(y8)]]) if free_last else np.asarray(y8)
    return L_CAP - D_CAP * y


def solve(y8, maxiter=400):
    """joint SOC problem with CORRECT y-chain-rule entries in the Jacobian"""
    def unpack(x):
        w = widths_from_y(x[:8])
        th = np.concatenate([[0.0], np.cumsum(w)])[:9]
        U = np.stack([np.cos(th), np.sin(th)], axis=1)
        return U, th, x[IC:IC + 22].reshape(11, 2), x[IZ:IZ + 22].reshape(11, 2), x[-1], w
    cons = []

    def mk(site, other, is_face):
        def f(x):
            U, th, c, z, r, w = unpack(x)
            t = z[other] if is_face else U[other]
            return r - float(np.linalg.norm(c[site] - t))

        def jac(x):
            U, th, c, z, r, w = unpack(x)
            t = z[other] if is_face else U[other]
            d = c[site] - t
            n = np.linalg.norm(d)
            g = np.zeros(NV)
            g[-1] = 1.0
            if n > 1e-14:
                u = d / n
                g[IC + 2 * site:IC + 2 * site + 2] = -u
                if is_face:
                    g[IZ + 2 * other:IZ + 2 * other + 2] = u
                else:
                    # d/dtheta_a of  -|c - U|  =  +unit(d) . U'(theta_a);  theta_a = sum_{j<a} w_j
                    ta = th[other]
                    dUdth = np.array([-np.sin(ta), np.cos(ta)])
                    dtheta_dyk = -D_CAP
                    for k in range(8):
                        if k < other:                     # theta_a depends on y_k (k < a)
                            g[k] += float(u @ dUdth) * dtheta_dyk
            return g
        return {'type': 'ineq', 'fun': f, 'jac': jac}
    for i in range(9):
        cons.append(mk(i, i, False))
        cons.append(mk(i, (i - 1) % 9, False))
    for fi, face in enumerate(FACES):
        for s in face:
            cons.append(mk(s, fi, True))
    for t in range(8):
        cons.append({'type': 'ineq', 'fun': lambda x, t=t: x[t],
                     'jac': lambda x, t=t: np.r_[np.zeros(t), 1.0, np.zeros(NV - t - 1)]})
    cons.append({'type': 'ineq', 'fun': lambda x: 1.0 - float(np.sum(x[:8])),
                 'jac': lambda x: np.r_[-np.ones(8), np.zeros(NV - 8)]})
    U0, th0, _, _, _, w0 = unpack(np.r_[y8, np.zeros(NV - 8)])
    x0 = np.zeros(NV)
    x0[:8] = y8
    sites = np.zeros((11, 2))
    for i in range(9):
        sites[i] = (U0[i] + U0[(i - 1) % 9]) / 2
    sites[9] = U0[:9].mean(axis=0) * 0.5
    sites[10] = U0[:9].mean(axis=0) * 0.35
    x0[IC:IC + 22] = sites.reshape(-1)
    zz = np.zeros((11, 2))
    for fi, face in enumerate(FACES):
        zz[fi] = sites[face].mean(axis=0)
    x0[IZ:IZ + 22] = zz.reshape(-1)
    seed = ([np.linalg.norm(sites[i] - U0[i]) for i in range(9)]
            + [np.linalg.norm(sites[i] - U0[(i - 1) % 9]) for i in range(9)]
            + [np.linalg.norm(sites[s] - zz[fi]) for fi, face in enumerate(FACES) for s in face])
    x0[-1] = float(max(seed)) + 0.01
    res = minimize(lambda x: x[-1], x0, jac=lambda x: np.r_[np.zeros(NV - 1), 1.0], method='SLSQP',
                   bounds=[(None, None)] * (NV - 1) + [(0.05, 1.2)], constraints=cons,
                   options={'maxiter': maxiter, 'ftol': 1e-13})
    U, th, c, z, r, w = unpack(res.x)
    edges = np.array([cc['fun'](res.x) for cc in cons[:51]])
    return {'r': float(r), 'success': bool(res.success), 'nit': int(res.nit),
            'min_edge_residual_all51': float(edges.min()), 'sum_y': float(np.sum(np.concatenate([res.x[:8], [1 - np.sum(res.x[:8])]]))),
            'y_all9': [float(v) for v in np.concatenate([res.x[:8], [1 - np.sum(res.x[:8])]])],
            'widths': [float(v) for v in w], 'widths_max_leq_L': bool(w.max() <= L_CAP + 1e-9),
            'widths_min': float(w.min()), 'init_r_seed': float(x0[-1]),
            'sites': c.tolist(), 'aux': z.tolist()}


def get_node_y():
    """read the adaptive stellar pilot for nodes 20 and 26; fall back to simplex points"""
    cand = {}
    f = OUT / 'adaptive_stellar_pilot.json'
    if not f.exists():
        f = ROOT / 'research-2026/team-current' / 'r20-alternative' / 'adaptive_stellar_pilot.json'
    try:
        d = json.loads(f.read_text(encoding='utf-8'))
        txt = json.dumps(d)[:4000000]

        def hunt(key):
            for k in ('nodes', 'node_list', 'stars'):
                if k in d and isinstance(d[k], list):
                    for rec in d[k]:
                        if isinstance(rec, dict) and str(rec.get('id', rec.get('index'))) == key:
                            for yk in ('y', 'y8', 'deficits', 'y_vec'):
                                if yk in rec:
                                    return np.asarray(rec[yk], dtype=float)[:8]
            return None
        cand['node20'] = hunt('20')
        cand['node26'] = hunt('26')
    except Exception as exc:                                  # noqa: BLE001
        cand['read_error'] = '%s: %s' % (type(exc).__name__, exc)
    m_small = 2 * np.pi - 8 * L_CAP
    y_vertex = [np.eye(9)[j] for j in range(9)]      # vertex j: widths (m at j, L elsewhere) => y = e_j
    bary378 = np.mean([np.asarray(y_vertex[k]) for k in (3, 7, 8)], axis=0)
    facet = np.mean([np.asarray(y_vertex[k]) for k in range(9)], axis=0)                # y = 1/9
    return cand, bary378, facet


def jac_cs_check(y8=None, h=1e-7, seed=11):
    """central-difference audit of the analytic Jacobians: all 51 constraints x 53 variables,
    x-all-8 y-coordinates included, at a GENERIC (non-candidate) y."""
    rng = np.random.default_rng(seed)
    if y8 is None:
        y8 = rng.dirichlet(np.ones(9))[:8] * 0.9            # generic interior point
    cons = None
    # rebuild the constraint list without solving
    # construct cons by calling solve's inner builder through a tiny trick: re-run one SLSQP step
    import types
    # the constraint list is built inside solve(); recreate it here identical to solve()
    def unpack(x):
        w = widths_from_y(x[:8])
        th = np.concatenate([[0.0], np.cumsum(w)])[:9]
        U = np.stack([np.cos(th), np.sin(th)], axis=1)
        return U, th, x[IC:IC + 22].reshape(11, 2), x[IZ:IZ + 22].reshape(11, 2), x[-1], w
    cons = []

    def mk(site, other, is_face):
        def f(x):
            U, th, c, z, r, w = unpack(x)
            t = z[other] if is_face else U[other]
            return r - float(np.linalg.norm(c[site] - t))

        def jac(x):
            U, th, c, z, r, w = unpack(x)
            t = z[other] if is_face else U[other]
            d = c[site] - t
            n = np.linalg.norm(d)
            g = np.zeros(NV)
            g[-1] = 1.0
            if n > 1e-14:
                u = d / n
                g[IC + 2 * site:IC + 2 * site + 2] = -u
                if is_face:
                    g[IZ + 2 * other:IZ + 2 * other + 2] = u
                else:
                    ta = th[other]
                    dUdth = np.array([-np.sin(ta), np.cos(ta)])
                    for k in range(8):
                        if k < other:
                            g[k] += float(u @ dUdth) * (-D_CAP)
            return g
        return {'type': 'ineq', 'fun': f, 'jac': jac}
    for i in range(9):
        cons.append(mk(i, i, False))
        cons.append(mk(i, (i - 1) % 9, False))
    for fi, face in enumerate(FACES):
        for s in face:
            cons.append(mk(s, fi, True))
    xr = np.zeros(NV)
    xr[:8] = y8
    sites = np.zeros((11, 2))
    for i in range(9):
        sites[i] = np.array([0.3 * np.cos(2 * np.pi * i / 9 + 0.2), 0.3 * np.sin(2 * np.pi * i / 9 + 0.2)])
    sites[9] = np.array([0.05, 0.10]); sites[10] = np.array([-0.05, -0.08])
    xr[IC:IC + 22] = sites.reshape(-1)
    zz = np.zeros((11, 2))
    for fi, face in enumerate(FACES):
        zz[fi] = sites[face].mean(axis=0) + np.array([0.01, -0.01])
    xr[IZ:IZ + 22] = zz.reshape(-1)
    xr[-1] = 0.5
    worst, tag, worst_k = 0.0, None, None
    for ci, cc in enumerate(cons[:51]):
        ga = np.asarray(cc['jac'](xr), dtype=float)
        for k in range(NV):
            xp, xm = xr.copy(), xr.copy()
            xp[k] += h; xm[k] -= h
            gc = (cc['fun'](xp) - cc['fun'](xm)) / (2 * h)
            err = abs(ga[k] - gc)
            if err > worst:
                worst, tag, worst_k = err, 'constraint %d' % ci, k
    return {'y_used': [float(v) for v in y8], 'n_constraints': 51, 'n_variables': NV,
            'max_jac_error': worst, 'worst': tag, 'worst_variable': worst_k, 'step': h,
            'PASS_lt_1e-6': bool(worst < 1e-6)}


if __name__ == '__main__':
    t0 = time.time()
    chk = jac_cs_check()
    print('jacobian CS check:', json.dumps(chk))
    if not chk['PASS_lt_1e-6']:
        print('JACOBIAN CHECK FAILED -> not running the four starts')
        raise SystemExit(1)
    cand, bary378, facet = get_node_y()
    m_small = 2 * np.pi - 8 * L_CAP
    y_vertex = [np.eye(9)[j] for j in range(9)]   # vertex j => y = e_j
    starts = []
    for nm in ('node20', 'node26'):
        yy = cand.get(nm)
        starts.append((nm + ('' if yy is not None else '_FALLBACK_vertex0'),
                       yy if yy is not None else np.asarray(y_vertex[0])[:8]))
    starts.append(('rootgame_face_378_barycentre', bary378[:8]))
    starts.append(('largest_width_facet_barycentre', facet[:8]))
    rep = {'R_STAR_label': 'C529 rational (NOT C891)', 'R_star': R_STAR, 'L_cap': L_CAP,
           'jacobian_cs_check': chk,
           'note': ('four NEW starts attacking the low-envelope region; y-Jacobian chain rule '
                    'IMPLEMENTED here (the earlier joint_oracle_attack.py had incomplete '
                    'y-gradients); candidate not re-run (old calibration stands); NUMERIC only'),
           'pilot_node_read': {str(k): (None if not isinstance(v, np.ndarray)
                                        else [float(x) for x in np.asarray(v).reshape(-1)[:8]])
                               for k, v in cand.items()},
           'runs': []}
    for name, y8 in starts:
        s = solve(np.asarray(y8, dtype=float))
        s['start'] = name
        s['V_minus_R_star'] = s['r'] - R_STAR
        s['below_R_star_by_1e7'] = bool(s['r'] < R_STAR - 1e-7
                                        and s['min_edge_residual_all51'] > -1e-9
                                        and s['widths_max_leq_L'])
        rep['runs'].append(s)
        print('%-34s r=%.9f r-R*=%.3e success=%s min51=%.1e wmax<=L=%s'
              % (name, s['r'], s['V_minus_R_star'], s['success'], s['min_edge_residual_all51'],
                 s['widths_max_leq_L']))
    rep['n_below'] = int(sum(1 for s in rep['runs'] if s['below_R_star_by_1e7']))
    rep['elapsed_s'] = round(time.time() - t0, 2)
    (OUT / 'joint_oracle_attack_new4.json').write_text(json.dumps(rep, indent=2), encoding='utf-8')
    print('n_below =', rep['n_below'], ' elapsed %.1f s' % rep['elapsed_s'])
