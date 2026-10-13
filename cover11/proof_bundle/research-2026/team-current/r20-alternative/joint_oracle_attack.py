"""joint_oracle_attack.py  (r20-alternative; sole write, no child; NUMERIC only)

Question: is  min_P V >= R*  credible?  Bounded NONCONVEX joint optimisation over the canonical
deficit simplex and the primal coordinates -- no new field construction.

Canonical parametrisation (lead):  widths = L - D*y,  y >= 0,  sum y = 1, D = 9L - 2*pi;
U = unit vectors at the prefix angles of the widths (theta_0 = 0).  Variables: y_1..y_8
(the ninth is 1 - sum y), 44 free primal coords (11 sites + 11 aux), radius r  => 53.
Constraints (SAME SOC/length units as fixed_oracle_v2, i.e. r - |edge| >= 0):
  18 endpoints + 33 face cones + y_i >= 0 (8) + 1 - sum(y) >= 0.
Objective min r.  Starts (<= 12): candidate widths, uniform, the nine simplex vertices,
one asymmetric mix.  A candidate-control run must recover R* ~ 0.37998385311983869.

If some start returns V < R* the FIXED-ORACLE GLOBAL ROUTE FAILS (it is not a cover
counterexample); any such numeric finding is kept pending an exact rational interior
certificate.  Nothing here is certified; v2 is not modified; no subagents.
"""
import json
import time
import numpy as np
from fractions import Fraction as F
from pathlib import Path
from scipy.optimize import minimize

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
R_STAR = float(F(3799838531198387090485182, 10**25))     # C529 rational (NOT C891)
L_CAP = 2 * np.arcsin(0.38)
D_CAP = 9 * L_CAP - 2 * np.pi
NV = 53
IC, IZ = 8, 30
T0 = time.time()
BUDGET = 30.0
from fixed_oracle_force_proposal import FACES, FORCE_ORDER, load_centres, switches_from_centres


def widths_from_y(y8):
    y = np.concatenate([y8, [1.0 - np.sum(y8)]])
    return L_CAP - D_CAP * y


def angles_from_widths(w):
    return np.concatenate([[0.0], np.cumsum(w)])[:9]


def build_unit_jac_helpers():
    pass


def solve(y0, maxiter=400):
    def unpack(x):
        w = widths_from_y(x[:8])
        th = angles_from_widths(w)
        U = np.stack([np.cos(th), np.sin(th)], axis=1)
        return U, x[IC:IC + 22].reshape(11, 2), x[IZ:IZ + 22].reshape(11, 2), x[-1], w
    cons = []

    def mk(site, other, is_face):
        def f(x):
            U, c, z, r, w = unpack(x)
            t = z[other] if is_face else U[other]
            return r - float(np.linalg.norm(c[site] - t))

        def jac(x):
            U, c, z, r, w = unpack(x)
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
            return g
        return {'type': 'ineq', 'fun': f, 'jac': jac}
    for i in range(9):
        cons.append(mk(i, i, False))
        cons.append(mk(i, (i - 1) % 9, False))
    for fi, face in enumerate(FACES):
        for s in face:
            cons.append(mk(s, fi, True))
    for t in range(8):                                        # y >= 0
        cons.append({'type': 'ineq', 'fun': lambda x, t=t: x[t],
                     'jac': lambda x, t=t: np.r_[np.zeros(t), 1.0, np.zeros(NV - t - 1)]})
    cons.append({'type': 'ineq', 'fun': lambda x: 1.0 - float(np.sum(x[:8])),
                 'jac': lambda x: np.r_[-np.ones(8), np.zeros(NV - 8)]})
    U0, c0, z0, r0, w0 = unpack(np.r_[y0, np.zeros(NV - 8)])
    x0 = np.zeros(NV)
    x0[:8] = y0
    sites = np.zeros((11, 2))
    for i in range(9):
        mid = (U0[i] + U0[(i - 1) % 9]) / 2
        sites[i] = mid
    sites[9] = U0[:9].mean(axis=0) * 0.5
    sites[10] = U0[:9].mean(axis=0) * 0.35
    x0[IC:IC + 22] = sites.reshape(-1)
    zz = np.zeros((11, 2))
    for fi, face in enumerate(FACES):
        zz[fi] = sites[face].mean(axis=0)
    x0[IZ:IZ + 22] = zz.reshape(-1)
    seed_edges = ([np.linalg.norm(sites[i] - U0[i]) for i in range(9)]
                  + [np.linalg.norm(sites[i] - U0[(i - 1) % 9]) for i in range(9)]
                  + [np.linalg.norm(sites[s] - zz[fi]) for fi, face in enumerate(FACES) for s in face])
    x0[-1] = float(max(seed_edges)) + 0.01
    res = minimize(lambda x: x[-1], x0, jac=lambda x: np.r_[np.zeros(NV - 1), 1.0], method='SLSQP',
                   bounds=[(None, None)] * (NV - 1) + [(0.05, 1.2)], constraints=cons,
                   options={'maxiter': maxiter, 'ftol': 1e-13})
    U, c, z, r, w = unpack(res.x)
    edges = np.array([cc['fun'](res.x) for cc in cons[:51]])
    return {'r': float(r), 'success': bool(res.success), 'nit': int(res.nit),
            'min_edge_residual_all51': float(edges.min()),
            'sum_y': float(np.sum(res.x[:8]) + (1 - np.sum(res.x[:8]))),
            'y_min': float(min(np.min(res.x[:8]), 1 - np.sum(res.x[:8]))),
            'widths': [float(v) for v in w], 'widths_min': float(w.min()),
            'widths_max_leq_L': bool(w.max() <= L_CAP + 1e-9),
            'sites': c.tolist(), 'aux': z.tolist(), 'U': U.tolist(),
            'init_r_seed': float(x0[-1])}


C = load_centres()
sw = switches_from_centres(C)
th = np.array([np.arctan2(p[1], p[0]) for p in sw])
wc = np.mod(np.diff(np.concatenate([th, [th[0] + 2 * np.pi]])), 2 * np.pi)
ycand = (L_CAP - wc) / D_CAP
m_small = 2 * np.pi - 8 * L_CAP
starts = [('candidate', ycand), ('uniform', (L_CAP - 2 * np.pi / 9) / D_CAP * np.ones(9))]
for k in range(9):
    w = np.full(9, L_CAP)
    w[k] = m_small
    starts.append(('vertex%d' % k, (L_CAP - w) / D_CAP))
starts.append(('asymmetric_mix', 0.5 * ycand + 0.5 * (L_CAP - np.concatenate([[m_small],
                                                                             np.full(8, L_CAP)])) / D_CAP))
starts = [(nm, np.asarray(y)[:8]) for nm, y in starts][:12]
rep = {'R_STAR_label': 'C529 rational (NOT C891)', 'R_star': R_STAR, 'L_cap': L_CAP,
       'D_cap_9L_minus_2pi': D_CAP,
       'note': ('bounded NUMERIC joint oracle attack; V < R* would mean the FIXED-ORACLE GLOBAL '
                'ROUTE FAILS (not a cover counterexample); findings pending exact rational '
                'interior certificate; nothing certified; v2 unmodified'),
       'runs': []}
best = None
for name, y8 in starts:
    if time.time() - T0 > BUDGET:
        rep['runs'].append({'start': name, 'skipped': 'budget'})
        break
    try:
        s = solve(y8)
        s['start'] = name
        s['V_minus_R_star'] = s['r'] - R_STAR
        s['below_R_star_minus_1e7'] = bool(s['r'] < R_STAR - 1e-7
                                           and s['min_edge_residual_all51'] > -1e-9
                                           and s['y_min'] > -1e-12 and s['widths_max_leq_L'])
    except Exception as exc:                                   # noqa: BLE001
        s = {'start': name, 'error': '%s: %s' % (type(exc).__name__, exc), 'failed': True}
    rep['runs'].append(s)
    if 'r' in s and (best is None or s['r'] < best):
        best = s['r']
    print('%-16s r=%.9f r-R*=%.3e success=%s min51=%.1e sumy=%.6f' %
          (name, s.get('r', float('nan')), s.get('V_minus_R_star', float('nan')),
           s.get('success'), s.get('min_edge_residual_all51', float('nan')), s.get('sum_y', float('nan'))))
rep['best_r'] = best
rep['best_V_minus_R_star'] = None if best is None else best - R_STAR
rep['n_below_R_star'] = int(sum(1 for s in rep['runs'] if s.get('below_R_star_minus_1e7')))
rep['elapsed_s'] = round(time.time() - T0, 2)
(OUT / 'joint_oracle_attack.json').write_text(json.dumps(rep, indent=2), encoding='utf-8')
print('best r =', best, ' n_below =', rep['n_below_R_star'], ' elapsed %.1f s' % rep['elapsed_s'])
