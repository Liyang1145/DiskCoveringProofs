"""socp_sector_pilot.py  (r20-alternative; sole write, no child)

Lead pilot: JOINT SECTOR SLSQP around the uniform configuration.
Variables U_i for i = 1..8 (theta_0 fixed at 0), plus the 11 sites c, 11 aux z and r (61 vars):
  * unit disk (CONVEX):   1 - |U_i|^2 >= 0                (8 inequalities; early drafts had the non-convex circle |U_i| = 1)
  * sector half-width h:  n_i . U_i >= cos h              (8 inequalities, n_i = uniform direction)
  * all 51 distance edges (18 endpoints + 33 face cones, same as the fixed-switch SOCP)
Objective min r.  Three bounded runs h in {0, 0.005, 0.02}; h = 0 is calibrated against the
existing uniform value (V - R* = +0.01367577 from the earlier fixed-switch run).
Reported: primal, plus a DUAL-side proxy = sum of norm-form multipliers, free-gradient residual
norm and the direct 51-edge residuals.  Purely numeric; nothing certified; no B&B.
"""
import json
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import minimize

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
Pf = np.array([[float(F(int(v[0]), 10**17)), float(F(int(v[1]), 10**17))]
               for v in raw['centers_scaled_1e17']])
NEW2RAW_RINGS = [5, 7, 1, 8, 6, 4, 9, 10, 3]
C0 = Pf[NEW2RAW_RINGS + [2, 0]]
R_STAR = float(F(3799838531198387090485182, 10**25))
graph = json.loads((ROOT / 'research-2026/team-current/lead/q0_graphs.json').read_text())[2]
FACES = [list(f) for f in graph['faces']]
UNIF = np.array([[np.cos(2 * np.pi * i / 9), np.sin(2 * np.pi * i / 9)] for i in range(9)])


exports = {}


def build(h):
    freeU = h > 0                              # h = 0: U_i FIXED (no extra free variables)
    NV = (16 if freeU else 0) + 22 + 22 + 1
    IU = lambda i: 2 * (i - 1)                 # i = 1..8
    IC = 16 if freeU else 0
    IZ = IC + 22

    def unpack(x):
        if h > 0:
            U = [UNIF[0]] + [x[IU(i):IU(i) + 2] for i in range(1, 9)]
        else:
            U = [UNIF[i] for i in range(9)]
        return np.array(U), x[IC:IC + 22].reshape(11, 2), x[IZ:IZ + 22].reshape(11, 2), x[-1]
    cons = []
    if h > 0:
        for i in range(1, 9):
            # CONVEX unit-disk inequality 1 - |U_i|^2 >= 0 (was wrongly |U_i| = 1, a circle)
            cons.append({'type': 'ineq',
                         'fun': lambda x, i=i: 1.0 - float(np.sum(x[IU(i):IU(i) + 2]**2)),
                         'jac': lambda x, i=i: np.r_[np.zeros(IU(i)), -2 * x[IU(i):IU(i) + 2],
                                                     np.zeros(NV - IU(i) - 2)]})
            n_i = UNIF[i]
            cons.append({'type': 'ineq',
                         'fun': lambda x, i=i, n_i=n_i: float(x[IU(i):IU(i) + 2] @ n_i) - np.cos(h),
                         'jac': lambda x, i=i, n_i=n_i: np.r_[np.zeros(IU(i)), n_i,
                                                              np.zeros(NV - IU(i) - 2)]})

    def mk_end(i, anchor):
        def f(x):
            U, c, z, r = unpack(x)
            return r * r - float(np.sum((c[i] - U[anchor])**2))

        def jac(x):
            U, c, z, r = unpack(x)
            g = np.zeros(NV)
            g[IC + 2 * i:IC + 2 * i + 2] = -2 * (c[i] - U[anchor])
            if IU(anchor) >= 0 and anchor >= 1 and NV > 45:
                g[IU(anchor):IU(anchor) + 2] = 2 * (c[i] - U[anchor])
            g[-1] = 2 * r
            return g
        return {'type': 'ineq', 'fun': f, 'jac': jac}

    def mk_face(fi, s):
        def f(x):
            U, c, z, r = unpack(x)
            return r * r - float(np.sum((c[s] - z[fi])**2))

        def jac(x):
            U, c, z, r = unpack(x)
            g = np.zeros(NV)
            g[IC + 2 * s:IC + 2 * s + 2] = -2 * (c[s] - z[fi])
            g[IZ + 2 * fi:IZ + 2 * fi + 2] = 2 * (c[s] - z[fi])
            g[-1] = 2 * r
            return g
        return {'type': 'ineq', 'fun': f, 'jac': jac}
    for i in range(9):
        cons.append(mk_end(i, i))
        cons.append(mk_end(i, (i - 1) % 9))
    for fi, face in enumerate(FACES):
        for s in face:
            cons.append(mk_face(fi, s))
    return NV, IU, IC, IZ, unpack, cons


def circumcenter_of(P):
    M = np.stack([2 * (P[1] - P[0]), 2 * (P[2] - P[0])], axis=0)
    b = np.array([P[1] @ P[1] - P[0] @ P[0], P[2] @ P[2] - P[0] @ P[0]])
    try:
        return np.linalg.solve(M, b)
    except np.linalg.LinAlgError:
        return P.mean(axis=0)


out = {'scope': 'numeric joint-sector pilot (no certificate, no B&B, no scaling)',
       'R_STAR_label': 'C529 rational value (NOT C891)',
       'r_star_value': R_STAR,
       'R_star': R_STAR, 'calibration_reference_uniform_V_minus_R_star': 0.01367577, 'runs': []}
for h in (0.0, 0.02):
    NV, IU, IC, IZ, unpack, cons = build(h)
    sites = np.zeros((11, 2))
    sites[:9] = (UNIF + np.roll(UNIF, 1, axis=0)) / 2
    sites[9] = np.array([0.0, 0.20])
    sites[10] = np.array([0.0, -0.12])
    x0 = np.zeros(NV)
    if h > 0:
        for i in range(1, 9):
            x0[IU(i):IU(i) + 2] = UNIF[i]
    x0[IC:IC + 22] = sites.reshape(-1)
    zz = np.zeros((11, 2))
    for fi, face in enumerate(FACES):
        zz[fi] = circumcenter_of(sites[face])
    x0[IZ:IZ + 22] = zz.reshape(-1)
    x0[-1] = 0.40
    res = minimize(lambda x: x[-1], x0, jac=lambda x: np.r_[np.zeros(NV - 1), 1.0], method='SLSQP',
                   bounds=[(None, None)] * (NV - 1) + [(0.05, 0.6)], constraints=cons,
                   options={'maxiter': 500, 'ftol': 1e-14})
    U, c, z, r = unpack(res.x)
    vals = np.array([cc['fun'](res.x) if cc['type'] == 'ineq' else abs(cc['fun'](res.x))
                     for cc in cons])
    n_eq = sum(1 for cc in cons if cc['type'] == 'eq')
    ineq_vals = np.array([cc['fun'](res.x) for cc in cons if cc['type'] == 'ineq'])
    off = 16 if h > 0 else 0                     # sector constraints exist only for h > 0
    entry = {'h': h, 'success': bool(res.success), 'nit': int(res.nit),
             'V': float(res.fun), 'V_minus_R_star': float(res.fun) - R_STAR,
             'min_ineq_residual_51edges': float(ineq_vals[off:].min()),
             'n_edges_checked': int(len(ineq_vals[off:])),
             'disk_margins_min': float(min(ineq_vals[0:16:2])) if h > 0 else None,
             'chord_margins_min': float(min(ineq_vals[1:16:2])) if h > 0 else None,
             'unit_norm_max_err': float(np.max(np.abs(np.array([np.linalg.norm(U[i]) - 1
                                                                for i in range(9)])))),
             'U_deviation_max_rad': float(np.max([abs(np.arctan2(U[i][1], U[i][0]) -
                                                      2 * np.pi * i / 9) for i in range(9)]))}
    mv = getattr(res, 'multipliers', None)
    if mv is not None:
        mv = np.atleast_1d(mv)
        lam_all = mv[-len(cons):] if mv.size >= len(cons) else None
        if lam_all is not None:
            edge_lam = np.array([abs(v) for v in lam_all[-51:]])       # 51 EDGE multipliers only
            entry['sum_abs_edge_lambda'] = float(np.sum(edge_lam))
            entry['n_edge_lambda_gt_1e-10'] = int(np.sum(edge_lam > 1e-10))
            # forces p_e = 2 lambda_e (C - U) resp. 2 lambda_e (C - Z), and the direct free balances
            p = []
            for k in range(18):
                i, anc = k // 2, (k // 2 if k % 2 == 0 else (k // 2 - 1) % 9)
                p.append(2 * lam_all[-51 + k] * (c[i] - U[anc]))
            for k in range(33):
                fi = 5 + k // 3 if k // 3 >= 5 else k // 3
                fi = [f for f in range(11)][k // 3]
                s_ = FACES[fi][k % 3]
                p.append(2 * lam_all[-51 + 18 + k] * (c[s_] - z[fi]))
            p = np.array(p)
            bal = np.zeros((22, 2))
            for k in range(18):
                i, anc = k // 2, (k // 2 if k % 2 == 0 else (k // 2 - 1) % 9)
                bal[i] += p[k]
            for k in range(33):
                fi = k // 3
                s_ = FACES[fi][k % 3]
                bal[s_] += p[18 + k]
                bal[11 + fi] -= p[18 + k]
            entry['direct_free_balance_max_abs'] = float(np.max(np.abs(bal)))
            entry['sum_abs_p'] = float(np.sum(np.abs(p)))
            exports[h] = {'U': U.tolist(), 'C': c.tolist(), 'Z': z.tolist(),
                          'edge_lambda_51': [float(v) for v in lam_all[-51:]],
                          'p_51': p.tolist(),
                          'free_node_balances': bal.tolist(),
                          'sum_abs_edge_lambda': float(np.sum(edge_lam)),
                          'direct_free_balance_max_abs': float(np.max(np.abs(bal))),
                          'sum_abs_p': float(np.sum(np.abs(p)))}
    out['runs'].append(entry)
(OUT / 'socp_sector_pilot.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
(OUT / 'socp_sector_export.json').write_text(
    json.dumps({'R_STAR_label': 'C529 rational (NOT C891)', 'R_star': R_STAR,
                'note': 'edge lambda are the 51 distance-edge multipliers only (sector '
                        'multipliers excluded); p_e = 2 lambda_e (C-U / C-Z); free-node '
                        'balances are DIRECT sums of p', 'runs': exports}, indent=2),
    encoding='utf-8')
print(json.dumps(out, indent=1))
