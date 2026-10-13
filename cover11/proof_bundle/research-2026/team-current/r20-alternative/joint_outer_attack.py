"""joint_outer_attack.py  (r20-alternative; sole write, no child; NUMERIC only)

Lead task: JOINT nonconvex outer-angle + SOCP primal attack on  min_P V  (P = angles + primal),
NOT a discrete resampling.  53 variables = theta_1..theta_8 (theta_0 = 0 fixed) + sites c (22)
+ aux z (22) + r; legality is LINEAR in theta with the TRUE cap L = 2*arcsin(0.38):
    L_i = theta_{i+1} - theta_i  (theta_0 = 0, theta_9 = 2*pi),   eps <= L_i <= L.
Constraints: 18 endpoint cones + 33 face cones (analytic jac including d/dtheta).
Seeds (<= 12, deterministic): candidate widths, uniform, the nine capped-simplex vertices
(w_k = m, others = L), and one asymmetric 0.5*(candidate + vertex_3).
Budget: <= 600 SLSQP iterations per seed, <= 90 s total, stop when 12 seeds are done.
GOAL: find a seed with V < R* - 1e-7 that ALSO passes the direct 51-constraint check and is
legal.  A null result is NOT a global proof.

R* label: C529 rational value (0.37998385311983873), used only for numeric differences.
"""
import json
import time
import numpy as np
from fractions import Fraction as F
from pathlib import Path
from scipy.optimize import minimize

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
LOG = OUT / 'joint_outer_attack.log'
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
Pf = np.array([[float(F(int(v[0]), 10**17)), float(F(int(v[1]), 10**17))]
               for v in raw['centers_scaled_1e17']])
NEW2RAW_RINGS = [5, 7, 1, 8, 6, 4, 9, 10, 3]
C0 = Pf[NEW2RAW_RINGS + [2, 0]]
R_STAR = float(F(3799838531198387090485182, 10**25))
graph = json.loads((ROOT / 'research-2026/team-current/lead/q0_graphs.json').read_text())[2]
FACES = [list(f) for f in graph['faces']]
L_CAP = 2 * np.arcsin(0.38)
EPS_MIN = 1e-4
NTH, NTOT = 8, 53
IC, IZ = 8, 30
T0 = time.time()
BUDGET = 90.0


def log(msg):
    with open(LOG, 'a', encoding='utf-8') as fh:
        fh.write(msg + '\n')


def angles_from_widths(w):
    th = np.concatenate([[0.0], np.cumsum(w)])
    return th[:9]


def U_from_angles(th):
    return np.stack([np.cos(th), np.sin(th)], axis=1)


def cand_widths():
    S = []
    for i in range(9):
        a_, b_ = C0[i], C0[(i + 1) % 9]
        m_ = (a_ + b_) / 2
        d_ = np.linalg.norm(b_ - a_)
        n_ = np.array([-(b_[1] - a_[1]) / d_, (b_[0] - a_[0]) / d_])
        mn = float(m_ @ n_)
        disc = np.sqrt(mn * mn + 1 - float(m_ @ m_))
        cand = [m_ + (-mn + disc) * n_, m_ + (-mn - disc) * n_]
        cand.sort(key=lambda P: max(np.linalg.norm(P - a_), np.linalg.norm(P - b_)))
        S.append(cand[0])
    S = np.array(S)
    return np.array([np.arccos(np.clip(S[i] @ S[(i + 1) % 9], -1, 1)) for i in range(9)])


def candidate_switches():
    S = []
    for i in range(9):
        a_, b_ = C0[i], C0[(i + 1) % 9]
        m_ = (a_ + b_) / 2
        d_ = np.linalg.norm(b_ - a_)
        n_ = np.array([-(b_[1] - a_[1]) / d_, (b_[0] - a_[0]) / d_])
        mn = float(m_ @ n_)
        disc = np.sqrt(mn * mn + 1 - float(m_ @ m_))
        cand = [m_ + (-mn + disc) * n_, m_ - (-mn - disc) * n_]
        cand = [m_ + (-mn + disc) * n_, m_ + (-mn - disc) * n_]
        cand.sort(key=lambda P: max(np.linalg.norm(P - a_), np.linalg.norm(P - b_)))
        S.append(cand[0])
    return np.array(S)


sw0 = candidate_switches()[0]


def build():
    def th_of(x):
        return np.concatenate([[0.0], x[:8]])

    def unpack(x):
        th = th_of(x)
        return U_from_angles(th), x[IC:IC + 22].reshape(11, 2), x[IZ:IZ + 22].reshape(11, 2), x[-1]
    def width_val(x, k):
        return (x[k] - (0.0 if k == 0 else x[k - 1])) if k < 8 else (2 * np.pi - x[7])

    def width_grad(k):
        g = np.zeros(NTOT)
        if k < 8:
            g[k] = 1.0
        if k >= 1:
            g[k - 1] -= 1.0
        return g

    cons = []
    for k in range(9):                                    # widths: eps <= L_k <= L_CAP
        cons.append({'type': 'ineq',
                     'fun': lambda x, k=k: width_val(x, k) - EPS_MIN,
                     'jac': lambda x, k=k: width_grad(k)})
        cons.append({'type': 'ineq',
                     'fun': lambda x, k=k: L_CAP - width_val(x, k),
                     'jac': lambda x, k=k: -width_grad(k)})

    def mk_end(i, anchor):
        def f(x):
            U, c, z, r = unpack(x)
            return r * r - float(np.sum((c[i] - U[anchor])**2))

        def jac(x):
            U, c, z, r = unpack(x)
            g = np.zeros(NTOT)
            d = c[i] - U[anchor]
            g[IC + 2 * i:IC + 2 * i + 2] = -2 * d
            if anchor >= 1:
                # d/dtheta of  r^2 - |c - U|^2  =  -2 (c-U) . U'(theta) = 2 (c-U) . (sin, -cos)
                th_a = x[anchor - 1]
                # f = r^2 - |c - U|^2 ;  df/dtheta = -2 d . U'(theta) = 2(-d_x sin t + d_y cos t)
                g[anchor - 1] = 2 * float(-d[0] * np.sin(th_a) + d[1] * np.cos(th_a))
            g[-1] = 2 * r
            return g
        return {'type': 'ineq', 'fun': f, 'jac': jac}

    def mk_face(fi, s):
        def f(x):
            U, c, z, r = unpack(x)
            return r * r - float(np.sum((c[s] - z[fi])**2))

        def jac(x):
            U, c, z, r = unpack(x)
            g = np.zeros(NTOT)
            d = c[s] - z[fi]
            g[IC + 2 * s:IC + 2 * s + 2] = -2 * d
            g[IZ + 2 * fi:IZ + 2 * fi + 2] = 2 * d
            g[-1] = 2 * r
            return g
        return {'type': 'ineq', 'fun': f, 'jac': jac}
    for i in range(9):
        cons.append(mk_end(i, i))
        cons.append(mk_end(i, (i - 1) % 9))
    for fi, face in enumerate(FACES):
        for s in face:
            cons.append(mk_face(fi, s))
    return unpack, cons


def seed_x0(w, warm_sites=None):
    th = angles_from_widths(w)
    U = U_from_angles(th)
    x0 = np.zeros(NTOT)
    x0[:8] = th[1:]
    if warm_sites is not None:
        sites = np.array(warm_sites, dtype=float).copy()
    else:
        sites = np.zeros((11, 2))
        for i in range(9):
            mid = (U[i] + U[(i - 1) % 9]) / 2
            nrm = np.linalg.norm(mid)
            sites[i] = mid * (0.97 * min(1.0, 1.0 / max(nrm, 1e-9)))
        centroid = sites[:9].mean(axis=0)
        sites[9] = centroid * 0.5
        sites[10] = centroid * 0.35
    x0[IC:IC + 22] = sites.reshape(-1)
    zz = np.zeros((11, 2))
    for fi, face in enumerate(FACES):
        P = sites[face]
        M = np.stack([2 * (P[1] - P[0]), 2 * (P[2] - P[0])], axis=0)
        b = np.array([P[1] @ P[1] - P[0] @ P[0], P[2] @ P[2] - P[0] @ P[0]])
        try:
            zz[fi] = np.linalg.solve(M, b)
        except np.linalg.LinAlgError:
            zz[fi] = P.mean(axis=0)
    x0[IZ:IZ + 22] = zz.reshape(-1)
    x0[-1] = 0.40
    return x0, th


def jac_cs_check(seed=7, h=1e-7):
    """central-difference check of the analytic jacobians of ALL 69 constraints x 53 vars"""
    rng = np.random.default_rng(seed)
    w = 0.5 * cand_widths() + 0.5 * np.full(9, 2 * np.pi / 9)
    x0, th = seed_x0(w)
    xr = x0 + 1e-3 * rng.standard_normal(NTOT)
    xr[0:8] = np.sort(np.abs(xr[0:8])) + 0.05        # keep angles increasing-ish & non-degenerate
    unpack, cons = build()
    worst = 0.0
    worst_tag = None
    for ci, cc in enumerate(cons):
        ga = np.asarray(cc['jac'](xr), dtype=float)
        gc = np.zeros(NTOT)
        for k in range(NTOT):
            xp, xm = xr.copy(), xr.copy()
            xp[k] += h
            xm[k] -= h
            gc[k] = (cc['fun'](xp) - cc['fun'](xm)) / (2 * h)
        err = float(np.max(np.abs(ga - gc)))
        if err > worst:
            worst, worst_tag = err, 'constraint %d (type=%s)' % (ci, cc.get('type'))
    return {'n_constraints_checked': len(cons), 'n_variables': NTOT, 'max_jac_error': worst,
            'worst_constraint': worst_tag, 'step': h}


wc = cand_widths()
uniform = np.full(9, 2 * np.pi / 9)
m_small = 2 * np.pi - 8 * L_CAP
verts = []
for k in range(9):
    w = np.full(9, L_CAP)
    w[k] = m_small
    verts.append(w)
seeds = [('candidate_widths', wc), ('uniform', uniform)]
for k, w in enumerate(verts):
    seeds.append(('vertex%d' % k, w))
seeds.append(('asymmetric_mix', 0.5 * wc + 0.5 * verts[3]))
seeds = seeds[:12]
res_out = {'R_STAR_label': 'C529 rational value (NOT C891)', 'R_star': R_STAR,
           'L_cap': L_CAP, 'm_small': float(m_small), 'seeds': [],
           'target_V_lt_R_minus_1e7': R_STAR - 1e-7,
           'note': 'NUMERIC ONLY; a null result is NOT a global proof; budget 90 s / 12 seeds / '
                   '600 SLSQP iterations each; 53 variables (8 angles + 45 primal)'}
import sys
CAL_ONLY = '--calib' in sys.argv
sw_all = candidate_switches()
phi0 = float(np.arctan2(sw_all[0][1], sw_all[0][0]))
if CAL_ONLY:
    chk = jac_cs_check()
    Rm = np.array([[np.cos(-phi0), -np.sin(-phi0)], [np.sin(-phi0), np.cos(-phi0)]])
    warm = (Rm @ C0.T).T
    x0c, thc = seed_x0(cand_widths(), warm_sites=warm)
    unpack, cons = build()
    direct = np.array([cc['fun'](x0c) for cc in cons[18:]])
    cal = {'R_STAR_label': 'C529 rational (NOT C891)', 'R_star': R_STAR,
           'phi0_of_first_switch': phi0, 'jacobian_check': chk,
           'direct_51_distances_at_saved_candidate': {
               'min': float(direct.min()), 'max': float(direct.max()),
               'n_negative_lt_-1e-12': int(np.sum(direct < -1e-12))},
           'widths_at_candidate': [float(v) for v in cand_widths()],
           'widths_legal': bool(cand_widths().max() <= L_CAP + 1e-12)}
    res = minimize(lambda x: x[-1], x0c, jac=lambda x: np.r_[np.zeros(NTOT - 1), 1.0],
                   method='SLSQP', bounds=[(None, None)] * (NTOT - 1) + [(0.05, 0.6)],
                   constraints=cons, options={'maxiter': 600, 'ftol': 1e-12})
    ivals = np.array([cc['fun'](res.x) for cc in cons[18:]])
    cal['calibration_run'] = {'V': float(res.fun), 'V_minus_R_star': float(res.fun) - R_STAR,
                              'success': bool(res.success), 'nit': int(res.nit),
                              'min_51_edge_residual': float(ivals.min())}
    cal['PASS'] = bool(chk['max_jac_error'] < 1e-6 and abs(res.fun - R_STAR) < 1e-5
                       and ivals.min() > -1e-9)
    (OUT / 'joint_outer_calibration.json').write_text(json.dumps(cal, indent=2), encoding='utf-8')
    print(json.dumps(cal, indent=1))
    raise SystemExit(0)


log('=== joint outer attack start; L_CAP=%.12f m=%.11f R*=%.12f ===' % (L_CAP, m_small, R_STAR))
for name, w in seeds:
    if time.time() - T0 > BUDGET:
        log('[budget] stopping before seed %s' % name)
        break
    if name == 'candidate_widths':
        # rotate the saved centres by -phi_0 (phi_0 = angle of the candidate's first switch)
        phi0 = float(np.arctan2(sw0[1], sw0[0]))
        Rm = np.array([[np.cos(-phi0), -np.sin(-phi0)], [np.sin(-phi0), np.cos(-phi0)]])
        warm = (Rm @ C0.T).T
        x0, th = seed_x0(w, warm_sites=warm)
    else:
        x0, th = seed_x0(w)
    unpack, cons = build()
    t0 = time.time()
    res = minimize(lambda x: x[-1], x0, jac=lambda x: np.r_[np.zeros(NTOT - 1), 1.0],
                   method='SLSQP', bounds=[(None, None)] * (NTOT - 1) + [(0.05, 0.6)],
                   constraints=cons, options={'maxiter': 600, 'ftol': 1e-12})
    U, c, z, r = unpack(res.x)
    ivals = np.array([cc['fun'](res.x) for cc in cons[18:]])   # the 51 edges
    widths_out = np.diff(np.concatenate([[0.0], res.x[:8], [2 * np.pi]]))
    entry = {'seed': name, 'V': float(res.fun), 'V_minus_R_star': float(res.fun) - R_STAR,
             'success': bool(res.success), 'nit': int(res.nit), 'secs': round(time.time() - t0, 2),
             'min_51_edge_residual': float(ivals.min()),
             'widths': [float(v) for v in widths_out],
             'widths_legal': bool(widths_out.min() >= EPS_MIN - 1e-9
                                  and widths_out.max() <= L_CAP + 1e-9),
             'below_target_raw': bool(res.fun < R_STAR - 1e-7),
             'below_target': bool(res.fun < R_STAR - 1e-7
                                  and ivals.min() >= -1e-9
                                  and widths_out.min() >= EPS_MIN - 1e-9
                                  and widths_out.max() <= L_CAP + 1e-9),
             'diverged_or_infeasible': bool(ivals.min() < -1e-3
                                            or not (widths_out.min() >= EPS_MIN - 1e-9
                                                    and widths_out.max() <= L_CAP + 1e-9)),
             'sites': c.tolist(), 'aux': z.tolist(),
             'angles': [float(v) for v in res.x[:8]]}
    res_out['seeds'].append(entry)
    log('seed=%-16s V-R*=%.9e nit=%d secs=%.1f min51=%.2e widthsOK=%s target=%s diverged=%s'
        % (name, entry['V_minus_R_star'], entry['nit'], entry['secs'],
           entry['min_51_edge_residual'], entry['widths_legal'], entry['below_target'],
           entry['diverged_or_infeasible']))
(OUT / 'joint_outer_attack.json').write_text(json.dumps(res_out, indent=2), encoding='utf-8')
log('=== done in %.1f s; seeds=%d; any below target=%s ==='
    % (time.time() - T0, len(res_out['seeds']),
       any(e['below_target'] for e in res_out['seeds'])))
res_out['n_target_hits'] = int(sum(1 for e in res_out['seeds'] if e['below_target']))
res_out['n_diverged'] = int(sum(1 for e in res_out['seeds'] if e['diverged_or_infeasible']))
(OUT / 'joint_outer_attack.json').write_text(json.dumps(res_out, indent=2), encoding='utf-8')
print(json.dumps({k: v for k, v in res_out.items() if k != 'seeds'}, indent=1))
for e in res_out['seeds']:
    print('%-16s V-R*=%.9e nit=%3d min51=%.2e legal=%s target=%s diverged=%s'
          % (e['seed'], e['V_minus_R_star'], e['nit'], e['min_51_edge_residual'],
             e['widths_legal'], e['below_target'], e['diverged_or_infeasible']))
