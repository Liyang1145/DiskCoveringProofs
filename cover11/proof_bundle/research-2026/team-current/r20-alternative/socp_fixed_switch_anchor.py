"""socp_fixed_switch_anchor.py  (r20-alternative; sole write, no child)

Bounded experiment per lead (numeric scope only):
  * baseline U = saved switches, 5 SLSQP runs from different starts near the primal;
  * +-0.01 rad single-switch perturbations (legal switch moves), 5 runs each;
  * per run report  V - R*  and the objective/dual-balance reading;
  * diagnostics of the baseline optimum: SOCP sites vs saved sites (centres difference),
    per-edge residuals, and the two slack faces checked INDIVIDUALLY (no lazy min<tol test).

NOTE (lead): the numerical min-r match is SHARPNESS EVIDENCE, not a proof of "no gap".
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
NV = 45


def switches(shift=None, kshift=0, dtheta=0.0):
    U = []
    for i in range(9):
        a_, b_ = C0[i], C0[(i + 1) % 9]
        m_ = (a_ + b_) / 2
        d_ = np.linalg.norm(b_ - a_)
        n_ = np.array([-(b_[1] - a_[1]) / d_, (b_[0] - a_[0]) / d_])
        mn = float(m_ @ n_)
        disc = np.sqrt(mn * mn + 1 - float(m_ @ m_))
        cand = [m_ + (-mn + disc) * n_, m_ + (-mn - disc) * n_]
        cand.sort(key=lambda P: max(np.linalg.norm(P - a_), np.linalg.norm(P - b_)))
        U.append(cand[0])
    U = np.array(U)
    if dtheta != 0.0:
        th = np.arctan2(U[kshift, 1], U[kshift, 0]) + dtheta
        U[kshift] = np.array([np.cos(th), np.sin(th)])
    return U


def build(U):
    def unpack(x):
        return x[:22].reshape(11, 2), x[22:44].reshape(11, 2), x[44]

    def obj(x):
        return x[44]

    def obj_grad(x):
        g = np.zeros(NV)
        g[44] = 1.0
        return g

    cons = []

    def mk(dim, site_or_face, pt, sign=1.0):
        def f(x):
            c, z, r = unpack(x)
            if dim == 'end':
                return r * r - float(np.sum((c[site_or_face] - pt)**2))
            return r * r - float(np.sum((c[site_or_face] - z[pt])**2))

        def jac(x):
            c, z, r = unpack(x)
            g = np.zeros(NV)
            if dim == 'end':
                g[2 * site_or_face:2 * site_or_face + 2] = -2 * (c[site_or_face] - pt)
            else:
                g[2 * site_or_face:2 * site_or_face + 2] = -2 * (c[site_or_face] - z[pt])
                g[22 + 2 * pt:22 + 2 * pt + 2] = 2 * (c[site_or_face] - z[pt])
            g[44] = 2 * r
            return g
        return {'type': 'ineq', 'fun': f, 'jac': jac}

    for i in range(9):
        cons.append(mk('end', i, U[i]))
        cons.append(mk('end', i, U[(i - 1) % 9]))
    for fi, face in enumerate(FACES):
        for s in face:
            cons.append(mk('face', s, fi))
    return unpack, obj, obj_grad, cons


def circumcenter(tri):
    P = C0[tri]
    A = np.column_stack([2 * (P[1] - P[0]), 2 * (P[2] - P[0])])
    b = np.array([P[1] @ P[1] - P[0] @ P[0], P[2] @ P[2] - P[0] @ P[0]])
    return np.linalg.solve(A, b)


def start(scale, seed):
    rng = np.random.default_rng(seed)
    x = np.zeros(NV)
    x[:22] = C0.reshape(-1)
    for fi, face in enumerate(FACES):
        x[22 + 2 * fi:22 + 2 * fi + 2] = circumcenter(face)
    x[44] = 0.38
    x[:44] += scale * rng.standard_normal(44)
    return x


def run(U, nstart=5, scale=1e-3):
    unpack, obj, obj_grad, cons = build(U)
    best = None
    vals = []
    for k in range(nstart):
        res = minimize(obj, start(scale, k), jac=obj_grad, method='SLSQP',
                       bounds=[(None, None)] * 44 + [(0.3, 0.45)], constraints=cons,
                       options={'maxiter': 300, 'ftol': 1e-13})
        vals.append(float(res.fun))
        if best is None or res.fun < best[0]:
            best = (float(res.fun), res, unpack)
    return vals, best


out = {'scope': 'numeric bounded experiment (no grid); min-r numerical match is SHARPNESS '
                'EVIDENCE, not a proof of no-gap',
       'R_star': R_STAR}
U0 = switches()
vals, best = run(U0, 5)
V0 = min(vals)
unpack, obj, obj_grad, cons = build(U0)
c_o, z_o, r_o = unpack(best[1].x)
res_list = [float(cc['fun'](best[1].x)) for cc in cons]
out['baseline'] = {'V': V0, 'V_minus_R_star': V0 - R_STAR,
                   'all_5_runs': vals,
                   'sites_max_delta_vs_saved': float(np.max(np.abs(c_o - C0))),
                   'endpoint_residuals_(least_negative_first)':
                       sorted(res_list[:18])[:4],
                   'face_residuals_ranked': sorted(res_list[18:18 + 33])[:6],
                   'two_slack_faces_individually':
                       {'face_9_(5,6,9)': sorted([res_list[18 + 3 * 9 + t] for t in range(3)]),
                        'face_10_(7,8,9)': sorted([res_list[18 + 3 * 10 + t] for t in range(3)])},
                   'n_endpoint_active_1e-9': int(sum(1 for v in res_list[:18] if abs(v) < 1e-9)),
                   'n_face_active_1e-9': int(sum(1 for v in res_list[18:] if abs(v) < 1e-9))}
pert = {}
for (k, dth) in ((0, 0.01), (0, -0.01), (4, 0.01), (4, -0.01)):
    U = switches(kshift=k, dtheta=dth)
    vals, best = run(U, 5)
    pert['switch%d_%+0.2frad' % (k, dth)] = {'V': min(vals), 'V_minus_R_star': min(vals) - R_STAR,
                                             'all_5_runs': vals}
out['perturbations'] = pert
out['outer_gradient_readings'] = {
    'dL/dtheta_switch0_central':
        (pert['switch0_+0.01rad']['V'] - pert['switch0_-0.01rad']['V']) / 0.02,
    'dL/dtheta_switch4_central':
        (pert['switch4_+0.01rad']['V'] - pert['switch4_-0.01rad']['V']) / 0.02,
    'note': 'central differences of the outer value V(U) at the candidate; |-| ~ 0 is consistent '
            'with the candidate being a stationary point of the outer problem (numeric)'}
(OUT / 'socp_fixed_switch_anchor.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
print(json.dumps(out, indent=1))
