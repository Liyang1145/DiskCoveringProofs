"""socp_anchor_export.py  (r20-alternative; sole write, no child)

URGENT audit fix (lead): the anchor load at switch U_i involves the edges
    ring i     endpoint U_i        -> constraint index [i*2]
    ring i+1   endpoint U_i        -> constraint index [((i+1)%9)*2 + 1]
(NOT [2i, 2i+1] as used before).  Correct load (norm form):
    F_i = alpha_e * unit(U_i - c_i) + alpha_e' * unit(U_i - c_{i+1}),  alpha_k = 2 r lambda_k.

Exports for the chain (not just a tail):
  all 51 squared-form lambdas, the norm-form alphas, the edge incidence map, U, C, Z,
  per-anchor radial/tangential load, total torque, and the exported arrays.
Numeric scope; no smoothness/stationarity conclusion.
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


def switches():
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
    return np.array(U)


def circumcenter(tri):
    P = C0[tri]
    M = np.stack([2 * (P[1] - P[0]), 2 * (P[2] - P[0])], axis=0)
    b = np.array([P[1] @ P[1] - P[0] @ P[0], P[2] @ P[2] - P[0] @ P[0]])
    return np.linalg.solve(M, b)


def build(U):
    def unpack(x):
        return x[:22].reshape(11, 2), x[22:44].reshape(11, 2), x[44]
    cons = []
    inc = []                                    # (kind, site, anchor/face index)

    def mk_end(i, anchor):
        def f(x):
            c, z, r = unpack(x)
            return r * r - float(np.sum((c[i] - U[anchor])**2))

        def jac(x):
            c, z, r = unpack(x)
            g = np.zeros(NV)
            g[2 * i:2 * i + 2] = -2 * (c[i] - U[anchor])
            g[44] = 2 * r
            return g
        cons.append({'type': 'ineq', 'fun': f, 'jac': jac})
        inc.append(('endpoint', i, anchor))

    def mk_face(fi, s):
        def f(x):
            c, z, r = unpack(x)
            return r * r - float(np.sum((c[s] - z[fi])**2))

        def jac(x):
            c, z, r = unpack(x)
            g = np.zeros(NV)
            g[2 * s:2 * s + 2] = -2 * (c[s] - z[fi])
            g[22 + 2 * fi:22 + 2 * fi + 2] = 2 * (c[s] - z[fi])
            g[44] = 2 * r
            return g
        cons.append({'type': 'ineq', 'fun': f, 'jac': jac})
        inc.append(('face', s, fi))
    for i in range(9):                          # order fixed by this loop
        mk_end(i, i)
        mk_end(i, (i - 1) % 9)
    for fi, face in enumerate(FACES):
        for s in face:
            mk_face(fi, s)
    return unpack, cons, inc


U0 = switches()
unpack, cons, inc = build(U0)
x0 = np.zeros(NV)
x0[:22] = C0.reshape(-1)
for fi, face in enumerate(FACES):
    x0[22 + 2 * fi:22 + 2 * fi + 2] = circumcenter(face)
x0[44] = 0.38
res = minimize(lambda x: x[44], x0, jac=lambda x: np.r_[np.zeros(44), 1.0], method='SLSQP',
               bounds=[(None, None)] * 44 + [(0.3, 0.45)], constraints=cons,
               options={'maxiter': 400, 'ftol': 1e-14})
c_o, z_o, r_o = unpack(res.x)
mv = np.atleast_1d(res.multipliers)
lam = mv[-len(cons):]                            # squared-form multipliers, 51 entries
alpha = 2 * float(r_o) * lam                      # norm form
# index map: endpoint slot for (ring i, anchor j) is the entry whose incidence matches
slot = {}
for idx, (kind, site, an) in enumerate(inc):
    if kind == 'endpoint':
        slot[(site, an)] = idx
loads = []
for i in range(9):
    e1 = slot[(i, i)]                             # ring i endpoint U_i
    e2 = slot[((i + 1) % 9, i)]                   # ring i+1 endpoint U_i
    Fv = np.zeros(2)
    for (e, ck) in ((e1, c_o[i]), (e2, c_o[(i + 1) % 9])):
        v = U0[i] - ck
        nv = float(np.linalg.norm(v))
        if nv > 0:
            Fv += alpha[e] * v / nv
    perp = np.array([-U0[i, 1], U0[i, 0]])
    loads.append({'switch': i,
                  'constraint_indices': [int(e1), int(e2)],
                  'rings': [i, (i + 1) % 9],
                  'lambda_squared': [float(lam[e1]), float(lam[e2])],
                  'alpha_norm': [float(alpha[e1]), float(alpha[e2])],
                  'dist_minus_r': [float(np.linalg.norm(U0[i] - c_o[i]) - r_o),
                                   float(np.linalg.norm(U0[i] - c_o[(i + 1) % 9]) - r_o)],
                  'load_xy': [float(Fv[0]), float(Fv[1])],
                  'radial': float(Fv @ U0[i]), 'tangential': float(Fv @ perp)})
torque = float(sum(U0[i, 0] * loads[i]['load_xy'][1] - U0[i, 1] * loads[i]['load_xy'][0]
                   for i in range(9)))
exp = {'scope': 'numeric; corrected edge incidence; no smoothness/stationarity conclusion',
       'R_star': R_STAR, 'V': float(res.fun), 'V_minus_R_star': float(res.fun) - R_STAR,
       'r_solution': float(r_o),
       'lambda_all_51_squared_form': [float(v) for v in lam],
       'alpha_all_51_norm_form_2r_lambda': [float(v) for v in alpha],
       'sum_alpha': float(np.sum(alpha)),
       'incidence_map': [[str(k), int(s), int(t)] for (k, s, t) in inc],
       'U': U0.tolist(), 'C_sites': c_o.tolist(), 'Z_aux': z_o.tolist(),
       'anchor_loads': loads,
       'sum_radial': float(sum(l['radial'] for l in loads)),
       'sum_tangential': float(sum(l['tangential'] for l in loads)),
       'total_torque': torque}
(OUT / 'socp_anchor_export.json').write_text(json.dumps(exp, indent=2), encoding='utf-8')
print('V-R* =', exp['V_minus_R_star'], ' r =', exp['r_solution'], ' sum_alpha =', exp['sum_alpha'])
print('anchor (radial, tangential):',
      [(l['switch'], round(l['radial'], 6), round(l['tangential'], 6)) for l in loads])
print('sum radial =', round(exp['sum_radial'], 8), ' sum tangential =',
      round(exp['sum_tangential'], 8), ' torque =', exp['total_torque'])
print('EXPORT ->', (OUT / 'socp_anchor_export.json').name, 'keys:', list(exp.keys()))
