"""socp_fixed_switch_pilot.py  (r20-alternative; sole write, no child)

Lead obligation: ONE bounded pilot of the FULL free-site fixed-switch convex relaxation
(representation taken from r20-gluing/SOCP-RELAXATION-INDEPENDENT-CHECK.md (a); its dual-zero
claim is NOT used):

  fix the nine boundary switches U_i (computed from the saved ring centres), free sites
  c (11 x R^2), aux z_f (11 x R^2), variable radius r:
      min r
      s.t.  |c_i - U_i| <= r  and  |c_i - U_{i-1}| <= r          (18 endpoint constraints)
            |c_s - z_f| <= r   for every face f and site s in f   (33 face cones)
  (convex; a relaxation of the cover problem, hence SOCP_min(U) <= R*)

  Candidate U_i => bounded pilot: does the optimum equal R* or is there a relaxation gap?
  Environment NOT modified: cvxpy absent (checked), so scipy SLSQP with analytic gradients,
  one bounded run.  Dual: report SLSQP multipliers if returned (the min-r dual question is
  explicitly NOT decided here).
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
C0 = Pf[NEW2RAW_RINGS + [2, 0]]                 # 9 rings + hubB + hubA (labelling as before)
R_STAR = float(F(3799838531198387090485182, 10**25))
graph = json.loads((ROOT / 'research-2026/team-current/lead/q0_graphs.json').read_text())[2]
FACES = [list(f) for f in graph['faces']]

# ---- switches U_i on the unit circle (radical line of adjacent ring pair) -----------
U = []
for i in range(9):
    a_, b_ = C0[i], C0[(i + 1) % 9]
    m_ = (a_ + b_) / 2
    d_ = np.linalg.norm(b_ - a_)
    n_ = np.array([-(b_[1] - a_[1]) / d_, (b_[0] - a_[0]) / d_])
    mn = float(m_ @ n_)
    disc = np.sqrt(mn * mn + 1 - float(m_ @ m_))
    cand = [m_ + (-mn + disc) * n_, m_ + (-mn - disc) * n_]
    # the covered switch is the unit-circle intersection with the SMALLER common distance
    cand.sort(key=lambda P: max(np.linalg.norm(P - a_), np.linalg.norm(P - b_)))
    U.append(cand[0])
U = np.array(U)
chords = [np.linalg.norm(U[(i + 1) % 9] - U[i]) for i in range(9)]

NV = 11 * 2 + 11 * 2 + 1                       # c(22) + z(22) + r
NP = 3 * 2                                     # npair per ring constraint (c_i, U)


def unpack(x):
    c = x[:22].reshape(11, 2)
    z = x[22:44].reshape(11, 2)
    r = x[44]
    return c, z, r


def obj(x):
    return x[44]


def obj_grad(x):
    g = np.zeros(NV)
    g[44] = 1.0
    return g


def constraints_list():
    cons = []

    def make_endpoint(i, Uj):
        def f(x):
            c, z, r = unpack(x)
            return r * r - float(np.sum((c[i] - Uj)**2))
        def jac(x):
            c, z, r = unpack(x)
            g = np.zeros(NV)
            g[2 * i:2 * i + 2] = -2 * (c[i] - Uj)
            g[44] = 2 * r
            return g
        return {'type': 'ineq', 'fun': f, 'jac': jac}
    for i in range(9):
        cons.append(make_endpoint(i, U[i]))
        cons.append(make_endpoint(i, U[(i - 1) % 9]))

    def make_face(f, s):
        def f_(x):
            c, z, r = unpack(x)
            return r * r - float(np.sum((c[s] - z[f])**2))
        def jac(x):
            c, z, r = unpack(x)
            g = np.zeros(NV)
            g[2 * s:2 * s + 2] = -2 * (c[s] - z[f])
            g[22 + 2 * f:22 + 2 * f + 2] = 2 * (c[s] - z[f])
            g[44] = 2 * r
            return g
        return {'type': 'ineq', 'fun': f_, 'jac': jac}
    for fi, face in enumerate(FACES):
        for s in face:
            cons.append(make_face(fi, s))
    return cons


def circumcenter(tri):
    P = C0[tri]
    A = np.column_stack([2 * (P[1] - P[0]), 2 * (P[2] - P[0])])
    b = np.array([P[1] @ P[1] - P[0] @ P[0], P[2] @ P[2] - P[0] @ P[0]])
    return np.linalg.solve(A, b)


x0 = np.zeros(NV)
x0[:22] = C0.reshape(-1)
for fi, face in enumerate(FACES):
    x0[22 + 2 * fi:22 + 2 * fi + 2] = circumcenter(face)
x0[44] = 0.38
bnds = [(None, None)] * 44 + [(0.3, 0.45)]
res = minimize(obj, x0, jac=obj_grad, method='SLSQP', bounds=bnds,
               constraints=constraints_list(),
               options={'maxiter': 400, 'ftol': 1e-12})
c_o, z_o, r_o = unpack(res.x)
out = {'model': 'free-site fixed-switch SOCP relaxation (min r); scipy SLSQP w/ analytic jac',
       'cvxpy_available': False, 'R_star': R_STAR,
       'optimum_r': float(r_o),
       'equals_R_star': bool(abs(r_o - R_STAR) < 1e-9),
       'gap_R_star_minus_opt': float(R_STAR - r_o),
       'chord_lower_bound': float(max(chords) / 2),
       'success': bool(res.success), 'status': str(res.status),
       'n_iter': int(res.nit), 'max_violation_final':
           float(max([-cc['fun'](res.x) for cc in constraints_list()])),
       'active_endpoint_constraints':
           int(sum(1 for cc in constraints_list()[:18] if -cc['fun'](res.x) < 1e-10)),
       'active_face_constraints':
           int(sum(1 for cc in constraints_list()[18:] if -cc['fun'](res.x) < 1e-10)),
       'has_multipliers': bool(hasattr(res, 'multipliers') and res.multipliers is not None)}
if out['has_multipliers']:
    out['multipliers_tail'] = [float(v) for v in np.atleast_1d(res.multipliers)[-6:]]
(OUT / 'socp_fixed_switch_pilot.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
print(json.dumps(out, indent=1))
