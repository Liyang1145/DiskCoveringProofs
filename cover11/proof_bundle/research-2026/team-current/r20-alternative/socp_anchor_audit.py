"""socp_anchor_audit.py  (r20-alternative; sole write, no child)

Corrected audit of the fixed-switch SOCP anchor experiment (lead source review applied):

BUG FIXES (preserved causes; see r20-alternative/socp_fixed_switch_anchor.py history):
  * circumcenter: np.column_stack made a transposed 2x2 system -> np.stack([...], axis=0);
  * active-set count tested  -slack < tol  (counted ALL feasible constraints!) -> abs(slack) < tol;
    the earlier "18/33 all active" artifact had THIS sign cause, not a loose tolerance;
  * multipliers must be converted for the SQUARED cone form:  alpha_e = 2 r lambda_e.

Outputs
  (1) full slack arrays: 18 endpoint residuals + 33 face residuals (3 per face, per face listed),
      sign convention residual = r^2 - |.|^2 (>= 0 feasible); the two slack faces must show
      Rc - r = -1.153e-3 i.e. residual ~ +2*r*1.153e-3;
  (2) KKT: free-gradient residual norm (Lagrangian under the NORM form), sum of alpha_e, and the
      per-switch anchor load decomposed into radial/tangential components;
  (3) switch legality: arc widths after perturbation vs the cap 0.779593 (candidate max ~0.776).
Numeric scope only; smoothness/stationarity are reported as observations, NOT conclusions.
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
CAP = 0.779593


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
    """FIXED: rows are the two normal equations (was np.column_stack -> transposed system)"""
    P = C0[tri]
    M = np.stack([2 * (P[1] - P[0]), 2 * (P[2] - P[0])], axis=0)
    b = np.array([P[1] @ P[1] - P[0] @ P[0], P[2] @ P[2] - P[0] @ P[0]])
    return np.linalg.solve(M, b)


def circumradius(tri):
    P = C0[tri]
    a2 = float(np.sum((P[1] - P[2])**2))
    b2 = float(np.sum((P[0] - P[2])**2))
    c2 = float(np.sum((P[0] - P[1])**2))
    X = float((P[1] - P[0])[0] * (P[2] - P[0])[1] - (P[1] - P[0])[1] * (P[2] - P[0])[0])
    return np.sqrt(a2 * b2 * c2) / (2 * abs(X))


def build(U):
    def unpack(x):
        return x[:22].reshape(11, 2), x[22:44].reshape(11, 2), x[44]
    cons = []

    def mk_end(i, Uj):
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
        return {'type': 'ineq', 'fun': f, 'jac': jac}
    for i in range(9):
        cons.append(mk_end(i, U[i]))
        cons.append(mk_end(i, U[(i - 1) % 9]))
    for fi, face in enumerate(FACES):
        for s in face:
            cons.append(mk_face(fi, s))
    return unpack, cons


U0 = switches()
unpack, cons = build(U0)
x0 = np.zeros(NV)
x0[:22] = C0.reshape(-1)
for fi, face in enumerate(FACES):
    x0[22 + 2 * fi:22 + 2 * fi + 2] = circumcenter(face)
x0[44] = 0.38
res = minimize(lambda x: x[44], x0, jac=lambda x: np.r_[np.zeros(44), 1.0], method='SLSQP',
               bounds=[(None, None)] * 44 + [(0.3, 0.45)], constraints=cons,
               options={'maxiter': 400, 'ftol': 1e-14})
c_o, z_o, r_o = unpack(res.x)
slacks = np.array([cc['fun'](res.x) for cc in cons])
ep, fc = slacks[:18], slacks[18:]
rep = {'scope': 'numeric corrected audit; smoothness/stationarity NOT concluded',
       'R_star': R_STAR, 'V': float(res.fun), 'V_minus_R_star': float(res.fun) - R_STAR,
       'success': bool(res.success), 'nit': int(res.nit),
       'endpoint_slacks_(18, residual=r^2-|c-U|^2)': [float(v) for v in ep],
       'face_slacks_(33, 3 per face, order = FACES)': [float(v) for v in fc],
       'active_count_abs_slack_lt_1e-12': int(np.sum(np.abs(slacks) < 1e-12)),
       'active_count_abs_slack_lt_1e-9': int(np.sum(np.abs(slacks) < 1e-9)),
       'per_face_Rc_minus_r': [float(circumradius(f) - R_STAR) for f in FACES],
       'two_slack_faces_Rc_minus_r':
           {'face_9': float(circumradius(FACES[9]) - R_STAR),
            'face_10': float(circumradius(FACES[10]) - R_STAR)},
       'sites_max_delta_vs_saved': float(np.max(np.abs(c_o - C0)))}
# ---- KKT / anchor load ---------------------------------------------------------------
mult = None
if hasattr(res, 'multipliers') and res.multipliers is not None:
    mv = np.atleast_1d(res.multipliers)
    if mv.size >= len(cons):
        mult = mv[-len(cons):]
if mult is not None:
    r_at = float(r_o)
    alpha = 2 * r_at * mult                     # squared-ineq -> NORM-form multiplier
    rep['sum_alpha_norm_form'] = float(np.sum(alpha))
    # Lagrangian under the norm form: 1 (r) + sum alpha_e * unit-gradient terms
    gL = np.zeros(NV)
    gL[44] = 1.0
    for cc, al in zip(cons, alpha):
        if al > 0:
            gL += -al * cc['jac'](res.x)        # derivative of the residual r^2-|.|^2 -> -jac
    rep['free_gradient_residual_norm'] = float(np.linalg.norm(gL[:44]))
    rep['obj_coordinate_gradient'] = float(gL[44])
    loads = []
    for i in range(9):
        lam_i = alpha[2 * i]
        lam_im1 = alpha[2 * ((i - 1) % 9) + 1]
        Ui = U0[i]
        tang = np.array([-Ui[1], Ui[0]])
        loads.append({'switch': i, 'alpha_next': float(lam_i), 'alpha_prev': float(lam_im1),
                      'total': float(lam_i + lam_im1),
                      'radial': float((lam_i + lam_im1)),
                      'tangential_estimate': float(0.0)})
    rep['anchor_loads'] = loads
    rep['sum_alpha_check'] = float(sum(x['total'] for x in loads))
else:
    rep['multipliers'] = 'not returned by this scipy build'
# ---- switch legality -----------------------------------------------------------------
widths = [float(np.arccos(np.clip(U0[i] @ U0[(i + 1) % 9], -1, 1))) for i in range(9)]
rep['arc_widths_rad'] = widths
rep['max_arc_width'] = max(widths)
rep['legality_cap'] = CAP
rep['legal_baseline'] = bool(max(widths) <= CAP)
rep['perturb_note'] = ('a +/-0.01 rad move of one switch changes two adjacent widths by ~0.01 rad; '
                       'the two widest arcs are %.6f and %.6f (cap %.6f) so any perturbed anchor '
                       'is legal only if max width stays <= cap -- otherwise it is an ARBITRARY '
                       'anchor, not a legal pilot.' % (widths[int(np.argmax(widths))],
                                                       sorted(widths)[-2], CAP))
(OUT / 'socp_anchor_audit.json').write_text(json.dumps(rep, indent=2), encoding='utf-8')
print(json.dumps({k: v for k, v in rep.items()
                  if k not in ('endpoint_slacks_(18, residual=r^2-|c-U|^2)',
                               'face_slacks_(33, 3 per face, order = FACES)', 'anchor_loads')},
                 indent=1))
print('endpoint slacks:', [round(v, 14) for v in rep['endpoint_slacks_(18, residual=r^2-|c-U|^2)']])
print('face slacks (3 per face):',
      {i: [round(v, 12) for v in rep['face_slacks_(33, 3 per face, order = FACES)'][3 * i:3 * i + 3]]
       for i in range(11)})
print('per-face Rc - r:', [round(v, 9) for v in rep['per_face_Rc_minus_r']])

# ---- anchor load (tangential/radial) at the baseline, from the scipy multipliers -----
if mult is not None:
    loads = []
    for i in range(9):
        Ui = U0[i]
        perp = np.array([-Ui[1], Ui[0]])
        Fv = np.zeros(2)
        for (kk, a) in ((i, alpha[2 * i]), ((i - 1) % 9, alpha[2 * ((i - 1) % 9) + 1])):
            v = c_o[kk] - Ui
            nv = float(np.linalg.norm(v))
            if nv > 0:
                Fv += a * v / nv
        loads.append({'switch': i, 'radial': float(Fv @ Ui), 'tangential': float(Fv @ perp),
                      'alpha_next': float(alpha[2 * i]),
                      'alpha_prev': float(alpha[2 * ((i - 1) % 9) + 1])})
    rep['anchor_loads'] = loads
    (OUT / 'socp_anchor_audit.json').write_text(json.dumps(rep, indent=2), encoding='utf-8')
    print('anchor loads (radial, tangential):',
          [(l['switch'], round(l['radial'], 6), round(l['tangential'], 8)) for l in loads])
