"""socp_outer_attack.py  (r20-alternative; sole write, no child)

Lead obligation: independent numeric outer attack of the fixed-switch SOCP relaxation.
Pick <= 20 deterministic LEGAL Delta points (near-uniform + the capped-simplex vertices and
their convex mixtures with the uniform), compute V with the OPTIMISED primal, and stop early if
V < R* - 1e-6, rechecking all 51 edges by direct evaluation.  Tests whether the GLOBAL relaxation
route (8-corner search) is valid or false -- NOT the original theorem.

Legal domain: the nine arc widths w_i > 0 with sum 2*pi and w_i <= CAP = 2 * np.arcsin(0.38)     # EXACT cap 2*arcsin(r), r = 0.38; no rounding of the input (a capped
simplex; rotation is a symmetry so theta_0 = 0).  A "bad" point (V well below R*) would be saved
with its coordinates (a *relaxation* point, not yet a cover: this SOCP is necessary, not
sufficient, so realizability must be checked separately).
"""
import json
import itertools
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
CAP = 0.779593
graph = json.loads((ROOT / 'research-2026/team-current/lead/q0_graphs.json').read_text())[2]
FACES = [list(f) for f in graph['faces']]
NV = 45
TWO_PI = 2 * np.pi


def U_from_widths(w):
    th = np.concatenate([[0.0], np.cumsum(w)[:-1]])
    return np.stack([np.cos(th), np.sin(th)], axis=1)


def build(U):
    def unpack(x):
        return x[:22].reshape(11, 2), x[22:44].reshape(11, 2), x[44]

    cons = []

    def mk(end, site, pt):
        def f(x):
            c, z, r = unpack(x)
            t = pt if end else z[pt]
            return r * r - float(np.sum((c[site] - t)**2))

        def jac(x):
            c, z, r = unpack(x)
            g = np.zeros(NV)
            t = pt if end else z[pt]
            g[2 * site:2 * site + 2] = -2 * (c[site] - t)
            if not end:
                g[22 + 2 * pt:22 + 2 * pt + 2] = 2 * (c[site] - t)
            g[44] = 2 * r
            return g
        return {'type': 'ineq', 'fun': f, 'jac': jac}
    for i in range(9):
        cons.append(mk(True, i, U[i]))
        cons.append(mk(True, i, U[(i - 1) % 9]))
    for fi, face in enumerate(FACES):
        for s in face:
            cons.append(mk(False, s, fi))
    return unpack, cons


def circumcenter_of(sites):
    P = sites
    M = np.stack([2 * (P[1] - P[0]), 2 * (P[2] - P[0])], axis=0)
    b = np.array([P[1] @ P[1] - P[0] @ P[0], P[2] @ P[2] - P[0] @ P[0]])
    try:
        return np.linalg.solve(M, b)
    except np.linalg.LinAlgError:
        return P.mean(axis=0)


def jac_obj(x):
    return np.r_[np.zeros(44), 1.0]


def solve_V(U):
    unpack, cons = build(U)
    sites = np.zeros((11, 2))
    sites[:9] = (U + np.roll(U, 1, axis=0)) / 2          # arc midpoints, inside D
    sites[9] = np.array([0.0, 0.20])
    sites[10] = np.array([0.0, -0.12])
    x0 = np.zeros(NV)
    x0[:22] = sites.reshape(-1)
    z0 = np.zeros((11, 2))
    for fi, face in enumerate(FACES):
        z0[fi] = circumcenter_of(sites[face])
    x0[22:44] = z0.reshape(-1)
    x0[44] = 0.40
    res = minimize(lambda x: x[44], x0, jac=jac_obj, method='SLSQP',
                   bounds=[(None, None)] * 44 + [(0.05, 0.6)], constraints=cons,
                   options={'maxiter': 400, 'ftol': 1e-14})
    vals = np.array([cc['fun'](res.x) for cc in cons])
    return float(res.fun), res.x, float(vals.min())




def switches_candidate():
    # the saved switches (calibration point and half mixtures only)
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
    return np.array(S)


# ---- <= 19 deterministic legal Delta points ----------------------------------------
# CORRECTED legal domain (lead): cap L = CAP, and the nine vertices of the capped simplex
# {0 <= w_i <= L, sum w = 2*pi} are  (w_k = m, other eight = L)  with  m = 2*pi - 8L.
# (One slot = L with the others equal is a FACET CENTRE, not a vertex -- previous sampling error.)
L = CAP
m = TWO_PI - 8 * L
assert m > 0, 'cap too large for nine arcs'
verts = []
for k in range(9):
    w = np.full(9, L)
    w[k] = m
    verts.append(w)


def cand_widths():
    U = switches_candidate()
    return np.array([np.arccos(np.clip(U[i] @ U[(i + 1) % 9], -1, 1)) for i in range(9)])


wc = cand_widths()
points = [('calibration_candidate', wc)]
for k, w in enumerate(verts):
    points.append(('vertex%d(m,L..L)' % k, w))
for k, w in enumerate(verts):
    points.append(('halfmix_candidate_vertex%d' % k, 0.5 * wc + 0.5 * w))
points = points[:19]
out_extra = {'L_cap': L, 'm_small_vertex_width': float(m),
             'candidate_widths': [float(x) for x in wc],
             'candidate_deficits': [float(L - x) for x in wc],
             'deficit_sum': float(np.sum(L - wc))}
out = {'scope': 'numeric outer attack of the SOCP relaxation (tests the global relaxation route, '
                'NOT the theorem)',
       'R_star': R_STAR, 'cap': CAP, 'n_points': len(points), 'legal_domain': out_extra,
       'results': []}
bad = None
for name, w in points:
    if np.any(w <= 0) or np.any(w > CAP + 1e-12) or abs(w.sum() - TWO_PI) > 1e-9:
        out['results'].append({'name': name, 'legal': False})
        continue
    U = U_from_widths(w)
    V, x, minres = solve_V(U)
    e = {'name': name, 'legal': True, 'V': V, 'V_minus_R_star': V - R_STAR,
         'min_over_51_cone_residual': minres, 'w_max': float(w.max()),
         'below_R_minus_1e6': bool(V < R_STAR - 1e-6)}
    if e['below_R_minus_1e6']:
        unpack, cons = build(U)
        c, z, r = unpack(x)
        e['direct_all51_min_residual'] = minres
        e['r_achieved'] = float(r)
        bad = {'name': name, 'U': U.tolist(), 'C': c.tolist(), 'Z': z.tolist(),
               'r': float(r), 'V': V}
        e['saved_bad_point'] = True
    out['results'].append(e)
    if bad is not None:
        break
out['any_bad_point'] = bad is not None
out['bad_point'] = bad
out['note'] = ('a bad point is a point of the RELAXATION (necessary conditions only), not yet a '
               'cover; realizability and exact rational checking are separate')
(OUT / 'socp_outer_attack.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
print(json.dumps({k: v for k, v in out.items() if k not in ('results', 'bad_point')}, indent=1))
for e in out['results']:
    print(e['name'], 'legal', e['legal'], 'V-R*', round(e['V_minus_R_star'], 8),
          'minres', round(e.get('min_over_51_cone_residual', float('nan')), 9),
          'bad' if e.get('below_R_minus_1e6') else '')
