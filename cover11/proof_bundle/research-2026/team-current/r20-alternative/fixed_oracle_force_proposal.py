"""fixed_oracle_force_proposal.py  (r20-alternative; sole write, no child)

Task (lead): a force-PROPOSAL generator for the fixed-angle SOCP (no angle optimisation).
Interface:  input = 9 widths (sum = 2*pi, each <= L = 2*arcsin(0.38));  output = sites, aux, r,
and the 51 force vectors in CANONICAL order (18 endpoints then 33 face cones, faces in the
canonical C911 order below);  proposal_norm = SUM OF EUCLIDEAN NORMS of the 51 vectors.

Method: solve the fixed-angle primal (<= 400 SLSQP iterations), then recover non-negative
weights by NNLS on  [44 free-coordinate balance rows; 1 normalisation row] x 51 edge gradients
(A alpha ~ (0,..,0,1), alpha >= 0), and form p_e = alpha_e * unit(C - U) resp. alpha_e * unit(C - Z).
The primal's own multipliers are reported side by side, plus the direct free-node balance of p.

NOTHING here is certified: this is a numeric proposal for the lead's independent forest-balance
check.  Importing the module must not run any optimisation (main guard at the bottom).
"""
import json
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import minimize, nnls

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
R_STAR = float(F(3799838531198387090485182, 10**25))
L_CAP = 2 * np.arcsin(0.38)

# canonical C911 labelling, written literally (no q0_graphs magic index):
# rings 0..8 in saved order; label 9 = hub B (saved raw centre 2); label 10 = hub A (raw 0).
RING_RAW = [5, 7, 1, 8, 6, 4, 9, 10, 3]
HUB_LABEL_RAW = {9: 2, 10: 0}
FACE_LIST_TEXT = """9 0 1
9 1 2
9 2 3
9 3 4
10 4 5
10 5 6
10 6 7
10 7 8
10 8 0
9 10 0
9 10 4"""
FACES = [[int(t) for t in line.split()] for line in FACE_LIST_TEXT.strip().splitlines()]
assert len(FACES) == 11 and all(len(f) == 3 for f in FACES)

FORCE_ORDER = []
for i in range(9):
    FORCE_ORDER.append(('endpoint', i, i))          # ring i -> switch U_i
    FORCE_ORDER.append(('endpoint', i, (i - 1) % 9))  # ring i -> switch U_{i-1}
for fi, face in enumerate(FACES):
    for s in face:
        FORCE_ORDER.append(('face', s, fi))
assert len(FORCE_ORDER) == 51


def load_centres():
    raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
    Pf = np.array([[float(F(int(v[0]), 10**17)), float(F(int(v[1]), 10**17))]
                   for v in raw['centers_scaled_1e17']])
    return np.array([Pf[r] for r in RING_RAW] + [Pf[HUB_LABEL_RAW[9]], Pf[HUB_LABEL_RAW[10]]])


def switches_from_centres(C):
    S = []
    for i in range(9):
        a_, b_ = C[i], C[(i + 1) % 9]
        m_ = (a_ + b_) / 2
        d_ = np.linalg.norm(b_ - a_)
        n_ = np.array([-(b_[1] - a_[1]) / d_, (b_[0] - a_[0]) / d_])
        mn = float(m_ @ n_)
        disc = np.sqrt(mn * mn + 1 - float(m_ @ m_))
        cand = [m_ + (-mn + disc) * n_, m_ + (-mn - disc) * n_]
        cand.sort(key=lambda P: max(np.linalg.norm(P - a_), np.linalg.norm(P - b_)))
        S.append(cand[0])
    return np.array(S)


def angles_from_widths(w):
    th = np.concatenate([[0.0], np.cumsum(w)])
    return th[:9]


def solve_fixed(w, maxiter=400):
    """fixed-angle primal: variables (c 22, z 22, r); switches fixed by the widths"""
    th = angles_from_widths(w)
    U = np.stack([np.cos(th), np.sin(th)], axis=1)
    NV = 45

    def unpack(x):
        return x[:22].reshape(11, 2), x[22:44].reshape(11, 2), x[44]
    cons = []

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
        cons.append(mk_end(i, i))
        cons.append(mk_end(i, (i - 1) % 9))
    for fi, face in enumerate(FACES):
        for s in face:
            cons.append(mk_face(fi, s))
    x0 = np.zeros(NV)
    sites = np.zeros((11, 2))
    for i in range(9):
        mid = (U[i] + U[(i - 1) % 9]) / 2
        sites[i] = mid * (0.97 if np.linalg.norm(mid) > 0 else 1.0)
    sites[9] = sites[:9].mean(axis=0) * 0.5
    sites[10] = sites[:9].mean(axis=0) * 0.35
    x0[:22] = sites.reshape(-1)
    for fi, face in enumerate(FACES):
        P = sites[face]
        M = np.stack([2 * (P[1] - P[0]), 2 * (P[2] - P[0])], axis=0)
        b = np.array([P[1] @ P[1] - P[0] @ P[0], P[2] @ P[2] - P[0] @ P[0]])
        try:
            x0[22 + 2 * fi:24 + 2 * fi] = np.linalg.solve(M, b)
        except np.linalg.LinAlgError:
            x0[22 + 2 * fi:24 + 2 * fi] = P.mean(axis=0)
    x0[44] = 0.40
    res = minimize(lambda x: x[44], x0, jac=lambda x: np.r_[np.zeros(44), 1.0], method='SLSQP',
                   bounds=[(None, None)] * 44 + [(0.05, 0.6)], constraints=cons,
                   options={'maxiter': maxiter, 'ftol': 1e-13})
    c, z, r = unpack(res.x)
    mv = getattr(res, 'multipliers', None)
    lam = np.atleast_1d(mv)[-len(cons):] if mv is not None else None
    eds = np.array([cc['fun'](res.x) for cc in cons])   # ALL 51 edges, in FORCE_ORDER order
    return {'U': U, 'c': c, 'z': z, 'r': float(r), 'success': bool(res.success),
            'edge_residuals': eds,
            'nit': int(res.nit), 'lam_51': (None if lam is None else np.array(lam[-51:], dtype=float)),
            'min_residual_all51': float(min(cc['fun'](res.x) for cc in cons))}


def unit(v):
    n = np.linalg.norm(v)
    return v / n if n > 0 else np.zeros_like(v)


def propose_forces(sol, mask_tol=1e-7):
    """NNLS on the ACTIVE (tight) edges only; G rows use unit(d) with the SIGNED incidence;
    the r-stationarity is enforced by the normalisation row sum(alpha) = 1.
    primal forces use p = 2*lambda*d (squared-constraint convention)."""
    c, z, U = sol['c'], sol['z'], sol['U']
    r = sol['r']
    res51 = sol['edge_residuals']
    active = [k for k in range(51) if res51[k] <= mask_tol]
    G = np.zeros((45, 51))
    for k in active:
        kind, site, other = FORCE_ORDER[k]
        g = np.zeros(45)
        d = (c[site] - U[other]) if kind == 'endpoint' else (c[site] - z[other])
        u = unit(d)
        g[2 * site:2 * site + 2] += u
        if kind == 'face':
            g[22 + 2 * other:24 + 2 * other] -= u
        g[44] = 1.0
        G[:, k] = g
    b = np.zeros(45)
    b[44] = 1.0
    alpha = np.zeros(51)
    if active:
        a_act, resid = nnls(G[:, active], b, maxiter=5000)
        for pos, k in enumerate(active):
            alpha[k] = a_act[pos]
        nnls_resid = float(np.linalg.norm(G[:, active] @ a_act - b))
    else:
        nnls_resid = float(np.linalg.norm(b))
    p = np.zeros((51, 2))
    for k in range(51):
        kind, site, other = FORCE_ORDER[k]
        d = (c[site] - U[other]) if kind == 'endpoint' else (c[site] - z[other])
        p[k] = alpha[k] * unit(d)
    bal = np.zeros((22, 2))
    for k in range(51):
        kind, site, other = FORCE_ORDER[k]
        if kind == 'endpoint':
            bal[site] += p[k]
        else:
            bal[site] += p[k]
            bal[11 + other] -= p[k]
    # matrix-side balance (from G, unit rows) must equal the direct scatter
    mat_bal = np.zeros(45)
    for k in active:
        mat_bal += alpha[k] * G[:, k]
    mat_max = float(np.max(np.abs(mat_bal[:44])))
    # proposal work: anchor loads from the PROPOSAL forces p (not from primal_p)
    load_p = np.zeros((9, 2))
    for k in range(51):
        kind, site, other = FORCE_ORDER[k]
        if kind == 'endpoint':
            load_p[other] -= p[k]
    proposal_work = float(sum(load_p[i] @ U[i] for i in range(9)))
    lam = sol['lam_51']
    primal_p = None
    work = None
    if lam is not None:
        primal_p = np.zeros((51, 2))
        for k in range(51):
            kind, site, other = FORCE_ORDER[k]
            d = (c[site] - U[other]) if kind == 'endpoint' else (c[site] - z[other])
            primal_p[k] = 2 * lam[k] * d                    # squared-constraint convention
        # anchor load: only endpoint edges carry into the anchors (F = -p at that anchor)
        load = np.zeros((9, 2))
        for k in range(51):
            kind, site, other = FORCE_ORDER[k]
            if kind == 'endpoint':
                load[other] -= primal_p[k]
        work = float(sum(load[i] @ U[i] for i in range(9)))
    return {'n_active_edges': len(active), 'n_masked_edges': 51 - len(active),
            'alpha_51': alpha.tolist(),
            'force_vectors_51': p.tolist(),
            'proposal_norm_sum_euclidean': float(np.sum(np.linalg.norm(p, axis=1))),
            'nnls_residual_norm': nnls_resid,
            'sum_alpha': float(alpha.sum()),
            'matrix_balance_max_abs_44': mat_max,
            'direct_free_balance_max_abs': float(np.max(np.abs(bal))),
            'balance_matrix_vs_scatter_gap': float(np.max(np.abs(mat_bal[:44]
                                                                   - bal.reshape(-1)[:44]))),
            'n_alpha_gt_1e-10': int(np.sum(alpha > 1e-10)),
            'primal_force_norm_sum_euclidean':
                (None if primal_p is None else float(np.sum(np.linalg.norm(primal_p, axis=1)))),
            'proposal_work_sum_anchor_load_dot_U': proposal_work,
            'primal_work_sum_anchor_load_dot_U': work,
            'primal_r': r, 'work_minus_primal_r': (None if work is None else work - r)}


def propose_from_widths(w, maxiter=400):
    if abs(float(np.sum(w)) - 2 * np.pi) > 1e-9 or float(np.max(w)) > L_CAP + 1e-9:
        raise ValueError('illegal widths (need sum 2*pi and each <= L_cap)')
    sol = solve_fixed(w, maxiter=maxiter)
    out = {'widths': [float(v) for v in w], 'r': sol['r'], 'r_minus_R_star': sol['r'] - R_STAR,
           'success': sol['success'], 'nit': sol['nit'],
           'min_residual_all51': sol['min_residual_all51'],
           'sites': sol['c'].tolist(), 'aux': sol['z'].tolist(),
           'force_order': [[k, int(s), int(o)] for (k, s, o) in FORCE_ORDER]}
    out.update(propose_forces(sol))
    out['LABEL'] = ('numeric force PROPOSAL for the lead forest-balance check; NOT certified; '
                    'proposal_norm = sum of Euclidean norms')
    return out


def corners_report(path=None):
    C = load_centres()
    m_small = 2 * np.pi - 8 * L_CAP
    out = {'R_STAR_label': 'C529 rational (NOT C891)', 'R_star': R_STAR, 'L_cap': L_CAP,
           'note': 'fixed-angle oracle at the nine capped-simplex vertices; NUMERIC proposal only, '
                   'NOT certified; failures kept explicitly', 'corners': []}
    for k in range(9):
        w = np.full(9, L_CAP)
        w[k] = m_small
        try:
            e = propose_from_widths(w, maxiter=400)
            rec = {'corner': k, 'widths': [float(v) for v in w], 'r': e['r'],
                   'r_minus_R_star': e['r_minus_R_star'], 'r_gt_0p38': bool(e['r'] > 0.38),
                   'success': e['success'], 'nit': e['nit'],
                   'all51_residual_min': e['min_residual_all51'],
                   'proposal_work': e['proposal_work_sum_anchor_load_dot_U'],
                   'nnls_residual_norm': e['nnls_residual_norm'],
                   'n_active_edges': e['n_active_edges'], 'n_masked_edges': e['n_masked_edges'],
                   'alpha_51': e['alpha_51'], 'p_51': e['force_vectors_51'],
                   'sites': e['sites'], 'aux': e['aux']}
        except Exception as exc:                      # noqa: BLE001
            rec = {'corner': k, 'widths': [float(v) for v in w],
                   'error': '%s: %s' % (type(exc).__name__, exc), 'failed': True}
        out['corners'].append(rec)
        print('corner%d r=%.9f r-R*=%s success=%s all51min=%s work=%s'
              % (k, rec.get('r', float('nan')), rec.get('r_minus_R_star'), rec.get('success'),
                 rec.get('all51_residual_min'), rec.get('proposal_work')))
    tgt = Path(path) if path else (OUT / 'corner_force_proposals.json')
    tgt.write_text(json.dumps(out, indent=2), encoding='utf-8')
    print('written', tgt.name, '| n_gt_0p38 =',
          sum(1 for c in out['corners'] if c.get('r_gt_0p38')), '| n_failed =',
          sum(1 for c in out['corners'] if c.get('failed')))
    return out


if __name__ == '__main__':
    import sys
    if '--corners' in sys.argv:
        corners_report()
        raise SystemExit(0)
    C = load_centres()
    sw = switches_from_centres(C)
    th = np.array([np.arctan2(p[1], p[0]) for p in sw])
    # CYCLIC widths: w_i = (theta_{i+1} - theta_i) mod 2*pi  (sum = 2*pi by construction)
    th_c = np.concatenate([th, [th[0] + 2 * np.pi]])
    wcand = np.mod(np.diff(th_c), 2 * np.pi)
    m_small = 2 * np.pi - 8 * L_CAP
    vert0 = np.full(9, L_CAP)
    vert0[0] = m_small
    points = [('candidate', wcand), ('uniform', np.full(9, 2 * np.pi / 9)), ('vertex0', vert0)]
    rep = {'R_STAR_label': 'C529 rational (NOT C891)', 'R_star': R_STAR, 'L_cap': L_CAP,
           'note': 'three calibration points only; NUMERIC; nothing certified; main-guard module',
           'points': []}
    for name, w in points:
        try:
            e = propose_from_widths(w)
            e['name'] = name
        except Exception as exc:                       # noqa: BLE001
            e = {'name': name, 'error': '%s: %s' % (type(exc).__name__, exc)}
        rep['points'].append(e)
        print(name, {k: e.get(k) for k in ('r_minus_R_star', 'proposal_norm_sum_euclidean',
                                           'nnls_residual_norm', 'direct_free_balance_max_abs',
                                           'n_alpha_gt_1e-10', 'primal_lambda_norm_sum_euclidean')})
    (OUT / 'fixed_oracle_force_proposal.json').write_text(json.dumps(rep, indent=2), encoding='utf-8')
    print('written fixed_oracle_force_proposal.json')
