"""socp_anchor_balance_lift.py  (r20-alternative; sole write, no child)

Lead obligation: solve for POSITIVE multiplier weights that satisfy the physical lift system on
the SAME (U, C, Z) as the SOCP optimum:

  unknowns: alpha_e >= 0 for the 45 ACTIVE distance edges (18 endpoints + 27 face cones);
            the 6 cone constraints of the two slack faces are FORCED to 0 (not unknowns);
  equations: 22 node balances (11 sites c, 11 aux z) x 2 = 44 rows,
             9 anchor tangential-load rows (corrected edge incidence),
             1 normalisation  sum_e alpha_e = 1;
  -> linear overdetermined system (54 equations / 45 unknowns): least squares, plus an
     LP that maximises min alpha (scipy linprog), both purely numeric.

Labelling note (lead's check): faces are taken verbatim from lead/q0_graphs.json[2].faces.
Label 9 = the degree-6 hub = saved centre raw 2 (y ~ +0.273); label 10 = the degree-7 hub =
saved centre raw 0 (y ~ -0.149).  The slack faces [10,5,6] and [10,7,8] therefore carry hub
label 10 = raw 0; cross-map emitted below so the chain can align labels.
"""
import json
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import linprog

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
Pf = np.array([[float(F(int(v[0]), 10**17)), float(F(int(v[1]), 10**17))]
               for v in raw['centers_scaled_1e17']])
NEW2RAW_RINGS = [5, 7, 1, 8, 6, 4, 9, 10, 3]
RAW_OF_LABEL = NEW2RAW_RINGS + [2, 0]
C0 = Pf[RAW_OF_LABEL]
R_STAR = float(F(3799838531198387090485182, 10**25))
graph = json.loads((ROOT / 'research-2026/team-current/lead/q0_graphs.json').read_text())[2]
FACES = [list(f) for f in graph['faces']]
export = json.loads((OUT / 'socp_anchor_export.json').read_text(encoding='utf-8'))
U = np.array(export['U'])
C = np.array(export['C_sites'])
Z = np.array(export['Z_aux'])
r_sol = float(export['r_solution'])
SLACK_FACES = [5, 7]


def switches():
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


U0 = switches()
# ---- unknown ordering: 18 endpoints then the 27 NON-slack face cones -----------------
unknowns = []                                  # (kind, site, anchor/face)
for i in range(9):
    unknowns.append(('endpoint', i, i))
    unknowns.append(('endpoint', i, (i - 1) % 9))
for fi, face in enumerate(FACES):
    if fi in SLACK_FACES:
        continue
    for s in face:
        unknowns.append(('face', s, fi))
NU = len(unknowns)
assert NU == 45, NU
idx = {u: k for k, u in enumerate(unknowns)}
rows, rhs, tags = [], [], []


def add(row, b, tag):
    rows.append(row)
    rhs.append(b)
    tags.append(tag)


# node balance: sites
for k in range(11):
    for comp in range(2):
        row = np.zeros(NU)
        for u, e in idx.items():
            kind, site, other = u
            if kind == 'endpoint' and site == k:
                v = C[k] - U[other]
                nv = np.linalg.norm(v)
                if nv > 0:
                    row[e] += v[comp] / nv
        add(row, 0.0, 'site%d_comp%d' % (k, comp))
# node balance: aux
for fi in range(11):
    for comp in range(2):
        row = np.zeros(NU)
        for u, e in idx.items():
            kind, site, other = u
            if kind == 'face' and other == fi:
                v = C[site] - Z[fi]
                nv = np.linalg.norm(v)
                if nv > 0:
                    row[e] -= v[comp] / nv
        add(row, 0.0, 'aux%d_comp%d' % (fi, comp))
# anchor tangential loads = 0
for i in range(9):
    perp = np.array([-U[i, 1], U[i, 0]])
    row = np.zeros(NU)
    for (ring, anchor) in ((i, i), ((i + 1) % 9, i)):
        u = ('endpoint', ring, anchor)
        if u in idx:
            v = U[i] - C[ring]
            nv = np.linalg.norm(v)
            if nv > 0:
                row[idx[u]] += (v / nv) @ perp
    add(row, 0.0, 'tangential_anchor%d' % i)
# normalisation
row = np.ones(NU)
add(row, 1.0, 'sum_alpha')
A = np.array(rows)
b = np.array(rhs)
sol_ls, res, rank, sv = np.linalg.lstsq(A, b, rcond=None)
resid = A @ sol_ls - b
# LP: maximise t with alpha >= t, A alpha = b
Aeq = np.c_[A, np.zeros((A.shape[0], 1))]
beq = b
c = np.r_[np.zeros(NU), -1.0]
Aub = np.c_[-np.eye(NU), np.ones(NU)]
bub = np.zeros(NU)
bounds = [(None, None)] * NU + [(None, None)]
lp = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=bounds, method='highs')
alpha_ls = sol_ls
alpha_lp = lp.x[:NU] if lp.success else None
full51 = np.zeros(51)
pos = 0
for k, u in enumerate(unknowns):
    full51[pos] = alpha_ls[k]
    pos += 1
slots = []
sl = 0
for fi, face in enumerate(FACES):
    if fi in SLACK_FACES:
        slots.append((fi, face, [45 + sl, 45 + sl + 1, 45 + sl + 2]))
        sl += 3
rep = {'scope': 'numeric linear system (54x45), least squares + max-min LP; no certificate',
       'label_cross_map': {str(i): {'raw_center': int(RAW_OF_LABEL[i]),
                                    'xy': [float(C0[i][0]), float(C0[i][1])]} for i in range(11)},
       'hub_labels': {'label9': 'degree-6 hub, raw 2', 'label10': 'degree-7 hub, raw 0',
                      'slack_faces': [[int(f), FACES[f]] for f in SLACK_FACES]},
       'r_solution': r_sol, 'rank_A': int(rank), 'n_equations': int(A.shape[0]),
       'n_unknowns': NU,
       'least_squares_residual_norm': float(np.linalg.norm(resid)),
       'least_squares_max_abs_residual': float(np.max(np.abs(resid))),
       'residuals_by_tag': {t: float(v) for t, v in zip(tags, resid)},
       'alpha_ls_min': float(np.min(alpha_ls)), 'alpha_ls_positive': bool(np.min(alpha_ls) > 0),
       'n_alpha_ls_lt_1e-10': int(np.sum(alpha_ls < 1e-10)),
       'alpha_ls_45': [float(v) for v in alpha_ls]}
if alpha_lp is not None:
    rep['lp_success'] = bool(lp.success)
    rep['lp_max_min_alpha'] = float(lp.x[NU])
    rep['alpha_lp_min'] = float(np.min(alpha_lp))
    rep['lp_residual_norm'] = float(np.linalg.norm(A @ alpha_lp - b))
    rep['n_alpha_lp_lt_1e-10'] = int(np.sum(alpha_lp < 1e-10))
    rep['alpha_lp_45'] = [float(v) for v in alpha_lp]
(OUT / 'socp_anchor_balance_lift.json').write_text(json.dumps(rep, indent=2), encoding='utf-8')
print('rank', rank, 'eq', A.shape[0], 'unk', NU)
print('LS residual norm', rep['least_squares_residual_norm'], 'max', rep['least_squares_max_abs_residual'])
print('LS min alpha', rep['alpha_ls_min'], 'positive', rep['alpha_ls_positive'],
      'n<1e-10', rep['n_alpha_ls_lt_1e-10'])
if alpha_lp is not None:
    print('LP success', rep['lp_success'], 'max-min alpha', rep.get('lp_max_min_alpha'),
          'min alpha', rep.get('alpha_lp_min'), 'resid', rep.get('lp_residual_norm'))
print('worst residuals:', sorted(rep['residuals_by_tag'].items(), key=lambda kv: -abs(kv[1]))[:6])
print('slack faces:', rep['hub_labels']['slack_faces'], 'labels:',
      {k: v['raw_center'] for k, v in rep['label_cross_map'].items()})
