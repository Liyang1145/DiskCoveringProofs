"""socp_anchor_lift_v2.py  (r20-alternative; sole write, no child)

CORRECTED lift system (lead source review):
  * site balance MUST include the face-edge forces too: every face cone contributes
    +alpha*(C[site]-Z[face])/|.| to the site and the opposite to the aux  (v1 omitted ALL face
    forces at the sites -> its "no strictly positive solution" reading is an ARTIFACT, retracted);
  * 51-slot mapping: unknown tuple -> the EXPORT incidence tuple (slack cones of faces 5,7 sit in
    their true slots), not "compress 45 then append zeros";
  * a DIRECT scatter-force calibration (independent loop structure) checks A @ alpha against the
    node-wise force summation;
  * the LP's floating-zero t* does NOT prove strict infeasibility -> only reported.

Exports U, C, Z, incidence (51) and both 51-vectors (LS, LP) for the chain.
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
graph = json.loads((ROOT / 'research-2026/team-current/lead/q0_graphs.json').read_text())[2]
FACES = [list(f) for f in graph['faces']]
ex = json.loads((OUT / 'socp_anchor_export.json').read_text(encoding='utf-8'))
U = np.array(ex['U'])
C = np.array(ex['C_sites'])
Z = np.array(ex['Z_aux'])
SLACK = [5, 7]

unit = lambda v: v / np.linalg.norm(v)

# ---- 51 incidence (export order = endpoint slots then face cones, as in socp_anchor_export) --
inc51 = []
for i in range(9):
    inc51.append(('endpoint', i, i))                 # ring i endpoint U_i
    inc51.append(('endpoint', i, (i - 1) % 9))       # ring i endpoint U_{i-1}
for fi, face in enumerate(FACES):
    for s in face:
        inc51.append(('face', s, fi))
assert len(inc51) == 51

free = [k for k, (kind, s, t) in enumerate(inc51)
        if not (kind == 'face' and t in SLACK)]
assert len(free) == 45
pos_of = {k: p for p, k in enumerate(free)}

rows, rhs, tags = [], [], []


def add(row, b, tag):
    rows.append(row)
    rhs.append(b)
    tags.append(tag)


# node balances: sites (endpoint forces AND face forces) and aux
for k in range(11):
    for comp in range(2):
        row = np.zeros(45)
        for s51, (kind, site, other) in enumerate(inc51):
            if s51 not in pos_of:
                continue
            p = pos_of[s51]
            if kind == 'endpoint' and site == k:
                row[p] += unit(C[k] - U[other])[comp]
            elif kind == 'face' and site == k:
                row[p] += unit(C[k] - Z[other])[comp]
        add(row, 0.0, 'site%d_%d' % (k, comp))
for fi in range(11):
    for comp in range(2):
        row = np.zeros(45)
        for s51, (kind, site, other) in enumerate(inc51):
            if s51 not in pos_of or kind != 'face' or other != fi:
                continue
            row[pos_of[s51]] -= unit(C[site] - Z[fi])[comp]
        add(row, 0.0, 'aux%d_%d' % (fi, comp))
# anchor tangential loads = 0
for i in range(9):
    perp = np.array([-U[i, 1], U[i, 0]])
    row = np.zeros(45)
    for (ring, anchor) in ((i, i), ((i + 1) % 9, i)):
        s51 = 2 * ring + (0 if anchor == ring else 1)
        if s51 in pos_of:
            row[pos_of[s51]] += float(unit(U[i] - C[ring]) @ perp)
    add(row, 0.0, 'tangential%d' % i)
add(np.ones(45), 1.0, 'sum_alpha')
A, b = np.array(rows), np.array(rhs)
sol_ls, _, rank, _ = np.linalg.lstsq(A, b, rcond=None)
res = A @ sol_ls - b
alpha51_ls = np.zeros(51)
for s51 in free:
    alpha51_ls[s51] = sol_ls[pos_of[s51]]
# direct scatter calibration (independent loop)
def scatter_balance(a51):
    bal = np.zeros((22, 2))
    for s51, (kind, site, other) in enumerate(inc51):
        al = a51[s51]
        if al == 0.0:
            continue
        if kind == 'endpoint':
            bal[site] += al * unit(C[site] - U[other])
        else:
            f = al * unit(C[site] - Z[other])
            bal[site] += f
            bal[11 + other] -= f
    return bal


cal = scatter_balance(alpha51_ls)
cal_max = float(np.max(np.abs(cal)))
# LP max-min
Aeq = np.c_[A, np.zeros((A.shape[0], 1))]
c = np.r_[np.zeros(45), -1.0]
Aub = np.c_[-np.eye(45), np.ones(45)]
lp = linprog(c, A_ub=Aub, b_ub=np.zeros(45), A_eq=Aeq, b_eq=b,
             bounds=[(None, None)] * 46, method='highs')
alpha51_lp = None
if lp.success:
    alpha51_lp = np.zeros(51)
    for s51 in free:
        alpha51_lp[s51] = lp.x[pos_of[s51]]
rep = {'scope': 'numeric corrected linear lift; LS + max-min LP; floating-zero t* is NOT a proof '
                'of strict infeasibility',
       'rank_A': int(rank), 'n_eq': int(A.shape[0]), 'n_unknowns': 45,
       'least_squares_residual_norm': float(np.linalg.norm(res)),
       'least_squares_max_abs_residual': float(np.max(np.abs(res))),
       'direct_scatter_max_abs_node_force': cal_max,
       'calibration_agrees': bool(cal_max < 1e-12),
       'alpha51_ls': [float(v) for v in alpha51_ls],
       'alpha_ls_min': float(np.min(alpha51_ls[np.array(free)])),
       'n_alpha_ls_lt_1e-9': int(np.sum(alpha51_ls[np.array(free)] < 1e-9)),
       'lp_success': bool(lp.success), 'lp_t_star': float(lp.x[45]) if lp.success else None,
       'worst_residual_tags': [t for _, t in sorted(zip(np.abs(res), tags), reverse=True)[:5]],
       'incidence_51': [[k, int(s), int(t)] for (k, s, t) in inc51],
       'slack_slots': [k for k, (kind, s, t) in enumerate(inc51) if kind == 'face' and t in SLACK],
       'U': U.tolist(), 'C': C.tolist(), 'Z': Z.tolist(),
       'label_cross_map': {str(i): int(RAW_OF_LABEL[i]) for i in range(11)}}
if alpha51_lp is not None:
    rep['alpha51_lp'] = [float(v) for v in alpha51_lp]
    rep['alpha_lp_min'] = float(np.min(alpha51_lp[np.array(free)]))
    rep['lp_residual_norm'] = float(np.linalg.norm(A @ lp.x[:45] - b))
    rep['direct_scatter_max_abs_node_force_lp'] = float(np.max(np.abs(scatter_balance(alpha51_lp))))
(OUT / 'socp_anchor_lift_v2.json').write_text(json.dumps(rep, indent=2), encoding='utf-8')
print('rank', rank, 'residual', rep['least_squares_residual_norm'],
      'scatter calib', rep['direct_scatter_max_abs_node_force'], rep['calibration_agrees'])
print('alpha LS: min', rep['alpha_ls_min'], 'n<1e-9', rep['n_alpha_ls_lt_1e-9'])
print('LP success', rep['lp_success'], 't*', rep['lp_t_star'],
      'min alpha', rep.get('alpha_lp_min'), 'resid', rep.get('lp_residual_norm'),
      'scatter', rep.get('direct_scatter_max_abs_node_force_lp'))
print('slack slots in 51:', rep['slack_slots'], ' worst:', rep['worst_residual_tags'])
