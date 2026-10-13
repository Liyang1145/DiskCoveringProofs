"""candidate_sharp_check.py  (r20-alternative; sole write, no child; final small task)

(1) read the actual joint_outer_attack.json and print all 12 seed rows (report discrepancy check);
(2) on the SAVED candidate geometry (centres rotated to the anchor angles, z_f = face circumcentres)
    set r = R_STAR and compute ALL 51 residuals directly: expect ~0 (active) for 18 endpoints and
    the 27 tight face cones, and positive slack (~8.8e-4) for the 6 cones of the two slack faces;
(3) relabel the calibration entry: the ~0.0156 residuals there came from x0 with r = 0.4, i.e. a
    strictly feasible seed check, NOT a sharp candidate calibration.
No optimisation, no scaling.
"""
import json
from fractions import Fraction as F
from pathlib import Path
import numpy as np

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

# ---- (1) the 12 seed rows -----------------------------------------------------------
run = json.loads((OUT / 'joint_outer_attack.json').read_text(encoding='utf-8'))
print('seeds recorded:', len(run['seeds']), ' n_target_hits:', run.get('n_target_hits'),
      ' n_diverged:', run.get('n_diverged'))
for e in run['seeds']:
    print('  %-16s V-R*=%.3e nit=%3d min51=%.1e legal=%s diverged=%s'
          % (e['seed'], e['V_minus_R_star'], e['nit'], e['min_51_edge_residual'],
             e['widths_legal'], e['diverged_or_infeasible']))

# ---- (2) r = R_STAR residuals on the saved candidate geometry ------------------------
sw = []
for i in range(9):
    a_, b_ = C0[i], C0[(i + 1) % 9]
    m_ = (a_ + b_) / 2
    d_ = np.linalg.norm(b_ - a_)
    n_ = np.array([-(b_[1] - a_[1]) / d_, (b_[0] - a_[0]) / d_])
    mn = float(m_ @ n_)
    disc = np.sqrt(mn * mn + 1 - float(m_ @ m_))
    cand = [m_ + (-mn + disc) * n_, m_ + (-mn - disc) * n_]
    cand.sort(key=lambda P: max(np.linalg.norm(P - a_), np.linalg.norm(P - b_)))
    sw.append(cand[0])
sw = np.array(sw)
phi0 = float(np.arctan2(sw[0][1], sw[0][0]))
Rm = np.array([[np.cos(-phi0), -np.sin(-phi0)], [np.sin(-phi0), np.cos(-phi0)]])
sites = (Rm @ C0.T).T
U = np.stack([np.cos(np.array([np.arctan2(s[1], s[0]) for s in sw]) - phi0),
              np.sin(np.array([np.arctan2(s[1], s[0]) for s in sw]) - phi0)], axis=1)
r = np.array(R_STAR)
res = {'R_STAR_label': 'C529 rational (NOT C891)', 'R_star': R_STAR,
       'note': 'r set exactly to R_STAR on the SAVED candidate geometry; direct 51 residuals; '
               'no optimisation'}
end_res = []
for i in range(9):
    end_res.append(r * r - float(np.sum((sites[i] - U[i])**2)))
    end_res.append(r * r - float(np.sum((sites[i] - U[(i - 1) % 9])**2)))
face_res = {}
tight, slack = [], []
for fi, face in enumerate(FACES):
    P = sites[face]
    M = np.stack([2 * (P[1] - P[0]), 2 * (P[2] - P[0])], axis=0)
    b = np.array([P[1] @ P[1] - P[0] @ P[0], P[2] @ P[2] - P[0] @ P[0]])
    z = np.linalg.solve(M, b)
    Rc = float(np.linalg.norm(sites[face[0]] - z))
    vals = [float(r * r - np.sum((sites[s] - z)**2)) for s in face]
    face_res[fi] = {'residuals': vals, 'Rc': Rc, 'Rc_minus_r': Rc - R_STAR,
                    'min_residual': min(vals)}
    (slack if min(vals) > 1e-8 else tight).append(fi)
res['endpoint_residuals_18'] = end_res
res['face_residuals_33'] = face_res
res['summary'] = {'endpoint_max_abs': float(np.max(np.abs(end_res))),
                  'tight_face_indices': tight, 'slack_face_indices': slack,
                  'slack_face_min_residuals': {str(f): face_res[f]['min_residual'] for f in slack},
                  'n_positive_slack_cones': int(sum(3 for f in slack))}
(OUT / 'candidate_sharp_check.json').write_text(json.dumps(res, indent=2), encoding='utf-8')
print('\nr = R_STAR on saved candidate: endpoint max |residual| = %.3e'
      % res['summary']['endpoint_max_abs'])
print('tight faces:', tight, ' slack faces:', slack)
for f in slack:
    print('  slack face %d: min residual %.6e  (Rc - r = %.6e)'
          % (f, face_res[f]['min_residual'], face_res[f]['Rc_minus_r']))

# ---- (3) relabel the calibration entry ----------------------------------------------
cal_p = OUT / 'joint_outer_calibration.json'
cal = json.loads(cal_p.read_text(encoding='utf-8'))
cal['direct_51_distances_at_saved_candidate']['LABEL'] = (
    'r = 0.4 at the warm start: this is a STRICTLY FEASIBLE SEED check, NOT the sharp candidate '
    'calibration; the sharp check (r = R_STAR) is in candidate_sharp_check.json')
cal['calibration_run']['LABEL'] = 'sharp check: SLSQP from the rotated warm start converges to V = R*'
cal_p.write_text(json.dumps(cal, indent=2), encoding='utf-8')
print('\nrelabelled joint_outer_calibration.json')
