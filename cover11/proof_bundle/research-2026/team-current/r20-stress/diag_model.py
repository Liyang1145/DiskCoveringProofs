"""R20-stress diagnostic: pin the saved q0(6,7) candidate's active constraints / equality
structure, and calibrate the sector-cap loss decomposition.

READ-ONLY reuse of lead model code (exec of file prefixes, exactly as lead/nonlinear_stress_probe.py
does). This script writes ONLY inside research-2026/team-current/r20-stress/.

Objects:
  a0 : 42 angles (33 site-face angles + 9 switch half-angles) of the saved candidate
  shape(a) -> (R_shape, 21 residuals, detail) ; detail has logg (root gauge), alpha, w, rat, ...
Legal (positive) angle domain D_legal:
  13 linear equalities (11 triangle sums + 2 hub sums)
  2 sine-cycle equations + 6 circle-ratio equations  (8 nonlinear, angle-only)
  positivity: site/switch angles in (0,pi) resp (0,pi/2), alpha_i in (0,pi), w_i in (0,pi).
All radii are normalized so that max_f gamma_f = 1 (scale elimination C836).
"""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np

W = Path(__file__).parent                      # r20-stress
LEAD = W.parent / 'lead'
OUT = W / 'out'

# ---- reuse lead model construction (prefixes only; no lead file is written) -------------
zz = {'__file__': str(LEAD / 'check_angle_only.py')}
exec((LEAD / 'check_angle_only.py').read_text(encoding='utf-8').split("a=ns['x0'][:42]")[0], zz)
ns, shape = zz['ns'], zz['shape']
a0 = ns['x0'][:42]

R, con, det = shape(a0)
logg = det['logg']                     # root gauge gamma_0 = 1
g = np.exp(logg)
M = g.max()
u = g / M                              # normalized local radii  (20,)
sw = np.arange(11, 20)                 # switch factors
active = np.where(u > 1 - 1e-7)[0]
slack = np.where(u <= 1 - 1e-7)[0]

alpha = det['alpha']                   # sector centre angles (9,)
w = det['w']                           # boundary arc widths (9,), sum = 2*pi
b = a0[33:42]                          # switch half-angles (9,)

# sector chord ell_i = sqrt(u_{i-1}^2 + u_i^2 - 2 u_{i-1} u_i cos alpha_i) with u = normalized switches
usw = u[sw]                            # usw[i] = normalized radius of switch factor i
ell = np.array([math.sqrt(usw[(i - 1) % 9] ** 2 + usw[i] ** 2
                          - 2 * usw[(i - 1) % 9] * usw[i] * math.cos(alpha[i])) for i in range(9)])
q = 2 * np.sin(w / 2)                  # chord of the unit boundary circle
Ri = q / ell                           # sector radius ratios, all equal on legal shapes
Lam0 = np.maximum(1.0, 2 * np.sin(alpha / 2))
D0 = q / Lam0
s0 = D0 / R                            # capacity ratio  (D = R * s)

# sine-law one-step caps for switch radii:  gamma_sw,i sin(2 b_i) = gamma_f sin(A_i)
c = ns['C'] if 'C' in ns else None
faces = ns['faces']
caps = np.zeros(9)
edge_face_angle = np.zeros(9)
for i in range(9):
    e = tuple(sorted((i, (i + 1) % 9)))
    for t, f in enumerate(faces):
        if e[0] in f and e[1] in f:
            k = f.index(next(v for v in f if v not in e))
            edge_face_angle[i] = a0[3 * t + k]      # angle opposite the boundary edge
            break
    caps[i] = min(1.0, math.sin(edge_face_angle[i]) / math.sin(2 * b[i]))
Lam1 = np.array([max(caps[(i - 1) % 9], caps[i],
                     math.sqrt(caps[(i - 1) % 9] ** 2 + caps[i] ** 2
                               - 2 * caps[(i - 1) % 9] * caps[i] * math.cos(alpha[i]))) for i in range(9)])
D1 = q / Lam1

# ---- tangent space of the legal angle domain at the candidate ---------------------------
eq = ns['eq'][:, :42]
Nr = np.linalg.svd(eq)[2][13:].T                      # 42 x 29 right nullspace of the 13 linear rows
assert Nr.shape == (42, 29)
h = 1e-6
def con8(a):
    return shape(a)[1][13:21]
J8 = np.column_stack([(con8(a0 + Nr @ (np.eye(29)[k] * h)) - con8(a0 - Nr @ (np.eye(29)[k] * h))) / (2 * h)
                      for k in range(29)])
T = np.linalg.svd(J8)[2][8:].T                        # 29 x 21 tangent of the 8 nonlinear equations
assert T.shape == (29, 21)

def Dvec(a):
    """D_i^0 and D_i^1 at angle vector a (42,)."""
    r, cc, d = shape(a)
    al, ww = d['alpha'], d['w']
    gg, _cy, _, _ = zz['radii'](a)
    MM = np.exp(gg).max()
    uu = np.exp(gg)[11:20] / MM
    qq = 2 * np.sin(ww / 2)
    el = np.array([math.sqrt(uu[(i - 1) % 9] ** 2 + uu[i] ** 2
                             - 2 * uu[(i - 1) % 9] * uu[i] * math.cos(al[i])) for i in range(9)])
    L0 = np.maximum(1.0, 2 * np.sin(al / 2))
    cc2 = np.zeros(9)
    for i in range(9):
        ee = tuple(sorted((i, (i + 1) % 9)))
        for t, f in enumerate(faces):
            if ee[0] in f and ee[1] in f:
                k = f.index(next(v for v in f if v not in ee))
                cc2[i] = min(1.0, math.sin(a[3 * t + k]) / math.sin(2 * a[33 + i]))
                break
    L1 = np.array([max(cc2[(i - 1) % 9], cc2[i],
                       math.sqrt(cc2[(i - 1) % 9] ** 2 + cc2[i] ** 2
                                 - 2 * cc2[(i - 1) % 9] * cc2[i] * math.cos(al[i]))) for i in range(9)])
    return qq / L0, qq / L1, el, uu, al, ww

# directional derivative of log D_i along tangent directions
def dlogD(a, v, eps):
    Dp = Dvec(a + eps * v)[1]
    Dm = Dvec(a - eps * v)[1]
    return (np.log(Dp) - np.log(Dm)) / (2 * eps)

dirs = []
for k in range(21):
    v = Nr @ T[:, k]
    v = v / np.linalg.norm(v)
    sp = []
    for eps in (1e-4, 5e-5):
        try:
            sp.append(dlogD(a0, v, eps))
        except (ValueError, OverflowError):
            sp.append(np.full(9, np.nan))
    dirs.append(np.nanmean(np.array(sp), axis=0))

G = np.array(dirs)                                        # 21 x 9 : d log D_i along tangent basis
G = G / np.linalg.norm(G, axis=1, keepdims=True)          # normalise rows (basis is not orthonormal)

# first-order feasibility of "all D_i decrease": LP  min t  s.t.  G v <= t,  -1 <= v <= 1
from scipy.optimize import linprog
Aub = np.c_[G.T, -np.ones(9)]                             # (G^T v)_i - t <= 0
res = linprog(c=np.r_[np.zeros(21), 1.0], A_ub=Aub, b_ub=np.zeros(9),
              bounds=[(-1, 1)] * 21 + [(None, None)], method='highs')
v_all = res.x[:21]
v_all = v_all / np.linalg.norm(v_all) if np.linalg.norm(v_all) > 0 else v_all
t_star = float(res.x[21])
der_all = G.T @ v_all

out = {
  'scope': 'candidate calibration + first-order tangency test for the sector-cap loss decomposition; numeric only',
  'candidate_radius_R': float(R),
  'max_residual_21': float(abs(con).max()),
  'sector_radius_ratios_Ri': Ri.tolist(),
  'max_rel_spread_Ri': float(abs(Ri / R - 1).max()),
  'normalized_radii_u': u.tolist(),
  'active_factors': active.tolist(),
  'active_switch_count': int(sum(1 for f in active if f >= 11)),
  'slack_factors': [{'factor': int(f), 'u': float(u[f]),
                     'kind': 'switch' if f >= 11 else 'site-face'} for f in slack],
  'alpha_deg': (alpha * 180 / math.pi).tolist(),
  'w_deg': (w * 180 / math.pi).tolist(),
  'b_deg': (b * 180 / math.pi).tolist(),
  'ell': ell.tolist(),
  'q': q.tolist(),
  'Lambda0': Lam0.tolist(),
  'D0': D0.tolist(),
  'capacity_ratio_s0': s0.tolist(),
  'max_abs_s0_minus_1': float(abs(s0 - 1).max()),
  'switch_caps_Gamma': caps.tolist(),
  'Lambda1': Lam1.tolist(),
  'D1': D1.tolist(),
  'D1_minus_R': (D1 - float(R)).tolist(),
  'tangent_dim': int(T.shape[1]),
  'LP_first_order_all_decrease': {'t_star': t_star, 'success': bool(res.success),
                                  'derivatives_along_best_direction': der_all.tolist()},
  'tangent_basis_dlogD': G.tolist(),
}
(OUT / 'diag_model.json').write_text(json.dumps(out, indent=2))

print('R =', R, ' max|residual| =', abs(con).max())
print('Ri/R - 1 max    =', abs(Ri / R - 1).max())
print('active          =', active.tolist(), ' switches active:', sum(1 for f in active if f >= 11))
print('slack           =', [(int(f), round(float(u[f]), 8), 'sw' if f >= 11 else 'face') for f in slack])
print('alpha (deg)     =', np.round(alpha * 180 / math.pi, 3).tolist())
print('w (deg)         =', np.round(w * 180 / math.pi, 3).tolist())
print('b (deg)         =', np.round(b * 180 / math.pi, 3).tolist())
print('s0 = D0/R       =', np.round(s0, 12).tolist(), ' max|s0-1| =', abs(s0 - 1).max())
print('caps Gamma      =', np.round(caps, 8).tolist())
print('D1 - R          =', np.round(D1 - float(R), 12).tolist())
print('LP t*           =', t_star, 'success', res.success)
print('derivatives     =', np.round(der_all, 8).tolist())
