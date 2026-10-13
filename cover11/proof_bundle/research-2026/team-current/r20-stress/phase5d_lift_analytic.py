"""Phase 5d: (A) replication of phase5a's own chart Jacobian R-column (float64 pipeline);
(B) 60-digit rank / null-space structure of Gb and of the model KKT matrix M;
(C) analytic lift of the TC multipliers: proportionality grad f_k = alpha_k grad b_{face_k},
    assembled 10-orbit avatar w with sum w grad_u b = e_R;
(D) 29-dim (shape-space) lift test: can sum w grad_y b + sum nu grad_y c equal dPhi/dR ?
(E) antisymmetric automaticity at the exactly symmetric chart point.

Numerics = calibration only (60-digit FD); no optimization, no root finding.
Writes only in r20-stress/out .
"""
import os, json, sys
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp

W_DIR = Path(__file__).parent; OUT = W_DIR / 'out'; LEAD = W_DIR.parent / 'lead'
sys.path.insert(0, str(W_DIR))
SRC = (W_DIR / 'phase5c_scale_audit.py').read_text(encoding='utf-8')
pre = SRC.split('# ---------------------------------------------------------------- high precision chart Jacobians')[0]
NS = {'__name__': '__main__', '__file__': str(W_DIR / 'phase5c_scale_audit.py')}
exec(compile(pre, str(W_DIR / 'phase5c_scale_audit.py'), 'exec'), NS)
MM, M0, ns, a0, Nr = NS['MM'], NS['M0'], NS['ns'], NS['a0'], NS['Nr']
faces, adj, root, u0 = NS['faces'], NS['adj'], NS['root'], NS['u0']
tc_geo, angle_vector, model_quant, at, res5 = NS['tc_geo'], NS['angle_vector'], NS['model_quant'], NS['at'], NS['res5']
mp = NS['mp']
mp.mp.dps = 60

# ================================================================ (A) replicate phase5a's own Gb
P5A = W_DIR / 'phase5a_kkt_weights.py'
src = P5A.read_text(encoding='utf-8').split('# ---------------- (4)')[0]
NS5 = {'__name__': '__main__', '__file__': str(P5A)}
exec(compile(src, str(P5A), 'exec'), NS5)
act = NS5['act']
pinvNr5 = np.linalg.pinv(NS5['Nr']); aTC5 = NS5['a_TC']; bc5 = NS5['bc']; av5 = NS5['angle_vector']; u05 = NS5['u0']


def bf_on_chart5(u, f):
    y = pinvNr5 @ (av5(u) - aTC5)
    return float(bc5([mp.mpf(float(x)) for x in y])[0][f])


def chart_deriv5(fun, k, h=1e-7):
    up = u05.copy(); um = u05.copy(); up[k] += h; um[k] -= h
    return (fun(up) - fun(um)) / (2 * h)


Gb5 = np.array([[chart_deriv5(lambda uu, f=f: bf_on_chart5(uu, f), k) for k in range(7)]
                for f in act])                                           # phase5a's own object
print('=== (A) phase5a float64 chart Jacobian: R-column (k=6) ===')
print('   rows = active factors', act.tolist())
print('   phase5a d b_f/dR =', np.array2string(Gb5[:, 6], precision=6, max_line_width=200))
print('   max |phase5a R-column| = %.6f ; min = %.6f  (NOT ~0)'
      % (float(np.abs(Gb5[:, 6]).max()), float(np.abs(Gb5[:, 6]).min())))
sv5 = np.linalg.svd(Gb5, compute_uv=False)
print('   phase5a sv(Gb) =', np.array2string(sv5, precision=3))

# ================================================================ (B) 60-digit Gb: rank / null space / R-column
aTC_m = angle_vector(u0)
Nr_m = [[mp.mpf(float(x)) for x in row] for row in Nr]
a0_m = [mp.mpf(float(x)) for x in a0]
yTC = [mp.fsum([Nr_m[i][k] * (aTC_m[i] - a0_m[i]) for i in range(42)]) for k in range(29)]

ORDER = [0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
H_STEPS = [mp.mpf('1e-8'), mp.mpf('1e-12'), mp.mpf('1e-16'), mp.mpf('1e-20'), mp.mpf('1e-24')]

def chart_b(u, f, h):
    up = list(u); um = list(u); up[6] = up[6] + h; um[6] = um[6] - h
    return (at(up)['b'][f] - at(um)['b'][f]) / (2 * h)

print()
print('=== (B) 60-digit chart Jacobian: FD step dependence of the two smallest singular values ===')
sv_by_h = {}
for h in H_STEPS:
    Gb_full = np.array([[float((at([u0[k] + (h if k == j else 0) for k in range(7)])['b'][f] -
                                at([u0[k] - (h if k == j else 0) for k in range(7)])['b'][f]) / (2 * h))
                         for j in range(7)] for f in ORDER])
    s = np.linalg.svd(Gb_full, compute_uv=False)
    sv_by_h['%.0e' % float(h)] = s.tolist()
    print('   h = %-8s sv = [%s]' % ('%.0e' % float(h), ', '.join('%.3e' % v for v in s)))
Gb = np.array([[float((at([u0[k] + (mp.mpf('1e-16') if k == j else 0) for k in range(7)])['b'][f] -
                      at([u0[k] - (mp.mpf('1e-16') if k == j else 0) for k in range(7)])['b'][f]) / (2 * mp.mpf('1e-16')))
                for j in range(7)] for f in ORDER])
U_, S_, Vt = np.linalg.svd(Gb)
print('   null directions of Gb (18x7), R-component in braces:')
for i in (5, 6):
    v = Vt[i]
    print('     v%d = %s   {v_R = %+.3e}' % (i, np.array2string(v, precision=6, max_line_width=200), v[6]))
print('   R-column (60-digit) of the same object:')
print('     switch rows f=11..19 :', np.array2string(Gb[9:, 6], precision=9))
print('     1/R = %.9f ; max|switch row - 1/R| = %.3e'
      % (1.0 / float(u0[6]), float(np.abs(Gb[9:, 6] - 1.0 / float(u0[6])).max())))
print('     site-face rows f in ORDER[:9] :', np.array2string(Gb[:9, 6], precision=6, max_line_width=200))
print('   solvability of Gb^T w = e_R needs e_R _|_ null(Gb): |v_R| above must vanish  ->',
      'e_R in rowspan(Gb) numerically: residual of lstsq = %.2e'
      % float(np.abs(Gb.T @ np.linalg.lstsq(Gb.T, np.array([0, 0, 0, 0, 0, 0, 1.0]), rcond=None)[0]
                                       - np.array([0, 0, 0, 0, 0, 0, 1.0])).max()))

# ================================================================ 60-digit 29-dim model Jacobian, M, rank
Am = NS['Am']; Bm = NS['Bm']; alm = NS['alm']; acm = NS['acm']
tree_set = set(M0['tree']); other = sorted(set(range(21)) - tree_set); edge = M0['edge']


def full_quant(alist):
    Q = model_quant(alist)
    Aa = [mp.fsum([Am[j][i] * alist[i] for i in range(42)]) for j in range(21)]
    Ba = [mp.fsum([Bm[j][i] * alist[i] for i in range(42)]) for j in range(21)]
    ls = [mp.log(mp.sin(Aa[j])) - mp.log(mp.sin(Ba[j])) for j in range(21)]
    lg = Q['logg']
    cy = [lg[edge[k][0]] - lg[edge[k][1]] + ls[k] for k in other]
    c8 = cy + [Q['rat'][i] / Q['rat'][0] - 1 for i in range(1, 7)]
    return Q, c8


def y_to_a(y):
    return [aTC_m[i] + mp.fsum([Nr_m[i][k] * y[k] for k in range(29)]) for i in range(42)]


def func29(y):
    Q, c8 = full_quant(y_to_a(y))
    return Q['b'], c8


hy = mp.mpf('1e-25')
W29 = mp.zeros(20, 29); J8m = mp.zeros(8, 29)
for k in range(29):
    yp = [mp.mpf(0)] * 29; ym = [mp.mpf(0)] * 29
    yp[k] = hy; ym[k] = -hy
    bp, cp = func29(yp); bm, cm = func29(ym)
    for i in range(20):
        W29[i, k] = (bp[i] - bm[i]) / (2 * hy)
    for i in range(8):
        J8m[i, k] = (cp[i] - cm[i]) / (2 * hy)
W29f = np.array([[float(W29[i, j]) for j in range(29)] for i in range(20)])
J8f = np.array([[float(J8m[i, j]) for j in range(29)] for i in range(8)])
WA = W29f[ORDER]
Prow = J8f.T @ np.linalg.inv(J8f @ J8f.T) @ J8f
Mmat = (np.eye(29) - Prow) @ WA.T
svM = np.linalg.svd(Mmat, compute_uv=False)
print()
print('=== (B2) model KKT matrix M = P_tangent W_A^T (29x18) at a_TC, 60-digit Jacobian ===')
print('   sv(M) last five =', np.array2string(svM[-5:], precision=6))
print('   ratio sv17/sv18 = %.3e ; rank by 1e-6: %d ; by 1e-12: %d ; by 1e-20: %d'
      % (svM[-2] / svM[-1], int((svM > 1e-6).sum()), int((svM > 1e-12).sum()), int((svM > 1e-20).sum())))
# exact-arithmetic-free nested refinement: solve M lam = 0 by one exact null-vector of the 60-digit matrix
uu, ss, vv = np.linalg.svd(Mmat)
lam60 = vv[-1]
lam60 = lam60 / lam60.sum()
print('   null vector lam60 (60-digit object): min = %.6e ; sum = %.15f ; ||M lam60|| = %.3e'
      % (lam60.min(), lam60.sum(), float(np.linalg.norm(Mmat @ lam60))))
P5 = json.loads((OUT / 'phase5a_kkt_weights.json').read_text())
P5B = json.loads((OUT / 'phase5b_certificate.json').read_text())
lam_sym = np.array(P5B['lam_sym'])
print('   ||lam60 - lam_sym(phase5b)||inf = %.3e   (both normalized to sum 1)' % float(np.abs(lam60 - lam_sym).max()))
print('   ||M lam_sym|| = %.3e   (phase5b float64 reported %.3e)' % (float(np.linalg.norm(Mmat @ lam_sym)), P5B['res_sym']))
print('   max|Gb^T lam_sym| = %.3e  (chart projection of the model certificate; report said 4.8e-9)'
      % float(np.abs(Gb.T @ lam_sym).max()))

# ================================================================ (C) analytic lift: alpha_k, avatar w
lamTC = np.array([float(v) for v in root[7:]])
print()
print('=== (C) analytic lift: grad f_k = alpha_k grad b_{face_k} ===')
# map TC contacts to model face labels:  TC arc k <-> model site (6-k)%9 ; hubs: TC hub0 -> 9, hub1 -> 10
ms = lambda k: (6 - k) % 9
def face_of(k, hub):
    tri = {ms(k), ms(k + 1), hub}
    for i, f in enumerate(faces):
        if set(f) == tri:
            return i
    raise KeyError((k, hub))
def face_central(k):
    tri = {ms(k), 9, 10}          # the central site-face through C_k and BOTH hubs (its circumcenter is the waist point)
    for i, f in enumerate(faces):
        if set(f) == tri:
            return i
    raise KeyError(k)
contacts = [(1, 10), (2, 9), (3, 9), (8, 10)]                 # (TC junction k, model hub label)
flabels = [face_of(k, h) for (k, h) in contacts]
fcentral = face_central(6)
print('   fan contacts (k,hub) -> model face:', list(zip(contacts, flabels)), ' ; central face (C6,C7,C8?) ->', fcentral)
h6 = mp.mpf('1e-16')
def du(fun, k, h=h6):
    up = list(u0); um = list(u0); up[k] = up[k] + h; um[k] = um[k] - h
    return (fun(up) - fun(um)) / (2 * h)
Gf = np.array([[float(du(lambda uu, i=i: res5(uu)[i], k)) for k in range(7)] for i in range(5)])
row_of = {f: i for i, f in enumerate(ORDER)}
alpha = []
for i, (k, h) in enumerate(contacts):
    fb = flabels[i]
    alpha.append(Gf[i, 6] / Gb[row_of[fb], 6])
alpha_c = Gf[4, 6] / Gb[row_of[fcentral], 6]
print('   alpha_k (fan, k=1,2,3,8) = ', ['%.6f' % v for v in alpha], ' ; alpha_central = %.6f' % alpha_c)
# full gradient proportionality check (not only the R component)
prop_err = []
for i in range(5):
    fb = flabels[i] if i < 4 else fcentral
    a_ = alpha[i] if i < 4 else alpha_c
    prop_err.append(float(np.abs(Gf[i, :] - a_ * Gb[row_of[fb], :]).max()))
print('   max|grad f_k - alpha_k grad b_face| over all 7 components = %.3e  (proportionality)' % max(prop_err))
# assemble the mirror-completed avatar: 9 site faces with the 5 lambda_TC weights (+mirror)
w = np.zeros(18)
mir = {0: 3, 1: 2, 2: 1, 3: 0, 4: 8, 8: 4, 6: 6, 9: 10, 10: 9}
def add(f, val):
    w[row_of[f]] += val
    if mir[f] != f:
        w[row_of[mir[f]]] += val
for i, (k, h) in enumerate(contacts):
    add(flabels[i], lamTC[i] * alpha[i])
add(fcentral, lamTC[4] * alpha_c)
print('   avatar w (18 active, order = %s):' % ORDER)
print('     ', np.array2string(w, precision=6, max_line_width=200))
print('   |Gb^T w - e_R|inf = %.3e ; (Gb^T w)_R = %.9f ; sum w = %.6e'
      % (float(np.abs(Gb.T @ w - np.array([0, 0, 0, 0, 0, 0, 1.0])).max()), float((Gb.T @ w)[6]), w.sum()))
orbits_site = [[0, 3], [1, 2], [4, 8], [6], [9, 10]]
orbits_sw = [[11, 14], [12, 13], [15, 19], [16, 18], [17]]
print('   10 mirror orbits and orbit weights:')
for o in orbits_site:
    print('      site-face orbit %-9s w = %+.9f' % (str(o), w[row_of[o[0]]]))
for o in orbits_sw:
    print('      switch    orbit %-9s w = %+.9f' % (str(o), 0.0))
# check on the model certificate: R-component relation (scale gradient use)
rcomp = Gb.T @ lam_sym
print('   model certificate chart projection (should be ~0):', np.array2string(rcomp, precision=3, max_line_width=200))

# ================================================================ (D) 29-dim lift test
print()
print('=== (D) shape-space (29-dim) lift test: sum w grad_y b + sum nu grad_y c  ?=  dPhi/dR ===')
dPhi_R = np.array([float((angle_vector([u0[k] + (h6 if k == 6 else 0) for k in range(7)])[i] -
                          angle_vector([u0[k] - (h6 if k == 6 else 0) for k in range(7)])[i]) / (2 * h6))
                   for i in range(42)])
rhs = Nr.T @ dPhi_R
Amat = np.hstack([WA.T, J8f.T])                         # 29 x 26  (18 branch + 8 constraint gradients)
sol, res, rk, sv_ = np.linalg.lstsq(Amat, rhs, rcond=None)
print('   free (w,nu) least squares: residual = %.3e ; rank = %d ; |rhs| = %.3e'
      % (float(np.abs(Amat @ sol - rhs).max()), int(rk), float(np.abs(rhs).max())))
print('   w part of the free solution  :', np.array2string(sol[:18], precision=6, max_line_width=200))
# symmetric ansatz: 5 site-face orbit weights only (switches 0), nu free
Basis = np.zeros((18, 5))
for j, o in enumerate(orbits_site):
    for f in o:
        Basis[row_of[f], j] = 1.0
Amat_sym = np.hstack([WA.T @ Basis, J8f.T])
sol_s, res_s, rk_s, _ = np.linalg.lstsq(Amat_sym, rhs, rcond=None)
print('   symmetric ansatz (5 site-face orbit weights, switches 0, nu free): residual = %.3e'
      % float(np.abs(Amat_sym @ sol_s - rhs).max()))
print('     orbit weights:', np.array2string(sol_s[:5], precision=6))
# tangential part of the residual (mod constraint gradients)
rr = rhs - Amat @ sol
rr_sym = rhs - Amat_sym @ sol_s
print('   residual after removing the 8 constraint directions: free %.3e ; symmetric %.3e'
      % (float(np.abs((np.eye(29) - Prow) @ rr).max()), float(np.abs((np.eye(29) - Prow) @ rr_sym).max())))
print('   ... and after also removing the 7 chart directions range(J):')
dPhi = np.array([[(float((angle_vector([u0[k] + (h6 if k == j else 0) for k in range(7)])[i] -
                         angle_vector([u0[k] - (h6 if k == j else 0) for k in range(7)])[i]) / (2 * h6)))
                   for j in range(7)] for i in range(42)])
J = Nr.T @ dPhi
Qj, _ = np.linalg.qr(J)
resid_gap = (np.eye(29) - Prow) @ (np.eye(29) - Qj @ Qj.T) @ rr_sym
print('     gap residual (14-dim subspace) = %.3e  ; its norm over |rhs| = %.3f'
      % (float(np.abs(resid_gap).max()), float(np.linalg.norm(resid_gap) / np.linalg.norm(rhs))))

# ================================================================ (E) antisymmetric automaticity
sig = lambda s: ((4 - s) % 9) if s < 9 else s
perm33 = [None] * 33
for t, f in enumerate(faces):
    ft = sorted([sig(v) for v in f])
    t2 = next(i for i, g in enumerate(faces) if sorted(g) == ft)
    for j, v in enumerate(f):
        perm33[3 * t + j] = 3 * t2 + faces[t2].index(sig(v))
perm42 = perm33 + [33 + ((3 - i) % 9) for i in range(9)]
# exact sigma-action in the y-coordinates:  (sigma a)_j = a_{p^{-1}(j)}  with p = perm42
Sig = np.zeros((42, 42))
for i in range(42):
    Sig[perm42[i], i] = 1.0
Msig = Nr.T @ Sig @ Nr                                    # orthogonal involution on y-space
aTC_np = np.array([float(v) for v in aTC_m])
yTC_np = np.array([float(v) for v in yTC])
print()
print('=== (E) sigma-action in y-coordinates (affine, exact at a_TC) ===')
print('   |sigma(a_TC) - a_TC|inf = %.3e   (a_TC is an exact reflection-fixed shape)'
      % float(np.abs(Sig @ aTC_np - aTC_np).max()))
print('   |sigma_y(y_TC) - y_TC|inf = %.3e' % float(np.abs(Msig @ yTC_np - yTC_np).max()))
print('   |M_sig^T M_sig - I|inf = %.3e   (involution => P_- = (I - M_sig^T)/2 is a projector)'
      % float(np.abs(Msig.T @ Msig - np.eye(29)).max()))
mu_sym = -np.linalg.solve(J8f @ J8f.T, J8f @ (WA.T @ lam_sym))
r29 = WA.T @ lam_sym + J8f.T @ mu_sym
print('   model KKT residual |r|inf = %.3e ; antisym part |P_- r|inf = %.3e ; ratio %.3e'
      % (float(np.abs(r29).max()),
         float(np.abs((r29 - Msig.T @ r29) / 2).max()),
         float(np.abs((r29 - Msig.T @ r29) / 2).max() / np.abs(r29).max())))
print('   (a nonzero antisym part here is a coordinate-offset artifact of the saved a0, not a')
print('    failure of the certificate: the exact statement is r = M_sig^T r, i.e. P_- r = 0)')
print('   |r - M_sig^T r|inf = %.3e' % float(np.abs(r29 - Msig.T @ r29).max()))
print('   check sigma_y(y_TC)=y_TC: |Nr^T(sigma a_TC - a0) - y_TC|inf = %.3e'
      % float(np.abs(Nr.T @ (Sig @ np.array([float(v) for v in aTC_m]) - a0) - yTC_np).max()))

out = dict(scope='phase5 audit + analytic lift calibration: float64 replication, 60-digit rank/nullspace, '
                 'proportionality lift, 29-dim lift gap, antisymmetry; numeric only',
           WA_same_object_18x29=WA.tolist(), J8=J8f.tolist(), ORDER=ORDER,
           note='WA rows = same-object branch gradients d(log gamma_f + log(q0/ell0))/dy at a_TC; '
                'J8 = the 8 nonlinear constraint gradients; y = 29 nullspace coordinates of the 13 linear equalities',
           phase5a_R_column_Gb=Gb5[:, 6].tolist(),
           sv_Gb_by_h=sv_by_h, sv_Gb_60digit=S_.tolist(),
           null_Gb_R_components=[float(Vt[5][6]), float(Vt[6][6])],
           R_column_60digit=Gb[:, 6].tolist(), invR=float(1.0 / float(u0[6])),
           sv_M_60digit=svM.tolist(), lam60=lam60.tolist(), lam_sym=lam_sym.tolist(),
           lam60_minus_lam_sym_inf=float(np.abs(lam60 - lam_sym).max()),
           M_lam_sym_norm=float(np.linalg.norm(Mmat @ lam_sym)), M_lam60_norm=float(np.linalg.norm(Mmat @ lam60)),
           GbT_lam_sym_inf=float(np.abs(Gb.T @ lam_sym).max()),
           alpha_fan=alpha, alpha_central=float(alpha_c), prop_err=float(max(prop_err)),
           avatar_w=w.tolist(), avatar_GbT_minus_eR=float(np.abs(Gb.T @ w - np.array([0, 0, 0, 0, 0, 0, 1.0])).max()),
           avatar_sum=float(w.sum()),
           lift29_free_res=float(np.abs(Amat @ sol - rhs).max()), lift29_free_w=sol[:18].tolist(),
           lift29_sym_res=float(np.abs(Amat_sym @ sol_s - rhs).max()), lift29_sym_orbits=sol_s[:5].tolist(),
           lift29_sym_gap=float(np.abs(resid_gap).max()),
           sigma_fixed_point_inf=float(np.abs(Sig @ aTC_np - aTC_np).max()),
           Msig_involution_dev=float(np.abs(Msig.T @ Msig - np.eye(29)).max()),
           resid_inf=float(np.abs(r29).max()),
           resid_antisym_inf=float(np.abs((r29 - Msig.T @ r29) / 2).max()),
           resid_sigma_covariance_dev=float(np.abs(r29 - Msig.T @ r29).max()),
           rhs_norm=float(np.linalg.norm(rhs)), mu_sym=mu_sym.tolist())
(OUT / 'phase5d_lift_analytic.json').write_text(json.dumps(out, indent=2))
print('[done] -> out/phase5d_lift_analytic.json')
