"""Phase 3c: resolve the "V0 dim 3 vs lead common kernel dim 4" discrepancy, raw data only.

Objects (29-dim nullspace coordinates y; a = point + Nr y):
  J8       8 x 29   gradients of the 8 nonlinear constraint residuals
  Jg      18 x 29   gradients of the 18 saved-active branch functions b_f
  gbar    = lam @ Jg (29,)  = grad Phi_lambda          (lam = saved sharp weights)
  K1 = [J8 ; Jg - gbar]                 (26 rows; lead's form, nonlinear_stress_probe.py L13-15)
  K2 = [J8 ; Jg[1:] - Jg[0]]            (25 rows; literal "differences of 18 g gradients")
  K3 = [J8 ; Jg]                        (26 rows; the form I used for V0)
  gspread = b_f - b_{f0} over the 18 active branches (tie check)

Two points: (A) original candidate a0 ; (B) the fixed-lambda Gauss-Newton refined point
(which enforces stationarity of Phi_lambda but NOT the 18 ties).

No optimisation, no intervalisation, no new starts. Numeric data + the one exact algebraic
fact (the lambda-weighted sum of the 18 centred rows is identically zero).
Writes only inside research-2026/team-current/r20-stress/out .
"""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np

import mp_model_r20 as MM

W_DIR = Path(__file__).parent; OUT = W_DIR / 'out'
M = MM.load()
ns, shape, Nr, a0 = M['ns'], M['shape'], M['Nr'], M['a0']
lam, act = np.asarray(M['lam']), np.asarray(M['act'])
P3 = json.loads((OUT / 'phase3_lambda_hessian.json').read_text())
y_ref = np.array(P3['point_refinement']['y_ref'])

POINTS = {'A_candidate_a0': np.zeros(29), 'B_refined_fixed_lambda': y_ref}
THRESH = [1e-4, 1e-6, 1e-7, 1e-8, 1e-9, 1e-10, 1e-12, 1e-14, 6.3e-15]


def svd_report(K, name):
    sv = np.linalg.svd(K, compute_uv=False)
    rows = []
    for t in THRESH:
        n_eff = int((sv > t).sum())
        rows.append(dict(rcond_or_abs=t, rank=n_eff, nullity=K.shape[1] - n_eff))
    return dict(name=name, shape=list(K.shape), sv=sv.tolist(),
                rank_default=int(np.linalg.matrix_rank(K)), nullity_default=K.shape[1] - int(np.linalg.matrix_rank(K)),
                rank_at=rows)


out = {'scope': 'dim-discrepancy resolution: raw SVD of [J8; centred/difference/raw active-branch gradient rows] '
                'and tie (g) spread; numeric except the stated exact identity', 'points': {}}
for tag, yp in POINTS.items():
    bc_p = MM.make_mp_model(dict(M, a0=a0 + Nr @ yp))
    G = np.array([[float(x) for x in row] for row in MM.jac_mp(bc_p)])
    J8, W = G[20:], G[:20]
    Jg = W[act]
    gbar = lam @ Jg
    K1 = np.vstack([J8, Jg - gbar])
    K2 = np.vstack([J8, Jg[1:] - Jg[0]])
    K3 = np.vstack([J8, Jg])
    rep = {k: svd_report(K, k) for k, K in (('K1_centred_26x29', K1), ('K2_diff_ref_25x29', K2), ('K3_raw_26x29', K3))}
    # tie / g spread at the point itself
    b, c8 = bc_p([0] * 29)
    bv = np.array([float(x) for x in b])[act]
    spread = bv - bv[0]
    a_p = a0 + Nr @ yp
    r64, con64, d64 = shape(a_p)
    gg = np.exp(d64['logg']); u = gg / gg.max()
    rep['ties'] = dict(g_spread=bv.tolist(), g_spread_span=float(spread.max() - spread.min()),
                       max_abs_g_spread=float(np.abs(spread).max()), argmax_f=int(act[int(np.argmax(np.abs(spread)))]),
                       n_ties_1e12=int((u > 1 - 1e-12).sum()), n_ties_1e9=int((u > 1 - 1e-9).sum()),
                       n_ties_1e7=int((u > 1 - 1e-7).sum()), u_active=[float(u[f]) for f in act])
    rep['point'] = dict(R=float(r64), res21=float(abs(con64).max()), y_norm=float(np.linalg.norm(yp)),
                        n_ties_1e12=rep['ties']['n_ties_1e12'])
    # exact algebraic fact check: lam-weighted sum of centred rows == 0 (roundoff only)
    Zsum = lam @ (Jg - gbar)
    rep['identity_check_lam_weighted_centred_sum'] = dict(abs_max=float(np.abs(Zsum).max()),
                                                          scales=float(np.abs(K1).max()))
    # symmetry: candidate mirror (site i -> 4-i mod 9). Check on the angle vector:
    # switch half-angles reverse under edge label i -> 3-i mod 9 ; z2 structure of the tangent space
    bsw = a_p[33:42]
    rep['symmetry_check'] = dict(switch_reversal_maxdiff=float(np.abs(bsw - bsw[[(3 - i) % 9 for i in range(9)]]).max()),
                                 note='site reflection i->(4-i) mod 9 induces edge labels i->(3-i) mod 9; '
                                      'checked on switch half-angles of the point')
    out['points'][tag] = rep
    print('== %s : R=%.17g res21=%.1e |y|=%.2e' % (tag, r64, abs(con64).max(), np.linalg.norm(yp)))
    for k in ('K1_centred_26x29', 'K2_diff_ref_25x29', 'K3_raw_26x29'):
        rr = rep[k]
        print('   %-20s sv(min 4) = %s | rank@1e-7=%d nullity@1e-7=%d | rank@1e-9=%d | rank default=%d'
              % (k, np.array2string(np.array(rr['sv'][-4:]), precision=3), 
                 [x['rank'] for x in rr['rank_at'] if x['rcond_or_abs'] == 1e-7][0],
                 [x['nullity'] for x in rr['rank_at'] if x['rcond_or_abs'] == 1e-7][0],
                 [x['rank'] for x in rr['rank_at'] if x['rcond_or_abs'] == 1e-9][0],
                 rr['rank_default']))
    print('   g-spread(18 active): max|b_f-b_ref|=%.3e  argmax=%d ; tied u>1-1e-12: %d ; u>1-1e-9: %d ; u>1-1e-7: %d'
          % (rep['ties']['max_abs_g_spread'], rep['ties']['argmax_f'], rep['ties']['n_ties_1e12'],
             rep['ties']['n_ties_1e9'], rep['ties']['n_ties_1e7']))
    print('   identity ||lam@(Jg-gbar)||inf = %.3e (scale %.1f) ; switch-reversal symmetry maxdiff = %.2e'
          % (rep['identity_check_lam_weighted_centred_sum']['abs_max'],
             rep['identity_check_lam_weighted_centred_sum']['scales'],
             rep['symmetry_check']['switch_reversal_maxdiff']))

(OUT / 'phase3c_dim_resolution.json').write_text(json.dumps(out, indent=2))
print('[done] -> out/phase3c_dim_resolution.json')
