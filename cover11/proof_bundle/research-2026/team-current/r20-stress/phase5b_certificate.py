"""Phase 5b: (a) improve the numeric certificate by linear projection (no root Newton),
(b) identify the sigma-fixed active factors, (c) identify the 2 chart directions annihilated by
the branch differentials (rank(Gb) = 5 of 7), (d) relation between the TC branch-avatar and the
model certificate. Evaluation + small linear algebra only.
"""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp

W_DIR = Path(__file__).parent; OUT = W_DIR / 'out'
mp.mp.dps = 50
P5 = json.loads((OUT / 'phase5a_kkt_weights.json').read_text())
# re-run the phase-5a prefix in its own namespace to reuse its objects (same file, no edits)
P5A = W_DIR / 'phase5a_kkt_weights.py'
_src = P5A.read_text(encoding='utf-8').split('# ---------------- (4)')[0]
NS = {'__name__': '__main__', '__file__': str(P5A)}
exec(compile(_src, str(P5A), 'exec'), NS)
Mmat, J8, Jg, act, pi, lam = NS['Mmat'], NS['J8'], NS['Jg'], NS['act'], NS['pi'], NS['best']
Nr, bc, a_TC, u0 = NS['Nr'], NS['bc'], NS['a_TC'], NS['u0']
angle_vector, res5 = NS['angle_vector'], NS['res5']
print('[reuse] act =', act.tolist(), ' ; sv(M) min = %.3e' % np.linalg.svd(Mmat, compute_uv=False)[-1])
lam_c = lam.copy()
for it in range(4):
    r = Mmat @ lam_c
    step = -np.linalg.lstsq(Mmat, r, rcond=None)[0]
    lam_c = lam_c + step
    lam_c = np.clip(lam_c, 0, None)
    lam_c = lam_c / lam_c.sum()
    print('[proj %d] ||M lam|| = %.3e  min lam = %.6e  sum = %.15f' % (it, float(np.linalg.norm(Mmat @ lam_c)), lam_c.min(), lam_c.sum()))
mu_c = -np.linalg.solve(J8 @ J8.T, J8 @ (Jg.T @ lam_c))
full = float(np.abs(Jg.T @ lam_c + J8.T @ mu_c).max())
print('[proj] full stationarity ||Jg^T lam + J8^T mu||inf = %.3e' % full)
# sigma-fixed active factors
pos = {int(f): i for i, f in enumerate(act)}
fixed = [act[i] for i in range(18) if int(pi[act[i]]) == act[i]]
print('[mirror] sigma-fixed active factors:', fixed, '(site face <11, switch >=11)')
Pact = np.array([pos[int(pi[f])] for f in act])
orbits, seen = [], set()
for i in range(18):
    if i not in seen:
        j = int(Pact[i]); seen.add(i); seen.add(j); orbits.append([i, j] if j != i else [i])
print('[mirror] %d orbits (pairs %d, fixed %d)' % (len(orbits), sum(1 for o in orbits if len(o) == 2), sum(1 for o in orbits if len(o) == 1)))
lam_sym = 0.5 * (lam_c + lam_c[Pact])
print('[mirror] symmetric certificate: ||M lam_sym|| = %.3e ; min = %.6e ; ||lam_sym-lam_c||inf = %.2e'
      % (float(np.linalg.norm(Mmat @ lam_sym)), lam_sym.min(), float(np.abs(lam_sym - lam_c).max())))
# chart (rebuilt here, same formulas as phase 5a)
pinvNr = np.linalg.pinv(Nr)
def bf_on_chart(u, f):
    y = pinvNr @ (angle_vector(u) - a_TC)
    return float(bc([mp.mpf(float(x)) for x in y])[0][f])
def cd(fun, k, h=1e-7):
    up = u0.copy(); um = u0.copy(); up[k] += h; um[k] -= h
    return (fun(up) - fun(um)) / (2 * h)
Gb = np.array([[cd(lambda uu, f=f: bf_on_chart(uu, f), k) for k in range(7)] for f in act])
Gf = np.array([[cd(lambda uu, i=i: float(res5(uu)[i]), k) for k in range(7)] for i in range(5)])
print('[chart] max|Gb^T lam_sym| = %.3e (certificate), %.3e (projected)' % (float(np.abs(Gb.T @ lam_sym).max()), float(np.abs(Gb.T @ lam_c).max())))
Vh = np.linalg.svd(Gb)[2]
nullG = Vh[-2:]                                     # 2 dims annihilated by the branch differentials
print('[chart] null directions of Gb (7-dim chart vectors):')
for v in nullG:
    print('   ', np.array2string(v / np.linalg.norm(v), precision=6))
Yt = np.linalg.lstsq(Gb.T, Gf.T, rcond=None)[0]
lamT = np.array(P5['lift']['lam_TC'])
avatar = Yt @ lamT
print('[lift] ||Gb^T avatar - e_R||inf = %.3e ; avatar sum = %.6f'
      % (float(np.abs(Gb.T @ avatar - np.array([0, 0, 0, 0, 0, 0, 1.0])).max()), float(avatar.sum())))
lam_s = lam_sym / lam_sym.sum()
proj_av = float(avatar @ lam_s) / float(lam_s @ lam_s) * lam_s
print('[lift] projection of the TC avatar onto the model certificate direction: ratio = %.6f ; residual = %.3e'
      % (float(avatar @ lam_s) / float(lam_s @ lam_s), float(np.linalg.norm(avatar - proj_av))))
print('[lift] avatar / certificate componentwise range: avatar [%.3e, %.3e], cert [%.3e, %.3e]'
      % (avatar.min(), avatar.max(), lam_s.min(), lam_s.max()))
out = dict(scope='certificate improvement + sigma-fixed factors + chart null directions + lift relation',
           lam_projected=lam_c.tolist(), res_projected=float(np.linalg.norm(Mmat @ lam_c)),
           full_stationarity_inf=full, mu=mu_c.tolist(),
           sigma_fixed_active=[int(v) for v in fixed], n_orbits=len(orbits), orbits=[[int(x) for x in o] for o in orbits],
           lam_sym=lam_sym.tolist(), res_sym=float(np.linalg.norm(Mmat @ lam_sym)),
           chart=dict(gb_rank=int((np.linalg.svd(Gb, compute_uv=False) > 1e-6).sum()),
                      null_directions=(nullG / np.linalg.norm(nullG, axis=1, keepdims=True)).tolist(),
                      projected_cert_res=float(np.abs(Gb.T @ lam_sym).max())),
           lift=dict(avatar=avatar.tolist(), avatar_sum=float(avatar.sum()),
                     GbT_avatar_minus_eR=float(np.abs(Gb.T @ avatar - np.array([0, 0, 0, 0, 0, 0, 1.0])).max()),
                     ratio=float(avatar @ lam_s) / float(lam_s @ lam_s),
                     residual=float(np.linalg.norm(avatar - proj_av))))
(OUT / 'phase5b_certificate.json').write_text(json.dumps(out, indent=2))
print('[done] -> out/phase5b_certificate.json')
