"""Phase 5c: AUDIT of the chart Jacobian Gb used in PHASE5 (same-object check + scale gradient).

Question (lead/user): the PHASE5 report claims (i) rank(Gb)=5 with two zero chart directions whose
R-components are ~1e-11 and (ii) the "branch avatar" w = Yt lam_TC satisfies Gb^T w = e_R.
If Gb's R-column were ~0 those two could not coexist.  We therefore recompute, in 60-digit
arithmetic and with the SAME object (b_f = log gamma_f + log(q0/ell0)),

  * d(b_f o Phi)/du   (18 x 7 chart Jacobian, Phi = TC chart -> 42 angles)
  * its decomposition  Gb = G_gauge + 1 s^T   with  s_k = d/du_k log(q0/ell0)
  * the R-column, the SVD and the null directions,
  * the identity check exp(b_switch) = R_chart  (physical meaning of the R-column),
  * d R_shape / du          (compare with phase4c's float64 value -1.658),
  * pullback of the TC stationarity  J^T e_R  and its representability in span{d b_f, d c_j}.

Numerics only as CALIBRATION; no optimization, no root finding.
Writes only in r20-stress/out .
"""
import os, json, sys
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp

W_DIR = Path(__file__).parent; OUT = W_DIR / 'out'; LEAD = W_DIR.parent / 'lead'
sys.path.insert(0, str(W_DIR))
mp.mp.dps = 60

import mp_model_r20 as MM

M0 = MM.load()
ns = M0['ns']; a0 = np.array(M0['a0']); Nr = np.array(M0['Nr'])
faces = [list(f) for f in ns['faces']]
Am = [[mp.mpf(float(x)) for x in row] for row in np.asarray(ns['A'])[:, :42]]
Bm = [[mp.mpf(float(x)) for x in row] for row in np.asarray(ns['B'])[:, :42]]
alm = [[mp.mpf(float(x)) for x in row] for row in np.asarray(ns['alpha'])[:, :42]]
acm = [mp.mpf(float(x)) for x in np.asarray(ns['ac'])]
adj = M0['adj']
D = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text())
root = [mp.mpf(s) for s in D['numeric_root']]
u0 = [mp.mpf(float(root[k])) for k in range(7)]                      # same point as phase5a (float64 read)
lamTC = np.array([float(v) for v in root[7:]])
R0 = u0[6]

# ---------------------------------------------------------------- chart geometry (mp)
def tc_geo(u):
    a04 = [mp.mpf(u[k]) for k in range(4)]
    y0, y1, R = mp.mpf(u[4]), mp.mpf(u[5]), mp.mpf(u[6])
    a4 = mp.pi - 2 * sum(a04)
    a = [a04[0], a04[1], a04[2], a04[3], a4, a04[3], a04[2], a04[1], a04[0]]
    rho = [mp.cos(a[k]) - mp.sqrt(R * R - mp.sin(a[k]) ** 2) for k in range(9)]
    th = [mp.mpf(0)] * 9
    for k in range(5, 9):
        th[k] = th[k - 1] + a[k - 1] + a[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (a[k] + a[k + 1])
    C = [(rho[k] * mp.cos(th[k]), rho[k] * mp.sin(th[k])) for k in range(9)]
    Bp = [(mp.cos(th[k] + a[k]), mp.sin(th[k] + a[k])) for k in range(9)]
    U = [(C[k][0] + C[(k + 1) % 9][0] - Bp[k][0], C[k][1] + C[(k + 1) % 9][1] - Bp[k][1])
         for k in range(9)]
    hubs = [(y0, mp.mpf(0)), (y1, mp.mpf(0))]
    m_, d_ = (y0 + y1) / 2, (y1 - y0) / 2
    waist = (m_, mp.sqrt(R * R - d_ * d_))
    return dict(a=a, C=C, Bp=Bp, U=U, hubs=hubs, waist=waist, R=R, th=th, rho=rho)


def angle_vector(u):
    g = tc_geo(u)
    pts = {((6 - k) % 9): g['C'][k] for k in range(9)}
    pts[9], pts[10] = g['hubs'][0], g['hubs'][1]
    ang = []
    for f in faces:
        for j in range(3):
            p = pts[f[j]]; q = pts[f[(j + 1) % 3]]; r = pts[f[(j + 2) % 3]]
            v1 = (q[0] - p[0], q[1] - p[1]); v2 = (r[0] - p[0], r[1] - p[1])
            ang.append(mp.atan2(abs(v1[0] * v2[1] - v1[1] * v2[0]), v1[0] * v2[0] + v1[1] * v2[1]))
    for s in range(9):
        i = (5 - s) % 9
        dd = mp.sqrt((g['C'][i][0] - g['C'][(i + 1) % 9][0]) ** 2 + (g['C'][i][1] - g['C'][(i + 1) % 9][1]) ** 2)
        ang.append(mp.asin(dd / (2 * g['R'])))
    return ang


def model_quant(alist):
    """Same object as mp_model_r20.bc, but returning all intermediate shape functionals."""
    Aa = [mp.fsum([Am[j][i] * alist[i] for i in range(42)]) for j in range(21)]
    Ba = [mp.fsum([Bm[j][i] * alist[i] for i in range(42)]) for j in range(21)]
    ls = [mp.log(mp.sin(Aa[j])) - mp.log(mp.sin(Ba[j])) for j in range(21)]
    logg = {0: mp.mpf(0)}; todo = [0]; tree = []
    for f in todo:
        for (g, k, d) in adj[f]:
            if g not in logg:
                logg[g] = logg[f] + d * ls[k]; todo.append(g); tree.append(k)
    lg = [logg[f] for f in range(20)]
    gsw = [logg[11 + i] for i in range(9)]
    alv = [acm[i] + mp.fsum([alm[i][j] * alist[j] for j in range(42)]) for i in range(9)]
    us = [mp.e ** gsw[(i - 1) % 9] for i in range(9)]
    vs = [mp.e ** gsw[i] for i in range(9)]
    ell = [mp.sqrt((us[i] - vs[i]) ** 2 + 4 * us[i] * vs[i] * mp.sin(alv[i] / 2) ** 2) for i in range(9)]
    Lv = [mp.atan2(vs[i] * mp.sin(alv[i]), us[i] - vs[i] * mp.cos(alv[i])) for i in range(9)]
    tau = [mp.pi - (mp.pi - alv[i] - Lv[i]) - Lv[(i + 1) % 9] - 2 * alist[33 + i] for i in range(9)]
    w = [mp.fsum([(-1) ** ((j - i) % 9) * tau[j] for j in range(9)]) for i in range(9)]
    q = [2 * mp.sin(w[i] / 2) for i in range(9)]
    rat = [q[i] / ell[i] for i in range(9)]
    b = [lg[f] + mp.log(rat[0]) for f in range(20)]
    return dict(logg=lg, gsw=gsw, us=us, al=alv, ell=ell, L=Lv, w=w, q=q, rat=rat, b=b,
                M=max(lg), Rshape=max(b), tree=tree)


def at(u):
    return model_quant(angle_vector(u))


Q0 = at(u0)
# ---------------------------------------------------------------- consistency checks
geom = tc_geo(u0)
chk = {}
# R_shape = max_f b_f is a LOG: compare exp(max b) with R_chart, and max b with log R_chart.
chk['exp_maxb_minus_R'] = float(mp.e ** Q0['Rshape'] - geom['R'])
chk['maxb_minus_logR'] = float(Q0['Rshape'] - mp.log(geom['R']))
chk['max_abs_b_minus_logR'] = float(max(abs(Q0['b'][f] - mp.log(geom['R'])) for f in [0, 1, 2, 3, 4, 6, 8, 9, 10] + list(range(11, 20))))
chk['exp_b_switch_minus_R'] = [float(mp.e ** Q0['b'][11 + i] - geom['R']) for i in range(9)]
chk['max_spread_b'] = float(max(Q0['b']) - min(Q0['b']))
chk['switch_gauge_spread'] = float(max(Q0['gsw']) - min(Q0['gsw']))
print('[check] exp(max_f b_f) - R_chart = %.3e ; max b - log R_chart = %.3e'
      % (chk['exp_maxb_minus_R'], chk['maxb_minus_logR']))
print('[check] max|b_f - log R| over 18 branches = %.3e' % chk['max_abs_b_minus_logR'])
print('[check] exp(b_switch) - R_chart  (should be 0 : switch leg = ring radius) :',
      ['%.1e' % v for v in chk['exp_b_switch_minus_R']][:3], 'max %.2e' % max(abs(v) for v in chk['exp_b_switch_minus_R']))
print('[check] 20-branch log spread = %.3e (18 tied at log R, 2 slack)' % chk['max_spread_b'])
print('[check] switch gauge spread = %.3e (all legs equal => all gauge equal)' % chk['switch_gauge_spread'])

# contact residuals of res5 at u0
def res5(u):
    g = tc_geo(u)
    dist = lambda p, q: mp.sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)
    out = [dist(g['U'][k], g['hubs'][l]) - g['R'] for (k, l) in [(1, 1), (2, 0), (3, 0), (8, 1)]]
    out.append(dist(g['waist'], g['C'][6]) - g['R'])
    return out
chk['res5_at_u0'] = [float(v) for v in res5(u0)]
print('[check] res5(u0) =', ['%.2e' % v for v in chk['res5_at_u0']])

# ---------------------------------------------------------------- high precision chart Jacobians
H = mp.mpf('1e-15')
def dFD(fun, k, h=H):
    up = list(u0); um = list(u0); up[k] = up[k] + h; um[k] = um[k] - h
    return (fun(up) - fun(um)) / (2 * h)

Nb = 20
Gb = np.array([[float(dFD(lambda uu, f=f: at(uu)['b'][f], k)) for k in range(7)] for f in range(20)])
Ggauge = np.array([[float(dFD(lambda uu, f=f: at(uu)['logg'][f], k)) for k in range(7)] for f in range(20)])
s_scale = np.array([float(dFD(lambda uu: mp.log(at(uu)['rat'][0]), k)) for k in range(7)])
GgeomR = np.array([float(dFD(lambda uu: tc_geo(uu)['R'], k)) for k in range(7)])
# R_shape = max_f b_f has NO ordinary gradient at the 18-tie.  Along each chart direction report the
# one-sided directional derivatives  D+ = max_f d_k b_f ,  D- = -min_f d_k b_f ,  and the central FD
# (which is their average, NOT a directional derivative).
Dplus = Gb.max(axis=0)
Dminus = -Gb.min(axis=0)
Gcentral = np.array([float(dFD(lambda uu: at(uu)['Rshape'], k, mp.mpf('1e-5'))) for k in range(7)])
print()
print('== R-column of the same-object chart Jacobian (k=6) ==')
print('   d b_f / dR  (f=0..19): ', np.array2string(Gb[:, 6], precision=6, max_line_width=200))
print('   d log gamma_f / dR   : ', np.array2string(Ggauge[:, 6], precision=6, max_line_width=200))
print('   d log(q0/ell0) / dR  : %.8f     (scale part; 1/R = %.8f)' % (s_scale[6], 1.0 / float(R0)))
print('   => Gb[:,6] = gauge part + scale part (check max dev): %.3e'
      % float(np.abs(Gb[:, 6] - (Ggauge[:, 6] + s_scale[6])).max()))
Gcentral_15 = np.array([float(dFD(lambda uu: at(uu)['Rshape'], k, mp.mpf('1e-15'))) for k in range(7)])
print()
print('== R_shape = max_f b_f along the chart: NO ordinary gradient at the tie ==')
print('   central FD (h=1e-5)  of max_f b_f : ', np.array2string(Gcentral, precision=8, max_line_width=200))
print('   central FD (h=1e-15) of max_f b_f : ', np.array2string(Gcentral_15, precision=8, max_line_width=200))
print('   one-sided D+ = max_f d_k b_f : ', np.array2string(Dplus, precision=8, max_line_width=200))
print('   one-sided D- = -min_f d_k b_f:', np.array2string(Dminus, precision=8, max_line_width=200))
print('   => the central FD is an h-dependent mixture (tie scale 1.8e-16), not a derivative;')
print('      phase4c dR_shape/dR = -1.658 is of this kind.  Clean one-sided values: D+_R = %.6f'
      % Dplus[6], ' , D-_R = %.6f' % Dminus[6])

# tc stationarity J^T e_R  and pullback of the contacts
dPhi = np.array([[float(dFD(lambda uu, i=i: angle_vector(uu)[i], k)) for k in range(7)] for i in range(42)])  # 42x7
J = Nr.T @ dPhi                                                     # 29x7  shape tangent of the chart
print()
print('[chart] rank(dPhi) = %d ; ||Nr^T Nr - I||inf = %.2e'
      % (int((np.linalg.svd(dPhi, compute_uv=False) > 1e-9).sum()), float(np.abs(Nr.T @ Nr - np.eye(29)).max())))
Jf = np.array([[float(dFD(lambda uu, i=i: res5(uu)[i], k)) for k in range(7)] for i in range(5)])
lhs = Jf.T @ lamTC
print('[chart] TC stationarity sum lam_k grad_u f_k =', np.array2string(lhs, precision=8))
print('[chart] residual vs e_R = %.3e' % float(np.abs(lhs - np.array([0, 0, 0, 0, 0, 0, 1.0])).max()))

# ---------------------------------------------------------------- lift bookkeeping (numerics as calibration)
Gbl = Gb[[0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19], :]     # 18 active
sv = np.linalg.svd(Gbl, compute_uv=False)
print()
print('[lift] sv(Gb|active 18x7) =', np.array2string(sv, precision=4))
print('[lift] rank by threshold 1e-6: %d ; by 1e-12: %d ; condition number %.2e'
      % (int((sv > 1e-6).sum()), int((sv > 1e-12).sum()), float(sv[0] / sv[-1])))
Yt = np.linalg.lstsq(Gbl.T, Jf.T, rcond=None)[0]
fit = Gbl.T @ Yt
print('[lift] fit Gf^T ~ Gb^T Yt : residual %.3e (relative %.3e) --- to be interpreted, not exact'
      % (float(np.abs(fit - Jf.T).max()), float(np.abs(fit - Jf.T).max() / np.abs(Jf.T).max())))
av = Yt @ lamTC
print('[lift] avatar w = Yt lam_TC : |Gb^T w - e_R|inf = %.3e ; sum w = %.6f ; min w = %.3e ; max w = %.3e'
      % (float(np.abs(Gbl.T @ av - np.array([0, 0, 0, 0, 0, 0, 1.0])).max()), float(av.sum()), float(av.min()), float(av.max())))
# what e_R needs from the R column alone
print('[lift] (Gb^T w)_R = sum_f w_f dR b_f = %.6f  while (e_R)_R = 1' % float((Gbl.T @ av)[6]))

# pullback of the TC stationarity to the shape space, and its representation test
rhs = J @ (Jf.T @ lamTC)                                            # = J e_R = dPhi/dR  (29)
rhs_direct = np.array([float(dFD(lambda uu, i=i: angle_vector(uu)[i], 6)) for i in range(42)])
rhs29 = Nr.T @ rhs_direct
print('[lift] J^T (sum lam grad f) vs dPhi/dR : %.3e' % float(np.abs(rhs - rhs29).max()))

out = dict(scope='AUDIT of phase5 chart Jacobian in the same object (b_f = log gamma_f + log(q0/ell0)); 60-digit '
                 'FD calibration only, no exactness claim',
           u0=[float(v) for v in u0], R_chart=float(R0), lam_TC=lamTC.tolist(),
           checks=chk,
           R_column=dict(b=Gb[:, 6].tolist(), gauge=Ggauge[:, 6].tolist(), scale=float(s_scale[6]),
                         decomposition_max_dev=float(np.abs(Gb[:, 6] - (Ggauge[:, 6] + s_scale[6])).max())),
           Rshape_derivs=dict(central_FD=Gcentral.tolist(), Dplus=Dplus.tolist(), Dminus=Dminus.tolist(),
                              note='max_f b_f is nonsmooth at the 18-tie: only one-sided directional '
                                   'derivatives exist; central FD = (D+ - D-)/2'),
           Gb=Gb.tolist(), Ggauge=Ggauge.tolist(), s_scale=s_scale.tolist(),
           sv_Gb_active=sv.tolist(), rank_1e6=int((sv > 1e-6).sum()), rank_1e12=int((sv > 1e-12).sum()),
           res5_at_u0=chk['res5_at_u0'], Jf=Jf.tolist(), TC_residual=float(np.abs(lhs - np.array([0, 0, 0, 0, 0, 0, 1.0])).max()),
           lift_fit_res=float(np.abs(fit - Jf.T).max()), avatar=av.tolist(),
           avatar_GbT_minus_eR=float(np.abs(Gbl.T @ av - np.array([0, 0, 0, 0, 0, 0, 1.0])).max()),
           pullback_TC=rhs.tolist(), pullback_check=float(np.abs(rhs - rhs29).max()))
(OUT / 'phase5c_scale_audit.json').write_text(json.dumps(out, indent=2))
print('[done] -> out/phase5c_scale_audit.json')
