"""Phase 6b: explicit cyclic nu formula of the lead, checked against the 12D solve.

In full physical coordinates (rho_j, theta_j, R):
    a_j(rho,R)=acos((rho^2+1-R^2)/(2 rho)),  a'_j = da_j/drho = (1-R^2-rho^2)/(2 rho^2 sin a_j) > 0
    g_i = delta_i - a_i - a_{i+1}   =>  dg_i/drho_j = -a'_j (delta_{ij} + delta_{i,j-1})
    f_c = active physical pin residuals (7 fan + 2 central), mu_c = -lambda_TC distributed by orbit
          (orbit sizes 2,2,2,1,2)
    v_j := sum_c mu_c df_c/drho_j   (theta, R fixed)  =>  nu_{j-1} + nu_j = v_j/a'_j =: w_j
    =>  nu_j = (1/2) sum_{k=0}^{8} (-1)^k w_{j-k}  (mod 9, odd cycle invertible)
Evaluation only, 60-digit FD.  Writes in r20-stress/out .
"""
import os, sys, json
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp
W = Path(__file__).parent; OUT = W / 'out'
sys.path.insert(0, str(W))
SRC = (W / 'phase6_boundary_nu.py').read_text(encoding='utf-8')
pre = SRC.split('# ------------------------------------------------------------------ branch-form covering KKT')[0]
NS = {'__name__': '__main__', '__file__': str(W / 'phase6_boundary_nu.py')}
exec(compile(pre, str(W / 'phase6_boundary_nu.py'), 'exec'), NS)
mp = NS['mp']; mp.mp.dps = 60
u0, tc_geo, root, lamTC = NS['u0'], NS['tc_geo'], NS['root'], NS['lamTC']
nu12 = np.array(NS['nu'])                      # 12D multipliers (representative gaps 0,1,2,3,8)
mu = np.array([float(-v) for v in lamTC])
g0 = tc_geo(u0)
R0 = g0['R']
rho = [abs(g0['C'][j][0] + 1j * g0['C'][j][1]) for j in range(9)]
rho = [mp.sqrt(g0['C'][j][0] ** 2 + g0['C'][j][1] ** 2) for j in range(9)]
th = [mp.atan2(g0['C'][j][1], g0['C'][j][0]) for j in range(9)]
hubs = g0['hubs']
H0 = (mp.mpf(float(hubs[0][0])), mp.mpf(0)); H1 = (mp.mpf(float(hubs[1][0])), mp.mpf(0))
print('rho =', [mp.nstr(v, 8) for v in rho])
print('theta(deg) =', [round(float(mp.degrees(v)), 4) for v in th])
print('a_arc(deg) =', [round(float(mp.degrees(mp.acos((rho[j]**2 + 1 - R0**2) / (2 * rho[j])))), 4) for j in range(9)])

# ---- full-space configuration from (rho, theta, R)
def centers_rt(r, t, R):
    return [(r[j] * mp.cos(t[j]), r[j] * mp.sin(t[j])) for j in range(9)], [H0, H1], R


def pin_of(C, P, Q):
    """radius-R circle intersection on the third-vertex side (third vertex passed implicitly by C,P,Q order)"""
    d = (Q[0] - P[0], Q[1] - P[1])
    c = mp.sqrt(d[0] ** 2 + d[1] ** 2)
    M = ((P[0] + Q[0]) / 2, (P[1] + Q[1]) / 2)
    n = (-d[1] / c, d[0] / c)
    hh = mp.sqrt(R0 * R0 - c * c / 4)
    third = C
    sgn = mp.mpf(1) if (third[0] - M[0]) * n[0] + (third[1] - M[1]) * n[1] >= 0 else mp.mpf(-1)
    return (M[0] + sgn * hh * n[0], M[1] + sgn * hh * n[1])


CONT_ORBIT = {                       # physical contact -> (orbit index in lamTC order, orbit size)
    ('fan', 1, 1): (0, 2), ('fan', 6, 1): (0, 2),
    ('fan', 2, 0): (1, 2), ('fan', 5, 0): (1, 2),
    ('fan', 3, 0): (2, 2), ('fan', 4, 0): (2, 2),
    ('fan', 8, 1): (3, 1),
    ('central', 6): (4, 2), ('central', 2): (4, 2),
}


def f_contact(kind, k, l, r, t, R):
    C, HH, _ = centers_rt(r, t, R)
    if kind == 'fan':
        P, Q, third = C[k], C[(k + 1) % 9], HH[l]
        U = pin_of(third, P, Q)
        return mp.sqrt((U[0] - third[0]) ** 2 + (U[1] - third[1]) ** 2) - R
    third = C[k]
    U = pin_of(third, HH[0], HH[1])
    return mp.sqrt((U[0] - third[0]) ** 2 + (U[1] - third[1]) ** 2) - R


def gap_i(i, r, t, R):
    a = [mp.acos((r[j] ** 2 + 1 - R * R) / (2 * r[j])) for j in range(9)]
    delta = [(t[(i + 1) % 9] - t[i]) % (2 * mp.pi) for i in range(9)]
    return [delta[i] - a[i] - a[(i + 1) % 9] for i in range(9)]


print('[check] contacts at the root: max|f| = %.3e   gaps: max|g| = %.3e'
      % (max(abs(float(f_contact(kd, k, l, rho, th, R0))) for (kd, k, l) in
             [('fan', 1, 1), ('fan', 6, 1), ('fan', 2, 0), ('fan', 5, 0), ('fan', 3, 0), ('fan', 4, 0), ('fan', 8, 1)] +
             [('central', 6, 0), ('central', 2, 0)]),
         max(abs(float(v)) for v in gap_i(0, rho, th, R0))))

HR = mp.mpf('1e-16')
# v_j = sum_c mu_c d f_c / d rho_j  (theta, R fixed)
v = []
for j in range(9):
    tot = mp.mpf(0)
    for (kind, k, l_or_dummy) in [('fan', 1, 1), ('fan', 6, 1), ('fan', 2, 0), ('fan', 5, 0),
                                  ('fan', 3, 0), ('fan', 4, 0), ('fan', 8, 1), ('central', 6, 0), ('central', 2, 0)]:
        oi, osz = CONT_ORBIT[(kind, k) if kind == 'central' else (kind, k, l_or_dummy)] if kind == 'central' \
            else CONT_ORBIT[(kind, k, l_or_dummy)]
        mu_c = mu[oi] / osz
        rp = list(rho); rm = list(rho); rp[j] = rp[j] + HR; rm[j] = rm[j] - HR
        fp = f_contact(kind, k, l_or_dummy if kind == 'fan' else 0, rp, th, R0)
        fm = f_contact(kind, k, l_or_dummy if kind == 'fan' else 0, rm, th, R0)
        tot += mu_c * (fp - fm) / (2 * HR)
    v.append(tot)
a_arr = [mp.acos((rho[j] ** 2 + 1 - R0 * R0) / (2 * rho[j])) for j in range(9)]
aprime = [(1 - R0 * R0 - rho[j] ** 2) / (2 * rho[j] ** 2 * mp.sin(a_arr[j])) for j in range(9)]
w = [v[j] / aprime[j] for j in range(9)]
nu_explicit = [mp.fsum([(-1) ** k * w[(j - k) % 9] for k in range(9)]) / 2 for j in range(9)]
print()
print('   v_j = sum mu_c df_c/drho_j :', [mp.nstr(x, 8) for x in v])
print('   a\'_j > 0 :', [mp.nstr(x, 8) for x in aprime])
print('   w_j = v_j/a\'_j :', [mp.nstr(x, 8) for x in w])
print('   nu_j (explicit cycl. sum) :', [mp.nstr(x, 8) for x in nu_explicit])
# compare with the 12D matrix-inversion nu, expanded on the 9 orbit representatives
GAPS_REP = [0, 1, 2, 3, 8]
nu_expanded = [mp.mpf(0)] * 9
for idx, gi in enumerate(GAPS_REP):
    nu_expanded[gi] = mp.mpf(float(nu12[idx]))
    pair = (7 - gi) % 9
    if pair != gi:
        nu_expanded[pair] = mp.mpf(float(nu12[idx]))
print('   nu expanded from 12D solve:', [mp.nstr(x, 8) for x in nu_expanded])
print('   max |nu_explicit - nu_12D| = %.3e'
      % float(max(abs(nu_explicit[j] - nu_expanded[j]) for j in range(9))))
# rho-component residual of the full KKT with the explicit nu
res = []
for j in range(9):
    tot = mp.mpf(0)
    for (kind, k, l_) in [('fan', 1, 1), ('fan', 6, 1), ('fan', 2, 0), ('fan', 5, 0),
                          ('fan', 3, 0), ('fan', 4, 0), ('fan', 8, 1), ('central', 6, 0), ('central', 2, 0)]:
        key = (kind, k) if kind == 'central' else (kind, k, l_)
        oi, osz = CONT_ORBIT[key]
        mu_c = mu[oi] / osz
        rp = list(rho); rm = list(rho); rp[j] = rp[j] + HR; rm[j] = rm[j] - HR
        fp = f_contact(kind, k, l_ if kind == 'fan' else 0, rp, th, R0)
        fm = f_contact(kind, k, l_ if kind == 'fan' else 0, rm, th, R0)
        tot += mu_c * (fp - fm) / (2 * HR)
    tot -= aprime[j] * (nu_explicit[j] + nu_explicit[(j - 1) % 9])
    res.append(tot)
print('   rho-component residual  max|v_j - a\'_j(nu_j+nu_{j-1})| = %.3e' % float(max(abs(x) for x in res)))
out = dict(scope='explicit cyclic nu formula calibration (evaluation only, 60-digit FD)',
           rho=[float(x) for x in rho], a_arc=[float(x) for x in a_arr], a_prime=[float(x) for x in aprime],
           v=[float(x) for x in v], w=[float(x) for x in w], nu_explicit=[float(x) for x in nu_explicit],
           nu_12D=[float(x) for x in nu_expanded],
           max_diff=float(max(abs(nu_explicit[j] - nu_expanded[j]) for j in range(9))),
           rho_residual=float(max(abs(x) for x in res)), mu=mu.tolist())
(OUT / 'phase6b_nu_explicit.json').write_text(json.dumps(out, indent=2))
print('[done] -> out/phase6b_nu_explicit.json')
