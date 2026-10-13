"""Phase 6 (lead's priority): physical symmetric coordinates, boundary B definition, nu calibration,
reflection lift to the full 23D physical space.  EVALUATION ONLY at the certified TC root box
(no root finding, no optimization).  All quantities are computed in 60-digit arithmetic and the
numbers are CALIBRATION, not a proof.

Symmetric coordinates x in R^12 (TC labels):
    x = (u0,v0, u1,v1, u2,v2, u3,v3, u4, y0, y1, R)
    C_k = (u_k, v_k) for k=0..3,  C_{8-k} = (u_k, -v_k),  C_4 = (u_4, 0),
    hubs H0=(y0,0), H1=(y1,0), ring/covering radius R.

Boundary gap constraints (lead's TC-BOUNDARY-CHART-RANK):
    a_k = acos((rho_k^2 + 1 - R^2)/(2 rho_k))          (inward branch, arc half width)
    delta_i = theta_{i+1} - theta_i (unwrapped)        (angular gap)
    g_i = delta_i - a_i - a_{i+1},  i mod 9             -> 5 reflection orbits {0,7},{1,6},{2,5},{3,4},{8}
Interior pin residuals (lead's TC-TO-PHYSICAL-KKT-LIFT):
    pin_k = inner circle intersection of (C_k,C_{k+1}) with radius R
    F_k = |pin_k - H_l| - R   for the 7 fan contacts;   central: F = |W - C_6| - R, W=(m,+sqrt(R^2-d^2))
    -> 5 reflection orbits.

Lift:  w := dR + sum_i mu_i dF_i  with mu = -lambda_TC  must lie in rowspan(DB);
       nu = -(DB DB^T)^-1 DB w ,  residual w + DB^T nu == 0  (exact content: TC root + chart).
"""
import os, sys, json
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp

W = Path(__file__).parent; OUT = W / 'out'; LEAD = W.parent / 'lead'
sys.path.insert(0, str(W))
SRC = (W / 'phase5c_scale_audit.py').read_text(encoding='utf-8')
pre = SRC.split('# ---------------------------------------------------------------- high precision chart Jacobians')[0]
NS = {'__name__': '__main__', '__file__': str(W / 'phase5c_scale_audit.py')}
exec(compile(pre, str(W / 'phase5c_scale_audit.py'), 'exec'), NS)
u0, tc_geo, at, faces = NS['u0'], NS['tc_geo'], NS['at'], NS['faces']
mp = NS['mp']; mp.mp.dps = 60
root = NS['root']
lamTC = [mp.mpf(float(v)) for v in root[7:]]              # all negative (lead's sign convention)

# ------------------------------------------------------------------ chart point -> symmetric x0
g0 = tc_geo(u0)
C0 = g0['C']; hubs0 = g0['hubs']; R0 = g0['R']
x0 = [C0[0][0], C0[0][1], C0[1][0], C0[1][1], C0[2][0], C0[2][1], C0[3][0], C0[3][1],
      C0[4][0], hubs0[0][0], hubs0[1][0], R0]
print('R =', mp.nstr(R0, 16))
# mirror consistency check
mm = max(max(abs(C0[k][0] - C0[8 - k][0]), abs(C0[k][1] + C0[8 - k][1])) for k in range(4))
print('[mirror] max|C_k - mirror(C_{8-k})| = %.3e  (0 => symmetric coords exact)' % mm)


def unpack(x):
    u0_, v0_, u1_, v1_, u2_, v2_, u3_, v3_, u4_, y0_, y1_, R_ = x
    C = [(u0_, v0_), (u1_, v1_), (u2_, v2_), (u3_, v3_), (u4_, mp.mpf(0)),
         (u3_, -v3_), (u2_, -v2_), (u1_, -v1_), (u0_, -v0_)]
    return C, [(y0_, mp.mpf(0)), (y1_, mp.mpf(0))], R_


def norm2(p):
    return p[0] * p[0] + p[1] * p[1]


def sub(p, q):
    return (p[0] - q[0], p[1] - q[1])


def cross2(p, q):
    return p[0] * q[1] - p[1] * q[0]


def gaps(x):
    C, hubs, R = unpack(x)
    th = [mp.atan2(C[k][1], C[k][0]) for k in range(9)]      # all |theta|<pi near the root
    delta = [th[i + 1] - th[i] for i in range(8)] + [th[0] + 2 * mp.pi - th[8]]
    a = [mp.acos((norm2(C[k]) + 1 - R * R) / (2 * mp.sqrt(norm2(C[k])))) for k in range(9)]
    return [delta[i] - a[i] - a[(i + 1) % 9] for i in range(9)], a, delta, th


def pin_pair(P, Q, third, R):
    """the circle-circle intersection of the two radius-R circles about P,Q that lies on the
    third vertex's side of the chord line (lead's physical extension; no unit-tie input)."""
    d = sub(Q, P)
    c = mp.sqrt(norm2(d))
    M = ((P[0] + Q[0]) / 2, (P[1] + Q[1]) / 2)
    n = (-d[1] / c, d[0] / c)
    hh = mp.sqrt(R * R - c * c / 4)
    sgn = mp.mpf(1) if (third[0] - M[0]) * n[0] + (third[1] - M[1]) * n[1] >= 0 else mp.mpf(-1)
    return (M[0] + sgn * hh * n[0], M[1] + sgn * hh * n[1])


def pin(x, k, third):
    C, hubs, R = unpack(x)
    return pin_pair(C[k], C[(k + 1) % 9], third, R)


def fanF(x, k, l):
    C, hubs, R = unpack(x)
    P = pin(x, k, hubs[l])
    return mp.sqrt(norm2(sub(P, hubs[l]))) - R


def centralF(x, k=6):
    C, hubs, R = unpack(x)
    W = pin_pair(hubs[0], hubs[1], C[k], R)
    return mp.sqrt(norm2(sub(W, C[k]))) - R


CONTACTS = [('fan', 1, 1), ('fan', 2, 0), ('fan', 3, 0), ('fan', 8, 1), ('central', 6, 0)]
GAPS = [0, 1, 2, 3, 8]                                     # orbit representatives


def Fvec(x):
    out = []
    for (kind, k, l) in CONTACTS:
        out.append(fanF(x, k, l) if kind == 'fan' else centralF(x))
    return out


def Gvec(x):
    gg, a, delta, th = gaps(x)
    return [gg[i] for i in GAPS]


print('[chart] max|F| = %.3e ; max|g| (9 gaps) = %.3e ; (both must vanish on the TC chart)'
      % (max(abs(v) for v in Fvec(x0)), max(abs(v) for v in gaps(x0)[0])))
print('[chart] gap closure sum_i delta_i = %.15f (2pi)' % float(sum(gaps(x0)[2])))
print('[chart] max_i |delta_i - (a_i+a_{i+1})| = %.3e'
      % max(abs(gaps(x0)[0][i]) for i in range(9)))

H = mp.mpf('1e-16')
def grad12(fun):
    out = []
    for j in range(12):
        xp = list(x0); xm = list(x0); xp[j] = xp[j] + H; xm[j] = xm[j] - H
        out.append((fun(xp) - fun(xm)) / (2 * H))
    return out

DF = [grad12(lambda x, i=i: Fvec(x)[i]) for i in range(5)]
DB = [grad12(lambda x, i=i: Gvec(x)[i]) for i in range(5)]
DF = np.array([[float(v) for v in row] for row in DF])
DB = np.array([[float(v) for v in row] for row in DB])
print()
print('=== symmetric 12D space ===')
print('   sv(DB) =', np.array2string(np.linalg.svd(DB, compute_uv=False), precision=6), ' => rank 5')
print('   sv(DF) =', np.array2string(np.linalg.svd(DF, compute_uv=False), precision=6))
# chart tangency: DB . dPhi/du == 0
dPhi_u = np.array([[float((NS['angle_vector']([u0[k] + (H if k == j else 0) for k in range(7)])[i] -
                           NS['angle_vector']([u0[k] - (H if k == j else 0) for k in range(7)])[i]) / (2 * H))
                    for j in range(7)] for i in range(42)])
# chart -> x map differential (7 -> 12)
def x_of_chart(u):
    gg = tc_geo(u)
    C = gg['C']; hubs = gg['hubs']
    return [C[0][0], C[0][1], C[1][0], C[1][1], C[2][0], C[2][1], C[3][0], C[3][1], C[4][0],
            hubs[0][0], hubs[1][0], gg['R']]
dXdu = np.array([[float((x_of_chart([u0[k] + (H if k == j else 0) for k in range(7)])[i] -
                         x_of_chart([u0[k] - (H if k == j else 0) for k in range(7)])[i]) / (2 * H))
                  for j in range(7)] for i in range(12)])
print('   max|DB @ dX/du| = %.3e   (chart lands in {B=0}: must vanish, order of the root box)'
      % float(np.abs(DB @ dXdu).max()))
mu = np.array([float(-v) for v in lamTC])                   # mu = -lambda_TC > 0
w = np.zeros(12); w[11] = 1.0
for i in range(5):
    w = w + mu[i] * DF[i]
print()
print('   mu = -lambda_TC =', np.array2string(mu, precision=9), ' (all positive?)', bool((mu > 0).all()))
nu = -np.linalg.solve(DB @ DB.T, DB @ w)
res = w + DB.T @ nu
print('   nu =', np.array2string(nu, precision=9))
print('   |w + DB^T nu|inf = %.3e  ;  |w|inf = %.3e  ;  relative %.3e'
      % (float(np.abs(res).max()), float(np.abs(w).max()), float(np.abs(res).max() / np.abs(w).max())))
print('   |w|inf (dR + sum mu dF) = %.6f ; components:' % float(np.abs(w).max()))
print('     ', np.array2string(w, precision=6, max_line_width=200))
# naive check: forgetting the explicit dR scale term (mu dF only) -> does it stay in rowspace(DB)?
w_naive = np.zeros(12)
for i in range(5):
    w_naive = w_naive + mu[i] * DF[i]
nu_n = -np.linalg.solve(DB @ DB.T, DB @ w_naive)
print('   [scale-term control] without dR: |w_naive + DB^T nu|inf = %.3e (relative %.3e)'
      % (float(np.abs(w_naive + DB.T @ nu_n).max()), float(np.abs(w_naive + DB.T @ nu_n).max() / np.abs(w_naive).max())))

# conversion factors (positive branch factors)
print()
print('=== positive branch factors (interior) ===')
for i, (kind, k, l) in enumerate(CONTACTS):
    gg = tc_geo(u0)
    if kind == 'fan':
        P, Q, Hh = gg['C'][k], gg['C'][(k + 1) % 9], gg['hubs'][l]
        U = gg['U'][k]
    else:
        P, Q, Hh = gg['hubs'][0], gg['hubs'][1], gg['C'][6]
        U = gg['waist']
    c = mp.sqrt(norm2(sub(Q, P)))
    e1 = ((Q[0] - P[0]) / c, (Q[1] - P[1]) / c); e2 = (-e1[1], e1[0])
    yv = (Hh[0] - P[0]) * e2[0] + (Hh[1] - P[1]) * e2[1]
    vv = (U[0] - P[0]) * e2[0] + (U[1] - P[1]) * e2[1]
    uu = mp.sqrt(gg['R'] ** 2 - c * c / 4)
    Fout = norm2(sub(Hh, (2 * ((P[0] + Q[0]) / 2) - U[0], 2 * ((P[1] + Q[1]) / 2) - U[1]))) - gg['R'] ** 2
    Fin = norm2(sub(Hh, U)) - gg['R'] ** 2
    print('   contact %d (%s k=%d): y=%.6f u=%.6f  y/u=%.9f  4y^2/Fout=%.9f  Fin=%+.1e Fout=%.6f'
          % (i, kind, k, yv, uu, yv / uu, 4 * yv * yv / Fout, Fin, Fout))
print()
print('=== boundary radial partials (lead formulas: a_rho>0, a_R>0, g_R<0) ===')
gg, a_arr, delta_arr, th = gaps(x0)
for k in range(5):
    C, hubs_, R = unpack(x0)
    rho = mp.sqrt(norm2(C[k])); ak = a_arr[k]
    a_rho = (1 - R * R - rho * rho) / (2 * rho * rho * mp.sin(ak))
    a_R = R / (rho * mp.sin(ak))
    print('   k=%d rho=%.6f a=%.6f  a_rho=%+.6f  a_R=%+.6f' % (k, rho, ak, a_rho, a_R))

# ------------------------------------------------------------------ reflection lift to R^23
print()
print('=== full physical space R^23 (22 center coords + R) ===')
FULL_CONTACTS = [('fan', 1, 1), ('fan', 6, 1), ('fan', 2, 0), ('fan', 5, 0), ('fan', 3, 0),
                 ('fan', 4, 0), ('fan', 8, 1), ('central', 6, 0), ('central', 2, 0)]
# invariant extension: divide the multiplier equally among the members of the orbit
# (lead's reflection lift).  Orbit sizes: 2,2,2,2,2,1,2,1.
weights = [mu[0] / 2, mu[0] / 2, mu[1] / 2, mu[1] / 2, mu[2] / 2, mu[2] / 2, mu[3], mu[4] / 2, mu[4] / 2]
nu_full = [nu[0] / 2, nu[0] / 2, nu[1] / 2, nu[1] / 2, nu[2] / 2, nu[2] / 2, nu[3] / 2, nu[3] / 2, nu[4]]


def unpack23(z):
    C = [(z[2 * i], z[2 * i + 1]) for i in range(11)]
    return C[:9], [C[9], C[10]], z[22]


def gaps23(z):
    C, hubs, R = unpack23(z)
    th = [mp.atan2(C[k][1], C[k][0]) for k in range(9)]
    delta = [th[i + 1] - th[i] for i in range(8)] + [th[0] + 2 * mp.pi - th[8]]
    a = [mp.acos((norm2(C[k]) + 1 - R * R) / (2 * mp.sqrt(norm2(C[k])))) for k in range(9)]
    return [delta[i] - a[i] - a[(i + 1) % 9] for i in range(9)]


def pin23(z, k):
    C, hubs, R = unpack23(z)
    P, Q = C[k], C[(k + 1) % 9]
    d = sub(Q, P); c = mp.sqrt(norm2(d))
    M = ((P[0] + Q[0]) / 2, (P[1] + Q[1]) / 2)
    n = (-d[1] / c, d[0] / c)
    hh = mp.sqrt(R * R - c * c / 4)
    A = (M[0] + hh * n[0], M[1] + hh * n[1]); B = (M[0] - hh * n[0], M[1] - hh * n[1])
    return A if norm2(A) < norm2(B) else B


def F23(z, kind, k, l):
    C, hubs, R = unpack23(z)
    if kind == 'fan':
        P = pin23(z, k)
        return mp.sqrt(norm2(sub(P, hubs[l]))) - R
    m_ = (hubs[0][0] + hubs[1][0]) / 2; d_ = (hubs[1][0] - hubs[0][0]) / 2
    W = (m_, mp.sqrt(R * R - d_ * d_)) if k == 6 else (m_, -mp.sqrt(R * R - d_ * d_))
    return mp.sqrt(norm2(sub(W, C[k]))) - R


z0 = []
for k in range(9):
    z0 += [C0[k][0], C0[k][1]]
z0 += [hubs0[0][0], hubs0[0][1], hubs0[1][0], hubs0[1][1]]
z0 += [R0]
GAP_ORDER = [0, 7, 1, 6, 2, 5, 3, 4, 8]
w23 = np.zeros(23); w23[22] = 1.0


def grad23(fun):
    out = []
    for j in range(23):
        zp = list(z0); zm = list(z0); zp[j] = zp[j] + H; zm[j] = zm[j] - H
        out.append((fun(zp) - fun(zm)) / (2 * H))
    return out


for idx, (kind, k, l) in enumerate(FULL_CONTACTS):
    w23 = w23 + float(weights[idx]) * np.array([float(v) for v in grad23(lambda z, kk=k, ll=l, kd=kind: F23(z, kd, kk, ll))])
for idx, gi in enumerate(GAP_ORDER):
    w23 = w23 + float(nu_full[idx]) * np.array([float(v) for v in grad23(lambda z, ii=gi: gaps23(z)[ii])])
print('   |e_R + sum mu dF + sum nu dg|inf over R^23 = %.3e   (reflection lift; |e_R|=1)'
      % float(np.abs(w23).max()))
# antisymmetric block must vanish separately: project on the reflection-antisymmetric directions
anti = []
for i in range(9):
    v = np.zeros(23); v[2 * i + 1] = 1.0; v[2 * (8 - i) + 1] = -1.0
    anti.append(v / np.sqrt(2))
for i in (9, 10):
    v = np.zeros(23); v[2 * i + 1] = 1.0
    anti.append(v)
anti = np.array(anti)
print('   antisymmetric part of the lifted covector: |A^T w23|inf = %.3e (dim %d)'
      % (float(np.abs(anti @ w23).max()), anti.shape[0]))

# ------------------------------------------------------------------ branch-form covering KKT
# On the constraint manifold {F=0,g=0} the objective max_f gamma_f equals the coordinate R, and
#   grad F_i = c_i (grad gamma_i - e_R)  with c_i = Fout_i/(4 y_i^2) > 0  (lead's conversion)
# so   sum_i mu_i grad F_i = sum_i mu_i c_i grad gamma_i - s e_R ,   s = sum_i mu_i c_i.
# Adding e_R + sum mu grad F + sum nu grad g = 0 gives the BRANCH-FORM certificate
#   sum_i (mu_i c_i) grad gamma_i + (1-s) e_R + sum_j nu_j grad g_j = 0 ,
# with all branch weights positive iff s<1 (the switch branches have grad gamma_sw = e_R).
print()
print('=== branch-form certificate: sum (mu_i c_i) grad gamma_i + (1-s) e_R + sum nu_j grad g_j = 0 ===')
HC = mp.mpf('1e-16')
def grad12h(fun):
    out = []
    for j in range(12):
        xp = list(x0); xm = list(x0); xp[j] = xp[j] + HC; xm[j] = xm[j] - HC
        out.append((fun(xp) - fun(xm)) / (2 * HC))
    return [float(v) for v in out]


def circum(x, kind, k, l=0):
    C, hubs, R = unpack(x)
    if kind == 'fan':
        A, B, Hh = C[k], C[(k + 1) % 9], hubs[l]
    else:
        A, B, Hh = hubs[0], hubs[1], C[k]
    la = mp.sqrt(norm2(sub(B, Hh))); lb = mp.sqrt(norm2(sub(A, Hh))); lc = mp.sqrt(norm2(sub(B, A)))
    s_ = (la + lb + lc) / 2
    area = mp.sqrt(s_ * (s_ - la) * (s_ - lb) * (s_ - lc))
    return la * lb * lc / (4 * area)


def conversion(kind, k, l=0):
    """c = Fout/(4 y^2) > 0 for the representative contact (third vertex on the pin side)."""
    C, hubs, R = unpack(x0)
    if kind == 'fan':
        P, Q, Hh = C[k], C[(k + 1) % 9], hubs[l]
        U = pin(x0, k, Hh)
    else:
        P, Q, Hh = hubs[0], hubs[1], C[k]
        U = pin_pair(P, Q, Hh, R)
    c = mp.sqrt(norm2(sub(Q, P)))
    e1 = ((Q[0] - P[0]) / c, (Q[1] - P[1]) / c); e2 = (-e1[1], e1[0])
    yv = (Hh[0] - P[0]) * e2[0] + (Hh[1] - P[1]) * e2[1]
    Uout = (2 * ((P[0] + Q[0]) / 2) - U[0], 2 * ((P[1] + Q[1]) / 2) - U[1])
    Fout = norm2(sub(Hh, Uout)) - R * R
    return float(4 * yv * yv / Fout), float(Fout), float(yv)


cert = np.zeros(12)
s_sum = 0.0
weights_face = []
for idx, (kind, k, l) in enumerate(CONTACTS):
    cc, Fout, yv = conversion(kind, k, l)
    ci = float(mu[idx]) * cc
    weights_face.append(ci)
    s_sum += ci
    g_face = np.array(grad12h(lambda x, kk=k, ll=l, kd=kind: circum(x, kd, kk, ll)))
    cert = cert + ci * g_face
cert = cert + (1.0 - s_sum) * np.array([0.0] * 11 + [1.0])          # switch branches: grad gamma = e_R
for j in range(5):
    gj = np.array(grad12h(lambda x, ii=j: Gvec(x)[ii]))
    cert = cert + float(nu[j]) * gj
print('   face branch weights mu_i c_i =', ['%.9f' % v for v in weights_face], ' sum s = %.12f' % s_sum)
print('   switch-total weight 1-s = %.12f   (>0 required for a convex certificate)' % (1 - s_sum))
print('   |certificate|inf = %.3e   (branch-form covering KKT in the 12D symmetric physical space)'
      % float(np.abs(cert).max()))

out = dict(scope='physical symmetric 12D boundary chart + nu calibration at the TC root box; evaluation only, '
                 'numeric calibration (60-digit FD), no exactness claim',
           x0=[float(v) for v in x0], mu=mu.tolist(), nu=nu.tolist(), w=w.tolist(),
           residual_inf=float(np.abs(res).max()), residual_rel=float(np.abs(res).max() / np.abs(w).max()),
           naive_without_dR_relative=float(np.abs(w_naive + DB.T @ nu_n).max() / np.abs(w_naive).max()),
           DB_rank=int(np.linalg.matrix_rank(DB, tol=1e-9)), DF_sv=np.linalg.svd(DF, compute_uv=False).tolist(),
           DB_dXdu_inf=float(np.abs(DB @ dXdu).max()),
           full23_residual_inf=float(np.abs(w23).max()), full23_antisym_inf=float(np.abs(anti @ w23).max()))
(OUT / 'phase6_boundary_nu.json').write_text(json.dumps(out, indent=2))
print('[done] -> out/phase6_boundary_nu.json')
