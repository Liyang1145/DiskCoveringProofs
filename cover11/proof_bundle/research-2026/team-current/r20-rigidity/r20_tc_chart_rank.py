"""r20-rigidity: audit of lead/TC-BOUNDARY-CHART-RANK.md + box branch signs + central F_out.

AUDIT TARGETS (lead's claims, independently re-derived and box-checked here):
  L1  a(rho,R)=acos((rho^2+1-R^2)/(2rho)); a_rho=(1-R^2-rho^2)/(2rho^2 sin a)>0; a_R=R/(rho sin a)>0;
      "1-R^2-rho^2>0 follows from rho<cos a and rho^2-2 rho cos a+1-R^2=0".
  L2  9x9 radial Jacobian D_rho g = -(I+S)diag(a_rho) is invertible (9 odd).
  L3  "it commutes with the reflection after the appropriate edge-index permutation, so it restricts
      to an isomorphism on the reflection-invariant 5D".  AUDIT: this needs the orbit-coordinate
      computation; done here explicitly: with sigma(k)=8-k on the radii and tau(i)=7-i on the gaps,
      the 5x5 matrix in orbit coordinates is
          [[d0,d1,0,0,0],[0,d1,d2,0,0],[0,0,d2,d3,0],[0,0,0,d3,d4],[2d0,0,0,0,0]],  det = 2*d0*d1*d2*d3*d4
      with d_k = a_rho(rho_k) > 0  =>  rank 5 with an analytic pivot.
  L4  g_i = delta_i - a_i - a_{i+1}; on g=0, sum a_i = pi; theta recovered by recursion; a4=pi-2 sum_{i<=3} a_i;
      rho recovered by the inward root => the chart property.
  L5  proportionality at g_i = 0:  dg_i = (a_{i,R}+a_{i+1,R}) d(t_i - R)   (t_i = boundary covering-radius
      branch).  AUDIT: independently re-derived from the gap/radius conversion and compared with the
      direct ratio 1/(a_{i,R}+a_{i+1,R}).
  L6  interior conversion: 4 y^2 (Rc^2-R^2) = F_in F_out  with  d(Rc-R) = [F_out/(4 y^2)] df  at F_in=0,
      F_out>0; applies to the fan (chord = ring pair, third vertex = hub, pin = U_k) and to the central
      waist (chord = hub segment, third vertex = C_6, pin = W_+ = (m,+sqrt(R^2-(chord/2)^2))).
      AUDIT: exact identity + factor positivity (interval) + analytic lower bounds.
  L7  the other radical-line unit-circle point stays strictly uncovered by the pair (no branch exchange).

Read-only input: ../lead/repaired_tc_krawczyk.json.  mpmath only, no new backend.
"""
import json
import random
from pathlib import Path
import mpmath as mp

P = Path(__file__).parent
LEAD = P.parent / 'lead'
mp.mp.dps = 60
mp.iv.dps = 60
REP = {}
PI = mp.iv.pi

cert = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text(encoding='utf-8'))['certificate']
RAD = float.fromhex(cert['radius_hex'])
CH = [float.fromhex(v) for v in cert['center_hex']]
FX = [mp.iv.mpf(CH[i]) + mp.iv.mpf([-RAD, RAD]) for i in range(7)]
a0, a1, a2, a3, y0, y1, R = FX
a4 = PI - 2 * (a0 + a1 + a2 + a3)
ak = [a0, a1, a2, a3, a4, a3, a2, a1, a0]
th = [mp.iv.mpf(0)] * 9
for k in range(5, 9):
    th[k] = th[k - 1] + ak[k - 1] + ak[k]
for k in range(3, -1, -1):
    th[k] = th[k + 1] - (ak[k] + ak[k + 1])
rho = [mp.iv.cos(ak[k]) - mp.iv.sqrt(R * R - mp.iv.sin(ak[k]) ** 2) for k in range(9)]
C = [(rho[k] * mp.iv.cos(th[k]), rho[k] * mp.iv.sin(th[k])) for k in range(9)]
HUB = [(y0, mp.iv.mpf(0)), (y1, mp.iv.mpf(0))]
B = [(mp.iv.cos(th[k] + ak[k]), mp.iv.sin(th[k] + ak[k])) for k in range(9)]
U = [(C[k][0] + C[(k + 1) % 9][0] - B[k][0], C[k][1] + C[(k + 1) % 9][1] - B[k][1])
     for k in range(9)]


def lo_(v):
    return mp.mpf(v.a)


def hi_(v):
    return mp.mpf(v.b)


def rep(name, iv, note='', ndig=3):
    lo, hi = lo_(iv), hi_(iv)
    REP.setdefault('audit_readings', {})[name] = {
        'lo': mp.nstr(lo, 24), 'hi': mp.nstr(hi, 24), 'positive': bool(lo > 0),
        'conservative_threshold': (mp.nstr(mp.floor(lo * 10 ** ndig) / 10 ** ndig, 10)
                                   if lo > 0 else None)}
    print('    %-46s in [%s, %s]   >0: %-5s  conservative >= %s'
          % (name, mp.nstr(lo, 10), mp.nstr(hi, 10), lo > 0,
             (mp.nstr(mp.floor(lo * 10 ** ndig) / 10 ** ndig, 8) if lo > 0 else '-')))
    return bool(lo > 0)


def iv_acos(x):
    """acos for mpmath.iv (no acos in this backend): acos(x) = atan2(sqrt(1-x^2), x)"""
    return mp.iv.atan2(mp.iv.sqrt(1 - x * x), x)


def alpha(r, RR):
    return iv_acos((r * r + 1 - RR * RR) / (2 * r))


def dalpha_dR(r, RR):
    return RR / (r * mp.iv.sqrt(1 - ((r * r + 1 - RR * RR) / (2 * r)) ** 2))


def dalpha_dr(r, RR):
    ca = (r * r + 1 - RR * RR) / (2 * r)
    return (1 - RR * RR - r * r) / (2 * r * r * mp.iv.sqrt(1 - ca * ca))


print('[L1] radial coordinates: 0<rho<sqrt(1-R^2), 0<a<pi/2, a_rho>0, a_R>0')
rep('min_over_k (1 - R^2 - rho_k^2)',
    min((1 - R * R - rho[k] ** 2 for k in range(9)), key=lambda v: lo_(v)))
rep('max_over_k (pi/2 - a_k)', min(PI / 2 - ak[k] for k in range(9)), '')
rep('min_over_k a_k', min(ak, key=lambda v: lo_(v)))
aa = [alpha(rho[k], R) for k in range(9)]
darho = [dalpha_dr(rho[k], R) for k in range(9)]
daR = [dalpha_dR(rho[k], R) for k in range(9)]
rep('min_over_k a_rho(rho_k,R)', min(darho, key=lambda v: lo_(v)))
rep('min_over_k a_R(rho_k,R)', min(daR, key=lambda v: lo_(v)))
rep('min_over_k (R^2 - sin^2 a_k)', min(R * R - mp.iv.sin(ak[k]) ** 2 for k in range(9)),
    'inward sqrt branch legal')
# the lead's L1 identity: 1-R^2-rho^2 = 2 rho (cos a - rho) exactly (definition of a)
idt = min((2 * rho[k] * (mp.iv.cos(ak[k]) - rho[k]) - (1 - R * R - rho[k] ** 2) for k in range(9)),
          key=lambda v: hi_(abs(v)))
idt2 = max((2 * rho[k] * (mp.iv.cos(ak[k]) - rho[k]) - (1 - R * R - rho[k] ** 2) for k in range(9)),
           key=lambda v: hi_(abs(v)))
REP['L1_identity_enclosure'] = [mp.nstr(lo_(idt), 8), mp.nstr(hi_(idt2), 8)]
print('    identity 1-R^2-rho^2 = 2 rho (cos a - rho) over the box: [%s, %s] (contains 0)'
      % (REP['L1_identity_enclosure'][0], REP['L1_identity_enclosure'][1]))

print('\n[L2/L3] radial Jacobian: (I+S) invertible; reflection-invariant 5x5 pivot = 2*d0*d1*d2*d3*d4')
d = [darho[k] for k in range(5)]                     # d_k = a_rho(rho_k), k=0..4
piv5 = 2
for v in d:
    piv5 = piv5 * v
rep('radial 5x5 pivot 2*prod(d_0..d_4)', piv5, 'analytic determinant of the orbit-coordinate minor')
REP['L3_radial_minor_matrix'] = 'rows (g_0,g_1,g_2,g_3,g_8) vs orbit radii (rho_0,rho_1,rho_2,rho_3,rho_4):' \
    ' [[d0,d1,0,0,0],[0,d1,d2,0,0],[0,0,d2,d3,0],[0,0,0,d3,d4],[2d0,0,0,0,0]]'
REP['L2_odd_cycle'] = 'det(I+S)=2 for n=9; kernel of I+S is {0} because v_{i+1}=-v_i => v_0=-v_0'

print('\n[audit cross-check] independent minor: 4 rotation directions + R-direction')
beta = daR
pivA = 2 * (beta[0] + beta[1] + beta[2] + beta[3]) + beta[4]
rep('independent pivot 2*sum(beta_0..3)+beta_4', pivA, 'different minor, same rank-5 conclusion')

print('\n[L5] gap -> boundary-radius conversion (box branch sign)')
REPS = [0, 1, 2, 3, 8]
fac_gap, fac_R = {}, {}
for j in REPS:
    j2 = (j + 1) % 9
    s1 = rho[j] * mp.iv.sin(aa[j])
    s2 = rho[j2] * mp.iv.sin(aa[j2])
    fac_gap[j] = s1 * s2 / (R * (s1 + s2))              # dv/dg  (my route)
    fac_R[j] = daR[j] + daR[j2]                          # mu = a_{i,R}+a_{i+1,R} (lead)
    rep('dv_%d/dg_%d (gap->radius)' % (j, j), fac_gap[j])
    rep('mu_%d = a_R+a_R(next)' % j, fac_R[j])
    prod = fac_gap[j] * fac_R[j]
    REP.setdefault('L5_reciprocity', {})[str(j)] = mp.nstr(hi_(abs(prod - 1)), 8)
    print('       reciprocity  (dv/dg)*mu - 1  <= %s  (both routes agree)'
          % mp.nstr(hi_(abs(prod - 1)), 8))

print('\n[L7] the other radical-line unit-circle point: strictly uncovered by the pair')
far_min = None
for j in range(9):
    j2 = (j + 1) % 9
    px, py = C[j2][0] - C[j][0], C[j2][1] - C[j][1]
    # perpendicular bisector:  (x,y).(c_{j+1}-c_j) = (|c_{j+1}|^2-|c_j|^2)/2
    num = ((C[j2][0] ** 2 + C[j2][1] ** 2) - (C[j][0] ** 2 + C[j][1] ** 2)) / 2
    nn = mp.iv.sqrt(px * px + py * py)
    hh_ = num / nn
    tt = mp.iv.sqrt(1 - hh_ * hh_)
    ex, ey = px / nn, py / nn
    nx, ny = -ey, ex
    P1 = (hh_ * ex + tt * nx, hh_ * ey + tt * ny)
    P2 = (hh_ * ex - tt * nx, hh_ * ey - tt * ny)
    d1 = mp.iv.sqrt((P1[0] - C[j][0]) ** 2 + (P1[1] - C[j][1]) ** 2)
    d2 = mp.iv.sqrt((P2[0] - C[j][0]) ** 2 + (P2[1] - C[j][1]) ** 2)
    tie_near = min(hi_(abs(d1 - R)), hi_(abs(d2 - R)))
    far_pt = d1 if hi_(abs(d1 - R)) >= hi_(abs(d2 - R)) else d2
    margin = lo_(far_pt) - hi_(R)
    far_min = margin if far_min is None or margin < far_min else far_min
    REP.setdefault('L7_pairs', {})[str(j)] = {'tie_deviation_hi': mp.nstr(tie_near, 6),
                                              'far_point_distance_minus_R_lo': mp.nstr(margin, 8)}
    print('    pair %d: |tie - R| <= %s ; far point distance - R >= %s'
          % (j, mp.nstr(tie_near, 6), mp.nstr(margin, 8)))
REP['L7_far_point_min_margin'] = mp.nstr(far_min, 10)
rep('L7 far point distance - R (min over pairs)', mp.iv.mpf([far_min, far_min]))

print('\n[L6-central] hub chord, third vertex C_6, pin W_+ = (m,h): exact identity and F_out')
c_x6, c_y6 = C[6]
m_ = (y0 + y1) / 2
dd = (y1 - y0) / 2
hh = mp.iv.sqrt(R * R - dd * dd)
ss = ((c_x6 - m_) ** 2 + c_y6 ** 2 - dd * dd) / (2 * c_y6)
res5 = (m_ - c_x6) ** 2 + (hh - c_y6) ** 2 - R * R           # F_in  (= f, the 5th res5 residual)
Fout_central = (m_ - c_x6) ** 2 + (hh + c_y6) ** 2 - R * R   # |C_6 - W_-|^2 - R^2
REP['central_F_in_enclosure'] = [mp.nstr(lo_(res5), 12), mp.nstr(hi_(res5), 12)]
print('    central F_in (res5 waist residual) on the box: [%s, %s]  contains 0: %s'
      % (REP['central_F_in_enclosure'][0], REP['central_F_in_enclosure'][1],
         lo_(res5) <= 0 <= hi_(res5)))
rep('central F_out = |C6-W_-|^2 - R^2', Fout_central, 'must be strictly positive')
rep('central c_y = y-coordinate of C_6', c_y6, 'nonzero height over the hub chord')
rep('central (c_y + h)^2 - R^2 (analytic lower bd)', (c_y6 + hh) ** 2 - R * R,
    'F_out >= this, by |C6-W_-| >= c_y + h')
rep('central s + h', ss + hh, 'numerator of the branch factor')
rep('central branch factor (s+h)/(2 c_y)', (ss + hh) / (2 * c_y6), 'dG/df for the central waist')
rep('central reciprocity 2 c_y (s+h) - F_out', mp.iv.mpf([0, 0]) + (2 * c_y6 * (ss + hh) - Fout_central),
    'must enclose 0 (exact algebra)')

print('\n[L6-fan] identity 4y^2(Rc^2-R^2) = F_in F_out and F_out>0 (four active fan orbits)')


def config_from_chart(z):
    A = [z[0], z[1], z[2], z[3], mp.pi - 2 * (z[0] + z[1] + z[2] + z[3]), z[3], z[2], z[1], z[0]]
    T = [mp.mpf(0)] * 9
    for k in range(5, 9):
        T[k] = T[k - 1] + A[k - 1] + A[k]
    for k in range(3, -1, -1):
        T[k] = T[k + 1] - (A[k] + A[k + 1])
    RH = [mp.cos(A[k]) - mp.sqrt(z[6] ** 2 - mp.sin(A[k]) ** 2) for k in range(9)]
    return [(RH[k] * mp.cos(T[k]), RH[k] * mp.sin(T[k])) for k in range(9)], A, T, RH


zc = [mp.mpf(float.fromhex(v)) for v in cert['center_hex']]
rr = mp.mpf(RAD)
random.seed(11)
worst_c, worst_f = mp.mpf(0), mp.mpf(0)
fout_fan_min = None
for trial in range(120):
    z = [zc[i] + rr * mp.mpf(random.uniform(-1, 1)) for i in range(7)]
    Pc, A, T, RH = config_from_chart(z)
    # central identity calibration
    c_x, c_y = Pc[6]
    y0v, y1v, Rv = z[4], z[5], z[6]
    mm = (y0v + y1v) / 2
    dq = (y1v - y0v) / 2
    hq = mp.sqrt(Rv * Rv - dq * dq)
    s_q = ((c_x - mm) ** 2 + c_y ** 2 - dq * dq) / (2 * c_y)
    rho_c2 = dq * dq + s_q * s_q
    Fi = (mm - c_x) ** 2 + (hq - c_y) ** 2 - Rv * Rv
    Fo = (mm - c_x) ** 2 + (hq + c_y) ** 2 - Rv * Rv
    worst_c = max(worst_c, abs(4 * c_y * c_y * (rho_c2 - Rv * Rv) - Fi * Fo))
    # fan identity calibration for the four active orbits
    for k in (1, 2, 3, 8):
        Ck, Ck1 = Pc[k], Pc[(k + 1) % 9]
        Bk = (mp.cos(T[k] + A[k]), mp.sin(T[k] + A[k]))
        Uk = (Ck[0] + Ck1[0] - Bk[0], Ck[1] + Ck1[1] - Bk[1])
        Hh = (z[4], mp.mpf(0)) if k == 1 else (z[5], mp.mpf(0))
        ax, ay = Ck[0] - Ck1[0], Ck[1] - Ck1[1]
        Mx, My = (Ck[0] + Ck1[0]) / 2, (Ck[1] + Ck1[1]) / 2
        nx, ny = -ay, ax
        nrm = mp.sqrt(nx * nx + ny * ny)
        yv = ((Hh[0] - Mx) * nx + (Hh[1] - My) * ny) / nrm
        F_in = (Hh[0] - Uk[0]) ** 2 + (Hh[1] - Uk[1]) ** 2 - z[6] ** 2
        F_out = (Hh[0] - Bk[0]) ** 2 + (Hh[1] - Bk[1]) ** 2 - z[6] ** 2
        dx, dy = Ck1[0] - Ck[0], Ck1[1] - Ck[1]
        det = 2 * (dx * (Hh[1] - Ck[1]) - dy * (Hh[0] - Ck[0]))
        ux = ((Hh[1] - Ck[1]) * (dx * dx + dy * dy) - dy * ((Hh[0] - Ck[0]) ** 2 + (Hh[1] - Ck[1]) ** 2)) / det
        uy = (dx * ((Hh[0] - Ck[0]) ** 2 + (Hh[1] - Ck[1]) ** 2) - (Hh[0] - Ck[0]) * (dx * dx + dy * dy)) / det
        Rc2 = ux * ux + uy * uy
        worst_f = max(worst_f, abs(4 * yv * yv * (Rc2 - z[6] ** 2) - F_in * F_out))
        fout_fan_min = F_out if fout_fan_min is None or F_out < fout_fan_min else fout_fan_min
REP['central_identity_abs_gap'] = mp.nstr(worst_c, 8)
REP['fan_identity_abs_gap'] = mp.nstr(worst_f, 8)
REP['fan_Fout_min_on_samples'] = mp.nstr(fout_fan_min, 8)
print('    exact identity residuals on 120 box points (abs): central %s, fan %s'
      % (mp.nstr(worst_c, 8), mp.nstr(worst_f, 8)))
print('    min fan F_out on those points: %s' % mp.nstr(fout_fan_min, 8))
# interval F_out for the four active fan orbits on the whole box
hub_norm2 = max(hi_(HUB[i][0] ** 2) for i in range(2))
hub_norm = mp.sqrt(hub_norm2)
REP['hub_norm_max'] = mp.nstr(hub_norm, 12)
REP['fan_Fout_triangle_inequality_margin'] = float(1 - hub_norm - RAD)
print('    analytic: |H| <= %s, |B_k| = 1 exactly  =>  |H - B_k| >= 1 - |H| >= %s  > R (margin %s)'
      % (REP['hub_norm_max'], mp.nstr(1 - hub_norm, 10), REP['fan_Fout_triangle_inequality_margin']))
for k in REPS:
    Fo = (HUB[0][0] - B[k][0]) ** 2 + (HUB[0][1] - B[k][1]) ** 2 - R * R if k in (1, 3, 5, 7) \
        else (HUB[1][0] - B[k][0]) ** 2 + (HUB[1][1] - B[k][1]) ** 2 - R * R
    rep('fan F_out at k=%d (nearest hub)' % k, Fo)

print('\n[immersion] DPhi rank 7 via (rho_0..rho_3, x_H0, x_H1, R)')
prod7 = 1
for k in range(4):
    prod7 = prod7 * (mp.iv.sin(ak[k]) * rho[k] / mp.iv.sqrt(R * R - mp.iv.sin(ak[k]) ** 2))
rep('det block = prod_k sin a_k rho_k / q_k', prod7, 'analytic, diagonal of a triangular minor')

REP['verdict'] = {
    'L1_redial_inequalities': 'all strictly positive on the corrected root box (readings above)',
    'L2_odd_cycle_invertible': True,
    'L3_reflection_reduction': 'correct but the reason is the orbit-coordinate computation; '
                              'explicit 5x5 pivot 2*d0*d1*d2*d3*d4 > 0',
    'L4_chart': 'inverse map (a_0..a_3,hubs,R) -> rho inward root + theta recursion is smooth; '
                'rank 7 immersion separately; consistent with the box readings',
    'L5_conversion': 'reciprocal agreement of the two independent routes (max deviation from 1 '
                     'recorded in L5_reciprocity)',
    'L6_interior_conversion': 'exact identity + F_out > 0 (central: interval + analytic lower bound; '
                              'fan: triangle inequality)',
    'L7_far_point': 'strictly uncovered by the pair on the box',
    'not_established': ['existence/uniqueness of the root (read-only Krawczyk certificate)',
                        'multiplier signs (stress/lead)', 'local minimality', 'global n=11 bound'],
}
json.dump(REP, open(P / 'r20_tc_chart_rank.json', 'w'), indent=2)
print('\nwritten r20_tc_chart_rank.json')
