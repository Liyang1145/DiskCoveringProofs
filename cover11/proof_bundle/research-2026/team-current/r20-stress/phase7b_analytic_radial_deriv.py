"""Phase 7b: INDEPENDENT second representation of the radial derivatives used in phase 7.

The phase-7 certificate obtains  d f_c / d rho_j  by interval forward-mode AD.  Here the same
derivative is obtained twice more, at the exact box centre, in 60-digit arithmetic:

   (A) closed-form analytic chain rule for the genuine chord-circle pin:
         U = M + sgn h e2,  M=(P+Q)/2, e1 = (Q-P)/|Q-P|, e2 = rot90(e1), h = sqrt(R^2-|d|^2/4),
         dU/dP = 1/2 I + sgn[ (c/(4h)) e2 e1^T + h rot90(-I + e1 e1^T)/c ]
         dU/dQ = 1/2 I + sgn[-(c/(4h)) e2 e1^T + h rot90( I - e1 e1^T)/c ]
         df/dC_j = ghat . (dU/dC_j),  ghat = (U-third)/|U-third|
         df/drho_j = df/dC_j . Chat_j   (fan: j in chord endpoints; central: third vertex C_6)
   (B) central finite differences in rho_j (h = 1e-25, 60 digits, theta/hubs/R fixed)

Then (A) is checked for CONTAINMENT in the phase-7 interval enclosures (AD partials, v_j, c_k).
This is a different representation of the same kernel (analytic vs interval AD), not new physics.
Writes only in r20-stress/.
"""
import os, sys, json
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
from mpmath import mp, mpf

mp.dps = 60
W = Path(__file__).parent
OUT = W / 'out'
LEAD = W.parent / 'lead'

D = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text(encoding='utf-8'))
CD = D['certificate']
CEN = [float.fromhex(h) for h in CD['center_hex']]


def chart(rho=False):
    a04 = [mpf(CEN[k]) for k in range(4)]
    y0, y1, R = mpf(CEN[4]), mpf(CEN[5]), mpf(CEN[6])
    a4 = mp.pi - 2 * sum(a04)
    a = [a04[0], a04[1], a04[2], a04[3], a4, a04[3], a04[2], a04[1], a04[0]]
    rr = [mp.cos(a[k]) - mp.sqrt(R * R - mp.sin(a[k]) ** 2) for k in range(9)]
    th = [mpf(0)] * 9
    for k in range(5, 9):
        th[k] = th[k - 1] + a[k - 1] + a[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (a[k] + a[k + 1])
    return rr, th, y0, y1, R, a


RHO, TH, Y0, Y1, R0, A = chart()
LAM = [mpf(CEN[7 + i]) for i in range(5)]
MU = [-l for l in LAM]

CONTACTS = [('fan', 1, 1), ('fan', 6, 1), ('fan', 2, 0), ('fan', 5, 0), ('fan', 3, 0),
            ('fan', 4, 0), ('fan', 8, 1), ('central', 6, 0), ('central', 2, 0)]
ORBIT = {0: 0, 1: 0, 2: 1, 3: 1, 4: 2, 5: 2, 6: 3, 7: 4, 8: 4}
OSZ = {0: 2, 1: 2, 2: 2, 3: 1, 4: 2}


def C_of(rho, th):
    return [(rho[j] * mp.cos(th[j]), rho[j] * mp.sin(th[j])) for j in range(9)]


def parts(rho, th, kind, k, l):
    C = C_of(rho, th)
    HUB = [(Y0, mpf(0)), (Y1, mpf(0))]
    if kind == 'fan':
        P, Q, T = C[k], C[(k + 1) % 9], HUB[l]
    else:
        P, Q, T = HUB[0], HUB[1], C[k]
    d = (Q[0] - P[0], Q[1] - P[1])
    c = mp.sqrt(d[0] * d[0] + d[1] * d[1])
    M = ((P[0] + Q[0]) / 2, (P[1] + Q[1]) / 2)
    e1 = (d[0] / c, d[1] / c)
    e2 = (-e1[1], e1[0])
    h = mp.sqrt(R0 * R0 - c * c / 4)
    sgn = mpf(1) if (T[0] - M[0]) * e2[0] + (T[1] - M[1]) * e2[1] >= 0 else mpf(-1)
    U = (M[0] + sgn * h * e2[0], M[1] + sgn * h * e2[1])
    Uo = (M[0] - sgn * h * e2[0], M[1] - sgn * h * e2[1])
    return dict(C=C, HUB=HUB, P=P, Q=Q, T=T, c=c, e1=e1, e2=e2, h=h, sgn=sgn, U=U, Uo=Uo, M=M)


def f_of(rho, th, kind, k, l):
    p = parts(rho, th, kind, k, l)
    g = (p['U'][0] - p['T'][0], p['U'][1] - p['T'][1])
    return mp.sqrt(g[0] * g[0] + g[1] * g[1]) - R0


def analytic_derivs(kind, k, l):
    """df/drho_j (j=0..8) for one contact, closed form, at (RHO, TH, Y0, Y1, R0)."""
    p = parts(RHO, TH, kind, k, l)
    e1, e2, c, h, sgn, U, T = p['e1'], p['e2'], p['c'], p['h'], p['sgn'], p['U'], p['T']
    g = (U[0] - T[0], U[1] - T[1])
    L = mp.sqrt(g[0] * g[0] + g[1] * g[1])
    gh = (g[0] / L, g[1] / L)

    def matmul(Amat, v):
        return (Amat[0][0] * v[0] + Amat[0][1] * v[1], Amat[1][0] * v[0] + Amat[1][1] * v[1])

    I2 = [[mpf(1), mpf(0)], [mpf(0), mpf(1)]]
    R90 = [[mpf(0), mpf(-1)], [mpf(1), mpf(0)]]
    O = [[e2[0] * e1[0], e2[0] * e1[1]], [e2[1] * e1[0], e2[1] * e1[1]]]
    P1 = [[e1[0] * e1[0] - 1, e1[0] * e1[1]], [e1[1] * e1[0], e1[1] * e1[1] - 1]]   # -I + e1 e1^T
    P2 = [[1 - e1[0] * e1[0], -e1[0] * e1[1]], [-e1[1] * e1[0], 1 - e1[1] * e1[1]]]  #  I - e1 e1^T

    def mm(X, Y):
        return [[sum(X[i][t] * Y[t][j] for t in range(2)) for j in range(2)] for i in range(2)]

    def scal(s, X):
        return [[s * X[i][j] for j in range(2)] for i in range(2)]

    def add(X, Y):
        return [[X[i][j] + Y[i][j] for j in range(2)] for i in range(2)]

    dU_P = add(scal(mpf(1) / 2, I2), scal(sgn, add(scal(c / (4 * h), O), scal(h / c, mm(R90, P1)))))
    dU_Q = add(scal(mpf(1) / 2, I2), scal(sgn, add(scal(-c / (4 * h), O), scal(h / c, mm(R90, P2)))))
    out = [mpf(0)] * 9
    if kind == 'fan':
        out[k] = gh[0] * dU_P[0][0] * mp.cos(TH[k]) + gh[0] * dU_P[0][1] * mp.sin(TH[k]) \
            + gh[1] * dU_P[1][0] * mp.cos(TH[k]) + gh[1] * dU_P[1][1] * mp.sin(TH[k])
        j = (k + 1) % 9
        out[j] = gh[0] * dU_Q[0][0] * mp.cos(TH[j]) + gh[0] * dU_Q[0][1] * mp.sin(TH[j]) \
            + gh[1] * dU_Q[1][0] * mp.cos(TH[j]) + gh[1] * dU_Q[1][1] * mp.sin(TH[j])
    else:
        out[k] = -(gh[0] * mp.cos(TH[k]) + gh[1] * mp.sin(TH[k]))          # third vertex is C_k
    return out, p


def fd_derivs(kind, k, l, hstep=mpf('1e-25')):
    out = []
    for j in range(9):
        rp = list(RHO); rm = list(RHO)
        rp[j] += hstep; rm[j] -= hstep
        out.append((f_of(rp, TH, kind, k, l) - f_of(rm, TH, kind, k, l)) / (2 * hstep))
    return out


# ------------------------------------------------------------------ run
ANA = []
FD = []
for (kind, k, l) in CONTACTS:
    a_, p_ = analytic_derivs(kind, k, l)
    ANA.append(a_)
    FD.append(fd_derivs(kind, k, l))
dev = max(abs(ANA[i][j] - FD[i][j]) for i in range(9) for j in range(9))
print('[analytic vs FD @ centre] max |d f/d rho| deviation = %.3e' % float(dev))

# v_j from the analytic derivatives with the orbit-split mu
v_ana = []
for j in range(9):
    tot = mpf(0)
    for idx in range(9):
        tot += (MU[ORBIT[idx]] / OSZ[ORBIT[idx]]) * ANA[idx][j]
    v_ana.append(tot)

# conversion factors at the centre
CK_ANA = []
for idx in (0, 2, 4, 6, 7):
    kind, k, l = CONTACTS[idx]
    p = parts(RHO, TH, kind, k, l)
    yv = (p['T'][0] - p['M'][0]) * p['e2'][0] + (p['T'][1] - p['M'][1]) * p['e2'][1]
    Uo = p['Uo']
    Fout = (Uo[0] - p['T'][0]) ** 2 + (Uo[1] - p['T'][1]) ** 2 - R0 * R0
    CK_ANA.append(4 * yv * yv / Fout)

# ------------------------------------------------------------------ containment check vs phase 7 boxes
P7 = json.loads((OUT / 'phase7_interval_cyclic_nu.json').read_text(encoding='utf-8'))


def inside(ivl, val):
    return mpf(ivl[0]) <= val <= mpf(ivl[1])


contain = {}
contain['v_all_inside'] = all(inside(P7['v'][j], v_ana[j]) for j in range(9))
contain['v_max_margin'] = float(max(min(abs(v_ana[j] - mpf(P7['v'][j][0])), abs(mpf(P7['v'][j][1]) - v_ana[j]))
                                    for j in range(9)))
contain['ck_all_inside'] = all(inside(P7['ck'][i], CK_ANA[i]) for i in range(5))
contain['ck_max_margin'] = float(max(min(abs(CK_ANA[i] - mpf(P7['ck'][i][0])), abs(mpf(P7['ck'][i][1]) - CK_ANA[i]))
                                     for i in range(5)))
# phase7 nu intervals must contain the radially-consistent nu: solve (I+S)nu = v_ana/a' at the centre
APR = [mpf(P7['a_prime'][j][0]) for j in range(9)]     # interval endpoints only used as a locator
w_c = [v_ana[j] / ((1 - R0 * R0 - RHO[j] ** 2) / (2 * RHO[j] ** 2 * mp.sin(A[j]))) for j in range(9)]
nu_c = [sum(((-1) ** kk) * w_c[(j - kk) % 9] for kk in range(9)) / 2 for j in range(9)]
contain['nu_all_inside'] = all(inside(P7['nu'][j], nu_c[j]) for j in range(9))
contain['nu_max_margin'] = float(max(min(abs(nu_c[j] - mpf(P7['nu'][j][0])), abs(mpf(P7['nu'][j][1]) - nu_c[j]))
                                    for j in range(9)))
contain['nu_centre_values'] = [mp.nstr(x, 20) for x in nu_c]
contain['v_centre_values'] = [mp.nstr(x, 20) for x in v_ana]
contain['ck_centre_values'] = [mp.nstr(x, 20) for x in CK_ANA]

print('[analytic derivative table @ centre] rows = contacts, cols = rho_0..rho_8:')
for i, (kind, k, l) in enumerate(CONTACTS):
    print('   %-14s ' % ('%s(%d,%d)' % (kind, k, l)) + ' '.join('%+9.6f' % float(ANA[i][j]) for j in range(9)))
print('[containment in phase-7 interval AD boxes]')
for kk in sorted(contain):
    v = contain[kk]
    print('   %-22s %s' % (kk, ('%.3e' % v) if isinstance(v, float) else v))

out = dict(scope='independent analytic + FD representation of df/drho and containment in the phase-7 '
                 'interval enclosures; centre of the same lead box; 60-digit evaluation',
           contact_labels=['%s %d %d' % c for c in CONTACTS],
           analytic_derivs=[[mp.nstr(x, 25) for x in row] for row in ANA],
           fd_derivs=[[mp.nstr(x, 25) for x in row] for row in FD],
           analytic_vs_fd_maxdev=mp.nstr(dev, 6), v_centre=[mp.nstr(x, 25) for x in v_ana],
           ck_centre=[mp.nstr(x, 25) for x in CK_ANA], nu_centre=[mp.nstr(x, 25) for x in nu_c],
           containment=contain)
(OUT / 'phase7b_analytic_radial_deriv.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
print('[done] -> out/phase7b_analytic_radial_deriv.json')
