"""Phase 7: INTERVAL certificate for the odd-9 cyclic boundary-multiplier formula
at the lead's certified exact 12D TC root box.

READ-ONLY inputs
    ../lead/repaired_tc_krawczyk.json      (Krawczyk box: center_hex + radius_hex, 12 variables
                                            u = (a0,a1,a2,a3,y0,y1,R, lam0..lam4))
    out/phase6b_nu_explicit.json           (old 60-digit FD calibration, used only as a control)
    out/phase6_boundary_nu.json            (old 12D nu calibration, used only as a control)

WHAT THIS DOES (no root finding, no rank/SVD, no optimisation, no new start)
    On that box, and on the SAME object (the genuine physical chord-circle pin residuals):
      * chart map        a4 = pi - 2(a0+a1+a2+a3); rho_k = cos a_k - sqrt(R^2 - sin^2 a_k);
                         th_4 = 0, th_k = th_{k-1}+a_{k-1}+a_k (k>4), th_k = th_{k+1}-(a_k+a_{k+1}) (k<4)
      * interior pin     fan (k,l): chord C_k C_{k+1}, third vertex H_l ;
                         central   : chord H_0 H_1, third vertex C_6 ;
                         pin U = the radius-R circle intersection ON THE THIRD-VERTEX SIDE ;
                         f = |U - third| - R          (genuine chord-circle pin, not the unit tie)
      * multipliers      mu_i = -lam_i (i=0..4) taken DIRECTLY from the root box;
                         orbit split: paired faces get mu_i/2 each, self-reflected fan(8,H1) gets mu_3
      * radial axis      v_j = sum over the 9 contacts of mu_c * d f_c / d rho_j
                         (theta, hubs, R fixed) -> interval forward-mode AD, analytic chain rule
      * gap radial data  a'_j = (1-R^2-rho_j^2)/(2 rho_j^2 sin a_j) > 0 ,  a_{R,j} = R/(rho_j sin a_j) > 0
      * odd 9-cycle      v_j = a'_j (nu_j + nu_{j-1})  =>  w_j = v_j/a'_j ,
                         nu_j = (1/2) sum_{k=0..8} (-1)^k w_{j-k mod 9}   (9 odd => (I+S) invertible)
      * conversion       c_k = 4 y_k^2 / F_out,k  (>0)  (y = signed height of the third vertex over
                         the chord, F_out = |pout - third|^2 - R^2),  s = sum_i mu_i c_i
      * R-stationarity   (lead TC-TO-PHYSICAL-KKT-LIFT, exact at the root, used here as an identity
                         to be INTERVAL-CHECKED):  1 - s - sum_j nu_j (a_{R,j}+a_{R,j+1}) = 0
                         => s < 1 is NOT an independent premise: 1-s = the positive boundary total.

OUTPUT   intervals (not residuals): mu, nu, c_k, s, 1-s, boundary total, a', a_R, rho, y, F_out,
         all with explicit endpoints; plus the verdict flags.  Writes only in r20-stress/.
"""
import os, sys, json, time
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
from mpmath import mp, iv, mpf

mp.dps = 60
iv.dps = 35

W = Path(__file__).parent
OUT = W / 'out'
LEAD = W.parent / 'lead'

D = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text(encoding='utf-8'))
CD = D['certificate']
RAD = float.fromhex(CD['radius_hex'])
CEN = [float.fromhex(h) for h in CD['center_hex']]
assert len(CEN) == 12
BOX = [iv.mpf(c) + iv.mpf([-RAD, RAD]) for c in CEN]          # lead's construction, exact dyadic centre

def LO(x): return mpf(x.a)
def HI(x): return mpf(x.b)
def sLO(x, n=32): return mp.nstr(LO(x), n)
def sHI(x, n=32): return mp.nstr(HI(x), n)
def POS(x): return LO(x) > 0
def HOLD(x, v): return LO(x) <= v <= HI(x)
def pair(v): return [iv.mpf(a) for a in (v.a, v.b)]

# ------------------------------------------------------------------ interval forward AD (9 inputs: rho_j)
NIN = 9
ZIV = iv.mpf(0)
ONEIV = iv.mpf(1)


class IVD(object):
    """interval value + interval partials w.r.t. rho_0..rho_8"""
    __slots__ = ('v', 'd')

    def __init__(self, v, d):
        self.v = v
        self.d = d

    def __add__(self, o):
        if isinstance(o, IVD):
            return IVD(self.v + o.v, [a + b for a, b in zip(self.d, o.d)])
        return IVD(self.v + o, list(self.d))
    __radd__ = __add__

    def __sub__(self, o):
        if isinstance(o, IVD):
            return IVD(self.v - o.v, [a - b for a, b in zip(self.d, o.d)])
        return IVD(self.v - o, list(self.d))

    def __rsub__(self, o):
        return IVD(o - self.v, [-a for a in self.d])

    def __mul__(self, o):
        if isinstance(o, IVD):
            return IVD(self.v * o.v, [a * o.v + self.v * b for a, b in zip(self.d, o.d)])
        return IVD(self.v * o, [a * o for a in self.d])
    __rmul__ = __mul__

    def inv(self):
        w = 1 / self.v
        return IVD(w, [-a * w * w for a in self.d])

    def __truediv__(self, o):
        if isinstance(o, IVD):
            return self * o.inv()
        return IVD(self.v / o, [a / o for a in self.d])

    def __rtruediv__(self, o):
        return o * self.inv()

    def __neg__(self):
        return IVD(-self.v, [-a for a in self.d])


def cst(x):
    return IVD(x, [ZIV] * NIN)


def var(x, j):
    d = [ZIV] * NIN
    d[j] = ONEIV
    return IVD(x, d)


def isqrt(x):
    """interval sqrt with explicit domain check (never silently clamps)"""
    if not (LO(x.v) > 0):
        raise ValueError('isqrt: non-positive argument interval, lo=%s' % mp.nstr(LO(x.v), 8))
    s = iv.sqrt(x.v)
    return IVD(s, [a / (2 * s) for a in x.d])


# ------------------------------------------------------------------ chart map -> physical intervals
a04 = BOX[0:4]
y0, y1, R = BOX[4], BOX[5], BOX[6]
lam = BOX[7:12]
a4 = iv.pi - 2 * (a04[0] + a04[1] + a04[2] + a04[3])
A = [a04[0], a04[1], a04[2], a04[3], a4, a04[3], a04[2], a04[1], a04[0]]
SIN = [iv.sin(a) for a in A]
RAD2 = [R * R - s * s for s in SIN]                    # R^2 - sin^2 a_k  (must be > 0)
RHO = [iv.cos(A[k]) - iv.sqrt(RAD2[k]) for k in range(9)]
TH = [iv.mpf(0)] * 9
for k in range(5, 9):
    TH[k] = TH[k - 1] + A[k - 1] + A[k]
for k in range(3, -1, -1):
    TH[k] = TH[k + 1] - (A[k] + A[k + 1])

fails = []
for k in range(9):
    if not (LO(RAD2[k]) > 0):
        fails.append('R^2-sin^2 a_%d <= 0' % k)
    if not (LO(RHO[k]) > 0):
        fails.append('rho_%d <= 0' % k)
    if not (LO(A[k]) > 0 and HI(A[k]) < mp.pi / 2):
        fails.append('a_%d outside (0,pi/2)' % k)

# ------------------------------------------------------------------ physical coordinates on the box
CX = [var(RHO[j], j) * cst(iv.cos(TH[j])) for j in range(9)]
CY = [var(RHO[j], j) * cst(iv.sin(TH[j])) for j in range(9)]
HUB = [(cst(y0), cst(ZIV)), (cst(y1), cst(ZIV))]
Rc = cst(R)
HALF = cst(iv.mpf('0.5'))
FOURTH = cst(iv.mpf('0.25'))
ZERO = cst(ZIV)

CONTACTS = [('fan', 1, 1), ('fan', 6, 1), ('fan', 2, 0), ('fan', 5, 0), ('fan', 3, 0),
            ('fan', 4, 0), ('fan', 8, 1), ('central', 6, 0), ('central', 2, 0)]
ORBIT = {0: 0, 1: 0, 2: 1, 3: 1, 4: 2, 5: 2, 6: 3, 7: 4, 8: 4}   # contact index -> mu index
OSZ = {0: 2, 1: 2, 2: 2, 3: 1, 4: 2}                            # orbit size of each mu index
MU = [-lam[i] for i in range(5)]                                # mu_i = -lambda_i, straight from the box


def contact(kind, k, l):
    if kind == 'fan':
        P, Q, T = (CX[k], CY[k]), (CX[(k + 1) % 9], CY[(k + 1) % 9]), HUB[l]
    else:
        P, Q, T = HUB[0], HUB[1], (CX[k], CY[k])
    dx, dy = Q[0] - P[0], Q[1] - P[1]
    c2 = dx * dx + dy * dy
    c = isqrt(c2)
    Mx, My = (P[0] + Q[0]) * HALF, (P[1] + Q[1]) * HALF
    nx, ny = (ZERO - dy) / c, dx / c
    hh = isqrt(Rc * Rc - c2 * FOURTH)
    sx = (T[0] - Mx) * nx + (T[1] - My) * ny                     # signed height of the third vertex
    if LO(sx.v) > 0:
        sg = iv.mpf(1)
    elif HI(sx.v) < 0:
        sg = iv.mpf(-1)
    else:
        return None                                              # sign not decided on the box
    Ux, Uy = Mx + hh * sg * nx, My + hh * sg * ny                 # pin (third-vertex side)
    Bx, By = Mx - hh * sg * nx, My - hh * sg * ny                 # pout (other side)
    gx, gy = Ux - T[0], Uy - T[1]
    L = isqrt(gx * gx + gy * gy)
    f = L - Rc
    Fout = (Bx - T[0]) * (Bx - T[0]) + (By - T[1]) * (By - T[1]) - Rc * Rc
    return dict(f=f, y=sx, hh=hh, Fout=Fout, sgn=sg, Fin=(gx * gx + gy * gy) - Rc * Rc)


t0 = time.time()
C = []
for (kind, k, l) in CONTACTS:
    r = contact(kind, k, l)
    if r is None:
        fails.append('pin-side sign undecided for %s %s %s' % (kind, k, l))
    C.append(r)
print('[setup] %d contacts evaluated in %.1f s ; fails = %s' % (len(C), time.time() - t0, fails))

# ------------------------------------------------------------------ v_j = sum_c mu_c * df_c/drho_j
v = [ZIV for _ in range(9)]
for idx in range(9):
    mu_c = MU[ORBIT[idx]] / OSZ[ORBIT[idx]]
    for j in range(9):
        v[j] = v[j] + mu_c * C[idx]['f'].d[j]

# ------------------------------------------------------------------ a'_j, a_{R,j}, w_j, nu_j
SIN_A = SIN
APRIME = [(1 - R * R - RHO[j] * RHO[j]) / (2 * RHO[j] * RHO[j] * SIN_A[j]) for j in range(9)]
AR = [R / (RHO[j] * SIN_A[j]) for j in range(9)]
w = [v[j] / APRIME[j] for j in range(9)]
nu = [sum(((-1) ** k) * w[(j - k) % 9] for k in range(9)) / 2 for j in range(9)]

# conversions c_k for the five orbit representatives: contact indices 0,2,4,6 (fans 1,2,3,8) and 7 (central 6)
REP_IDX = [0, 2, 4, 6, 7]                                        # (fan1), (fan2), (fan3), (fan8), (central6)
CK = [4 * (C[i]['y'].v * C[i]['y'].v) / C[i]['Fout'].v for i in REP_IDX]
s_face = sum(MU[i] * CK[i] for i in range(5))                     # sum_i mu_i c_i
one_minus_s = 1 - s_face

# boundary total weight: full 9-gap form and symmetric-orbit form
bnd_gap = [nu[j] * (AR[j] + AR[(j + 1) % 9]) for j in range(9)]
bnd_tot = sum(bnd_gap)
nu_sym = [2 * nu[0], 2 * nu[1], 2 * nu[2], 2 * nu[3], nu[8]]      # symmetric-space (orbit-summed) nu
bnd_sym = sum(nu_sym[i] * (AR[o] + AR[(o + 1) % 9]) for i, o in enumerate([0, 1, 2, 3, 8]))

# radial-equation control: v_j = a'_j (nu_j + nu_{j-1}) must be consistent with the computed nu
radeq = [v[j] - APRIME[j] * (nu[j] + nu[(j - 1) % 9]) for j in range(9)]

# ------------------------------------------------------------------ verdicts
verdict = {}
verdict['mu_positive'] = all(POS(m) for m in MU)
verdict['nu_positive'] = all(POS(x) for x in nu)
verdict['nu_sym_positive'] = all(POS(x) for x in nu_sym)
verdict['aprime_positive'] = all(POS(x) for x in APRIME)
verdict['aR_positive'] = all(POS(x) for x in AR)
verdict['ck_positive'] = all(POS(x) for x in CK)
verdict['Fout_positive'] = all(POS(C[i]['Fout'].v) for i in range(9))
verdict['f_contains_zero'] = all(HOLD(C[i]['f'].v, mpf(0)) for i in range(9))
verdict['Fin_contains_zero'] = all(HOLD(C[i]['Fin'].v, mpf(0)) for i in range(9))
verdict['one_minus_s_positive'] = POS(one_minus_s)
verdict['bnd_total_positive'] = POS(bnd_tot)
verdict['R_stationarity_holds'] = (not (HI(one_minus_s) < LO(bnd_tot) or HI(bnd_tot) < LO(one_minus_s)))
verdict['R_stationarity_gap'] = mp.nstr(max(abs(LO(one_minus_s) - HI(bnd_tot)), abs(HI(one_minus_s) - LO(bnd_tot))), 8)
verdict['s_lt_1'] = HI(s_face) < 1 and POS(one_minus_s)
verdict['bnd_gap_eq_sym'] = (not (HI(bnd_tot) < LO(bnd_sym) or HI(bnd_sym) < LO(bnd_tot)))
verdict['weight_total_1'] = (not (HI(s_face + bnd_tot) < 1 or LO(s_face + bnd_tot) > 1))
verdict['weight_total_closure'] = mp.nstr(max(abs(HI(s_face + bnd_tot) - 1), abs(1 - LO(s_face + bnd_tot))), 8)
verdict['chart_consistency'] = all(
    not (HI(iv.cos(A[j])) < LO((RHO[j] ** 2 + 1 - R * R) / (2 * RHO[j])) or
         LO(iv.cos(A[j])) > HI((RHO[j] ** 2 + 1 - R * R) / (2 * RHO[j]))) for j in range(9))
verdict['radial_eq_residual_contains_zero'] = all(HOLD(radeq[j], mpf(0)) for j in range(9))
verdict['radial_eq_residual_max_abs'] = mp.nstr(max(max(abs(LO(x)), abs(HI(x))) for x in radeq), 8)
verdict['y_nonzero'] = all(min(abs(LO(C[i]['y'].v)), abs(HI(C[i]['y'].v))) > 0 for i in range(9))
verdict['chord_shorter_than_2R'] = all(POS(C[i]['hh'].v) for i in range(9))
verdict['pin_side_decided'] = all(r is not None for r in C)

# ------------------------------------------------------------------ controls against the old FD work
CTL = {}
try:
    O6 = json.loads((OUT / 'phase6b_nu_explicit.json').read_text(encoding='utf-8'))
    CTL['max|rho_fd - rho_iv@center|'] = max(abs(O6['rho'][j] - float(mp.mpf(0.5) * (LO(RHO[j]) + HI(RHO[j]))))
                                             for j in range(9))
    CTL['v_iv_vs_v_fd_maxdev'] = max(abs(float(mp.mpf(0.5) * (LO(v[j]) + HI(v[j]))) - O6['v'][j]) for j in range(9))
    CTL['nu_iv_vs_nu_fd_maxdev'] = max(abs(float(mp.mpf(0.5) * (LO(nu[j]) + HI(nu[j]))) - O6['nu_explicit'][j])
                                       for j in range(9))
    CTL['mu_iv_vs_mu_fd_maxdev'] = max(abs(float(mp.mpf(0.5) * (LO(MU[i]) + HI(MU[i]))) - O6['mu'][i]) for i in range(5))
except Exception as e:  # pragma: no cover
    CTL['phase6b_error'] = repr(e)
try:
    O6n = json.loads((OUT / 'phase6_boundary_nu.json').read_text(encoding='utf-8'))
    CTL['nu_sym_iv_vs_12D_maxdev'] = max(abs(float(mp.mpf(0.5) * (LO(nu_sym[i]) + HI(nu_sym[i]))) - O6n['nu'][i])
                                         for i in range(5))
except Exception as e:  # pragma: no cover
    CTL['phase6_error'] = repr(e)

# ------------------------------------------------------------------ print summary
print()
print('=== INTERVAL CERTIFICATE @ lead 12D TC root box (radius %.3e) ===' % RAD)
print('R          = [%s, %s]' % (sLO(R), sHI(R)))
print()
print('mu_i = -lam_i (orbit-representative multipliers, i=0..4):')
for i in range(5):
    print('   mu_%d = [%s, %s]   width %.2e   positive=%s' % (i, sLO(MU[i]), sHI(MU[i]),
                                                              float(HI(MU[i]) - LO(MU[i])), POS(MU[i])))
print()
print('c_k (conversion 4 y^2 / F_out, orbit representatives):')
for i in range(5):
    print('   c_%d  = [%s, %s]   F_out = [%s, %s]   y = [%s, %s]'
          % (i, sLO(CK[i]), sHI(CK[i]), sLO(C[REP_IDX[i]]['Fout'].v), sHI(C[REP_IDX[i]]['Fout'].v),
             sLO(C[REP_IDX[i]]['y'].v), sHI(C[REP_IDX[i]]['y'].v)))
print()
print('a\'_j = a_rho (radial gap derivative, must be > 0):')
for j in range(9):
    print('   a\'_%d = [%s, %s]     a_R,%d = [%s, %s]' % (j, sLO(APRIME[j]), sHI(APRIME[j]),
                                                          j, sLO(AR[j]), sHI(AR[j])))
print()
print('v_j = sum_c mu_c df_c/drho_j :')
for j in range(9):
    print('   v_%d = [%s, %s]' % (j, sLO(v[j]), sHI(v[j])))
print()
print('nu_j (odd-9 cyclic formula, per gap j = 0..8):')
for j in range(9):
    print('   nu_%d = [%s, %s]   positive=%s' % (j, sLO(nu[j]), sHI(nu[j]), POS(nu[j])))
print()
print('nu orbit-summed (symmetric-space multipliers, comparable with the 12D solve):')
for i in range(5):
    print('   nu^sym_%d = [%s, %s]' % (i, sLO(nu_sym[i]), sHI(nu_sym[i])))
print()
print('s = sum_i mu_i c_i   = [%s, %s]' % (sLO(s_face), sHI(s_face)))
print('1 - s                = [%s, %s]  positive=%s' % (sLO(one_minus_s), sHI(one_minus_s), POS(one_minus_s)))
print('boundary total (9 gaps, sum nu_j (a_R,j + a_R,j+1)) = [%s, %s]' % (sLO(bnd_tot), sHI(bnd_tot)))
print('boundary total (orbit form)                          = [%s, %s]' % (sLO(bnd_sym), sHI(bnd_sym)))
print('s + boundary total   = [%s, %s]   (1 inside: %s, closure %.2e)'
      % (sLO(s_face + bnd_tot), sHI(s_face + bnd_tot), verdict['weight_total_1'],
         float(verdict['weight_total_closure'])))
print()
print('per-gap boundary weights nu_j (a_R,j + a_R,j+1):')
for j in range(9):
    print('   W_%d = [%s, %s]' % (j, sLO(bnd_gap[j]), sHI(bnd_gap[j])))
print()
print('face branch weights mu_i c_i (orbit-summed):')
for i in range(5):
    print('   w_face_%d = [%s, %s]' % (i, sLO(MU[i] * CK[i]), sHI(MU[i] * CK[i])))
print()
print('radial-equation control  v_j - a\'_j (nu_j + nu_{j-1})  (must contain 0):')
for j in range(9):
    print('   res_%d = [%s, %s]' % (j, sLO(radeq[j], 12), sHI(radeq[j], 12)))
print()
print('VERDICTS:')
for k in sorted(verdict):
    print('   %-28s %s' % (k, verdict[k]))
print('CONTROLS (vs old FD calibration):')
for k in sorted(CTL):
    print('   %-34s %s' % (k, ('%.3e' % CTL[k]) if isinstance(CTL[k], float) else CTL[k]))

# ------------------------------------------------------------------ dump
def I(x):
    return [sLO(x, 34), sHI(x, 34)]

out = dict(
    scope='interval enclosure of the odd-9 cyclic boundary-multiplier formula at the lead Krawczyk '
          '12D TC root box; same object (genuine physical chord-circle pins); interval forward AD '
          'w.r.t. rho_j; no root finding, no rank/SVD, no optimisation',
    box=dict(source='../lead/repaired_tc_krawczyk.json', radius_hex=CD['radius_hex'], radius=mp.nstr(mpf(RAD), 20),
             center_hex=CD['center_hex'], vars='u=(a0,a1,a2,a3,y0,y1,R,lam0..lam4)',
             krawczyk_contraction=CD['contraction_inf'], pass_inclusion=CD['pass_inclusion']),
    interval_backend=dict(mp_dps=60, iv_dps=35, note='mpmath iv, outward rounding; '
                          'rho_j partials by interval forward-mode AD with the other coordinates as intervals'),
    R=I(R), rho=[I(x) for x in RHO], theta=[I(x) for x in TH], a=[I(x) for x in A],
    a_prime=[I(x) for x in APRIME], a_R=[I(x) for x in AR],
    mu=[I(x) for x in MU], nu=[I(x) for x in nu], nu_sym=[I(x) for x in nu_sym],
    v=[I(x) for x in v], w=[I(x) for x in w], ck=[I(x) for x in CK],
    s=I(s_face), one_minus_s=I(one_minus_s), boundary_total_9gap=I(bnd_tot), boundary_total_orbit=I(bnd_sym),
    boundary_gap_weights=[I(x) for x in bnd_gap], face_weights=[I(MU[i] * CK[i]) for i in range(5)],
    f_residuals=[I(C[i]['f'].v) for i in range(9)], F_out=[I(C[i]['Fout'].v) for i in range(9)],
    y_height=[I(C[i]['y'].v) for i in range(9)],
    radial_equation_residual=[I(x) for x in radeq],
    contacts=['%s %d %d' % c for c in CONTACTS], orbit_of_contact=[ORBIT[i] for i in range(9)],
    verdict=verdict, controls=CTL, fails=fails, seconds=time.time() - t0,
    source_hashes={str(p): __import__('hashlib').sha256(p.read_bytes()).hexdigest()
                   for p in [Path(__file__), LEAD / 'repaired_tc_krawczyk.json',
                             LEAD / 'TC-TO-PHYSICAL-KKT-LIFT.md', LEAD / 'TC-BOUNDARY-CHART-RANK.md']},
)
(OUT / 'phase7_interval_cyclic_nu.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
print()
print('[done] -> out/phase7_interval_cyclic_nu.json   (%.1f s)' % out['seconds'])
