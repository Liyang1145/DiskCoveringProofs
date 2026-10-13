"""r20-rigidity: executable candidate constants for the quantitative neighbourhood (coarse closed forms).

Implements R20-QUANTITATIVE-NEIGHBORHOOD.md section 5: interval geometric margins over the chart box
(det_min = 2 min area, d_min, rad_min), explicit numerator bounds for the face/tie branch derivatives
(degree-explicit: w = P/(2 det) with P cubic => det_min^{-2,-3,-4}), the |.|-chain rule, the fixed
point rho = min(1, mu eta/L2, lambda/(2 L3)) with f_min = R* - rho, and the assembly
L2 = max_i L2_i, L3 = max_i L3_i, M <= sum_i w_i L2_i.

All printed constants are CANDIDATES: the numerator coefficients still need a finite symbolic check
(see the design note).  No interval certification of L2/L3 is claimed here.

Writes r20_operator_bounds.json / .log.
"""
import json
from pathlib import Path
import mpmath as mp

P = Path(__file__).parent
LEAD = P.parent / 'lead'
mp.mp.dps = 40
mp.iv.dps = 40
REP = []


def say(s):
    print(s, flush=True)
    REP.append(s)


CERT = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text(encoding='utf-8'))
RAD_ = float.fromhex(CERT['certificate']['radius_hex'])
CHV = [float.fromhex(v) for v in CERT['certificate']['center_hex'][:7]]
ZIV = [mp.iv.mpf(CHV[i]) + mp.iv.mpf([-RAD_, RAD_]) for i in range(7)]
R_STAR = mp.mpf(CERT['numeric_root'][6])
a0, a1, a2, a3, y0, y1, Rv = ZIV
a4 = mp.iv.pi - 2 * (a0 + a1 + a2 + a3)
ak = [a0, a1, a2, a3, a4, a3, a2, a1, a0]
th = [mp.iv.mpf(0)] * 9
for k in range(5, 9):
    th[k] = th[k - 1] + ak[k - 1] + ak[k]
for k in range(3, -1, -1):
    th[k] = th[k + 1] - (ak[k] + ak[k + 1])
rho_ = [mp.iv.cos(ak[k]) - mp.iv.sqrt(Rv * Rv - mp.iv.sin(ak[k]) ** 2) for k in range(9)]
C = [(rho_[k] * mp.iv.cos(th[k]), rho_[k] * mp.iv.sin(th[k])) for k in range(9)]
S = C + [(y0, mp.iv.mpf(0)), (y1, mp.iv.mpf(0))]
FACES = [(1, 2, 10), (2, 3, 9), (3, 4, 9), (4, 5, 9), (5, 6, 9), (6, 7, 10), (8, 0, 10)]
say('[O0] chart box (r = %.1e exact) ; R* = %s' % (RAD_, mp.nstr(R_STAR, 22)))


def lo(x):
    return mp.mpf(x.a)


def hi(x):
    return mp.mpf(x.b)


det_min = None
for tri in FACES:
    ca, cb, cc = S[tri[0]], S[tri[1]], S[tri[2]]
    g1x, g1y = ca[0] - cb[0], ca[1] - cb[1]
    g2x, g2y = ca[0] - cc[0], ca[1] - cc[1]
    det = g1x * g2y - g1y * g2x
    d_ = min(abs(lo(det)), abs(hi(det)))
    det_min = d_ if det_min is None else min(det_min, d_)
d_min, rad_min = None, None
for k in range(9):
    ca, cb = S[k], S[(k + 1) % 9]
    dx, dy = cb[0] - ca[0], cb[1] - ca[1]
    D = dx * dx + dy * dy
    dn = mp.iv.sqrt(D)
    d_min = lo(dn) if d_min is None else min(d_min, lo(dn))
    kap = ((cb[0] * cb[0] + cb[1] * cb[1]) - (ca[0] * ca[0] + ca[1] * ca[1])) / 2
    a0x, a0y = (kap / D) * dx, (kap / D) * dy
    rad = 1 - (a0x * a0x + a0y * a0y)
    rad_min = lo(rad) if rad_min is None else min(rad_min, lo(rad))
say('[O1] margins over the box: det_min >= %.6f ; d_min >= %.6f ; rad_min >= %.6f'
    % (det_min, d_min, rad_min))

# scale-separated crude numerator coefficients (design step 3): N_k are NOT assumed small and
# homogeneity is NOT used as a conditioning substitute; the finite symbolic check is still pending.
Cw = [(12, 1, 1), (48, 2, 2), (192, 3, 3)]      # (N_k, power of g_min, power of sin_min)
sin_min = det_min / 4                           # sin th = det/(|g1||g2|), |g_i| <= 2
g_min = mp.mpf('0.30')                          # |g_i| floor for the active faces (conservative)
say('[O2a] scale-separated margins: sin_min = det_min/4 = %.6f ; g_min floor = %.6f (conservative)'
    % (sin_min, g_min))
mu = mp.mpf('0.00143254')                      # pilot (LP vertex enumeration)
lam = mp.mpf('0.082')                          # half of the numeric 0.164903 (conservative placeholder)
say('[O2] using mu = %.8f (pilot) and lambda = %.4f (half of the numeric quotient margin; certificate pending)'
    % (mu, lam))

rho = mp.mpf('1e-3')
for it in range(6):
    f_min = R_STAR - rho
    dw = Cw[0][0] / (g_min ** Cw[0][1] * sin_min ** Cw[0][2])
    d2w = Cw[1][0] / (g_min ** Cw[1][1] * sin_min ** Cw[1][2])
    d3w = Cw[2][0] / (g_min ** Cw[2][1] * sin_min ** Cw[2][2])
    L2_face = d2w + dw * dw / f_min
    L3_face = d3w + 3 * dw * d2w / f_min + dw ** 3 / f_min ** 2
    # tie branch (coarse): denominators d_min and sqrt(rad_min)
    dA0, d2A0, d3A0 = 4 / d_min, 16 / d_min ** 2, 64 / d_min ** 3
    dn1, dn2, dn3 = 1 / d_min, 2 / d_min ** 2, 8 / d_min ** 3
    rt = mp.sqrt(rad_min)
    dt1 = dA0 / rt
    dt2 = (d2A0 + dA0 ** 2 / rt) / rt
    dt3 = (d3A0 + 3 * dA0 * d2A0 / rt + 2 * dA0 ** 3 / rt ** 2) / rt
    dp1, dp2, dp3 = dA0 + dt1 + dn1, d2A0 + dt2 + dn2, d3A0 + dt3 + dn3
    L2_tie = dp2 + dp1 ** 2 / f_min
    L3_tie = dp3 + 3 * dp1 * dp2 / f_min + dp1 ** 3 / f_min ** 2
    L2 = max(L2_face, L2_tie)
    L3 = max(L3_face, L3_tie)
    M = L2                                       # conservative M <= sum_i w_i L2_i <= max_i L2_i
    eta = min(mp.mpf(1) / 4, lam / (16 * M))
    rho_new = min(mp.mpf(1), mu * eta / L2, lam / (2 * L3))
    say('[O3] iter %d: f_min = %.6f ; L2(face/tie) = %.3f/%.3f ; L3(face/tie) = %.3f/%.3f ;'
        ' eta = %.3e ; rho = %.3e' % (it, f_min, L2_face, L2_tie, L3_face, L3_tie, eta, rho_new))
    if abs(rho_new - rho) < mp.mpf('1e-12'):
        rho = rho_new
        break
    rho = rho_new
c = min(mu * eta / (2 * rho), lam / 4)
say('[O4] candidate constants: L2 = %.4f ; L3 = %.4f ; M = %.4f ; eta = %.3e ; rho = %.3e ; c = %.6e'
    % (L2, L3, M, eta, rho, c))
say('     branch validity: f_min = R* - rho = %.6f > 0 : %s ; det_min/d_min/rad_min > 0 : %s'
    % (R_STAR - rho, bool(R_STAR - rho > 0), bool(det_min > 0 and d_min > 0 and rad_min > 0)))
OUT = {'margins': {'det_min': float(det_min), 'd_min': float(d_min), 'rad_min': float(rad_min)},
       'mu': float(mu), 'lambda_placeholder': float(lam), 'L2': float(L2), 'L3': float(L3),
       'M': float(M), 'eta': float(eta), 'rho': float(rho), 'c': float(c),
       'status': 'candidates; numerator coefficients need the finite symbolic check; lambda needs the '
                 'certified quotient value (C893+C901); mu needs the interval LP value',
       'repro': 'py -3 -B -X utf8 r20_operator_bounds.py'}
(P / 'r20_operator_bounds.json').write_text(json.dumps(OUT, indent=2))
(P / 'r20_operator_bounds.log').write_text('\n'.join(REP) + '\n')
say('\nwritten r20_operator_bounds.json / .log')
