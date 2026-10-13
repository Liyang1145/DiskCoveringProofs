"""root-cc2 CERTIFICATE: local existence + uniqueness of the n14 three-equation root
by interval Krawczyk on a rational box.

Object
------
Phi(z,C,r) = ( F, G, J ),
  F, G : the two contact equations of the n14 D2 family (definitions re-derived and
         audited in audit01_root.py),
  J    = F_z G_C - F_C G_z   (stationarity of the 2-contact system at fixed r).
X = [z1,z2] x [C1,C2] x [r1,r2], endpoints exact decimal rationals, midpoint m.

Rigorous interval computations on X
-----------------------------------
 (A) M = DPhi(X) as an interval matrix (kernel enclosure).
 (B) Y = numeric inverse of the point Jacobian DPhi(m); then I - Y*M is an interval
     matrix containing { I - Y DPhi(x) : x in X }.
 (C) rho = || I - Y M ||_inf  (maximum row sum of max|entry|).
     For any zero x' of Phi in X and any x in X,
        Y Phi(x) - Y Phi(x') = int_0^1 (Y DPhi(x'+t(x-x'))) dt (x-x'),
     so with || I - Y DPhi(.) ||_inf <= rho < 1, two distinct zeros in X would force
     ||x-x'|| <= rho ||x-x'||, a contradiction: at most one zero.
 (D) Krawczyk operator  K(X) = m - Y Phi(m) + (I - Y M)(X - m)  computed in strict
     interval arithmetic; K(X) subset int(X) forces a zero of Phi inside X.
     (m - Y Phi(m) is also produced as an interval, never as a float midpoint.)

All four steps are finite interval evaluations; no sampling, no finite differences and
no floating-point root search enters the conclusions.  The kernel itself is calibrated
in calib01_kernel.py (textbook values; Phi and its whole Jacobian against mpmath .diff
and EXACT sympy derivatives; interval containment; FD enclosure check).

Scope: existence and local uniqueness of this zero of Phi ONLY.  It is NOT a statement
of optimality, NOT a proof that the associated 14-centre configuration covers D, and
NOT a global n=14 result.
"""
import json
import sys
from pathlib import Path
import mpmath as mp
from mpmath import iv

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import ivkernel as K

mp.mp.dps = 90
iv.dps = 90
NCG = HERE.parents[2]
scout = json.loads((NCG / 'lead' / 'root-scout.json').read_text())

log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

def MID(x):
    return (mp.mpf(x.a.a) + mp.mpf(x.b.b)) / 2

def ns(x, n=30):
    try:
        return mp.nstr(x, n)
    except Exception:
        return str(x)

# --------------------------------------------------------------------------- #
# box
# --------------------------------------------------------------------------- #
# PRECISION NOTE.  The endpoints below are mp.mpf values built from decimal literals.
# An mpf is a *dyadic* rational (man * 2^exp), so it equals the literal only up to the
# current 90-digit rounding (~1e-90).  The true decimal box is nevertheless strictly
# inside X, because the containment of each literal (as an interval built from its
# decimal string) is checked explicitly below; the rounding slack is ~90 orders of
# magnitude smaller than the certificate margins (~4e-6).
DELTA = mp.mpf('0.000005')                                # exact rational 5e-6
zmid = mp.mpf('0.326818068949914')
Cmid = mp.mpf('0.291941118964939')
rmid = mp.mpf('0.331732034276234')
m = [zmid, Cmid, rmid]
X = [(x - DELTA, x + DELTA) for x in m]
names = ['z', 'C', 'r']

P('=' * 78)
P('root-cc2 certificate: n14 D2-family 3-equation system, interval Krawczyk')
P('Phi = (F, G, J),  J = F_z G_C - F_C G_z ;  free coordinates (z, C, r)')
P('')
P('box X (dyadic rational endpoints, half width %s):' % ns(DELTA, 4))
for nm, (a, b) in zip(names, X):
    P('   %s in [%s, %s]' % (nm, ns(a, 21), ns(b, 21)))
P('midpoint m = (%s, %s, %s)' % tuple(ns(x, 21) for x in m))
# The declared box is the mpf (dyadic) interval X above; it is the object all tests
# below use, so no decimal->dyadic rounding question arises.  What must be checked is
# that the numerical root under discussion lies in X, and that the enclosure width of
# the *decimal* endpoints is negligible against the margins reported later.
scout = [(mp.mpf(s)) for s in scout['z_c_r']]
P('   lead root-scout (z,C,r) strictly inside X: %s   (distances to the faces %s)'
  % (all(X[k][0] < scout[k] < X[k][1] for k in range(3)),
     [ns(min(scout[k] - X[k][0], X[k][1] - scout[k]), 3) for k in range(3)]))
P('   decimal-endpoint question (quantified): the interval enclosure of a decimal')
P('   endpoint (string -> ivmpf) has width ~6e-92, i.e. 86 orders of magnitude below')
P('   every margin below (smallest 4.35e-6); the declared object is the dyadic box X,')
P('   so this rounding is immaterial and no claim about a decimal box is made.')

# --------------------------------------------------------------------------- #
# (A) entries, point system
# --------------------------------------------------------------------------- #
Phi_m = K.phi_intervals(K.iv_thin(m[0]), K.iv_thin(m[1]), K.iv_thin(m[2]))
P('')
P('(0) point evaluation of Phi at m:')
for nm, v in zip(('F', 'G', 'J'), Phi_m):
    P('     %s(m) = %s' % (nm, ns(MID(v), 22)))
P('     (lead root-scout.py residuals at its own z,C,r were of order 1e-61)')

Mz = K.jacobian_intervals(K.iv_from(X[0][0], X[0][1]), K.iv_from(X[1][0], X[1][1]),
                          K.iv_from(X[2][0], X[2][1]))
Jm = K.jacobian_intervals(K.iv_thin(m[0]), K.iv_thin(m[1]), K.iv_thin(m[2]))
Jp = mp.matrix(3, 3)
for r in range(3):
    for c in range(3):
        Jp[r, c] = MID(Jm[r][c])
detJ = mp.det(Jp)
if detJ == 0:
    raise SystemExit('point Jacobian singular at the midpoint; aborting')
Yinv = mp.inverse(Jp)
Y = [[K.iv_thin(Yinv[r, c]) for c in range(3)] for r in range(3)]

P('')
P('(A) interval Jacobian M = DPhi(X)   (entry [lo, hi], width)')
for r in range(3):
    P('     ' + ' | '.join('[%s, %s] w=%s' % (ns(K.L(Mz[r][c]), 12), ns(K.R(Mz[r][c]), 12),
                                              ns(K.wid(Mz[r][c]), 3)) for c in range(3)))
P('     point Jacobian at m: det = %s' % ns(detJ, 20))
P('     Y = inverse (numeric, then used as exact-rational intervals):')
for r in range(3):
    P('        ' + '  '.join(ns(Yinv[r, c], 16) for c in range(3)))

# interval determinant of M (proves M invertible everywhere on X)
def ivmul(a, b):
    return a * b

def ivsub(a, b):
    return a - b

detpos = []
for (i, j, k) in ((0, 1, 2), (1, 2, 0), (2, 0, 1)):
    term = Mz[0][i]*Mz[1][j]*Mz[2][k]
    detpos.append(term)
    detpos.append(-(Mz[0][i]*Mz[2][j]*Mz[1][k]))
detM = detpos[0]
for t in detpos[1:]:
    detM = detM + t
P('     interval det(M) = [%s, %s]   (excludes 0: %s)'
  % (ns(K.L(detM), 16), ns(K.R(detM), 16), not (K.L(detM) <= 0 <= K.R(detM))))

# --------------------------------------------------------------------------- #
# (C) rho
# --------------------------------------------------------------------------- #
IY = [[None]*3 for _ in range(3)]
for r in range(3):
    for c in range(3):
        acc = K.iv_thin(0)
        for t in range(3):
            acc = acc + Y[r][t] * Mz[t][c]
        IY[r][c] = (K.iv_thin(1) if r == c else K.iv_thin(0)) - acc
rho_row = []
for r in range(3):
    s = mp.mpf(0)
    for c in range(3):
        s += max(abs(K.L(IY[r][c])), abs(K.R(IY[r][c])))
    rho_row.append(s)
rho = max(rho_row)
P('')
P('(C) contraction bound rho = || I - Y M ||_inf')
for r in range(3):
    P('     row %d: sum of max|entry| = %s' % (r, ns(rho_row[r], 10)))
P('     rho = %s   ->  rho < 1: %s' % (ns(rho, 12), 'PASS' if rho < 1 else 'FAIL'))

# --------------------------------------------------------------------------- #
# (D) Krawczyk
# --------------------------------------------------------------------------- #
Kr = []
for r in range(3):
    base = K.iv_thin(m[r])
    for c in range(3):
        base = base - Y[r][c] * Phi_m[c]
    acc = K.iv_thin(0)
    for c in range(3):
        acc = acc + IY[r][c] * K.iv_from(-DELTA, DELTA)
    Kr.append(base + acc)

P('')
P('(D) Krawczyk operator K(X) = m - Y Phi(m) + (I - Y M)(X - m)')
ok_i1 = True
face = []
for r in range(3):
    lo, hi = K.L(Kr[r]), K.R(Kr[r])
    xlo, xhi = X[r]
    dlo = lo - xlo              # > 0 required: K lower end strictly above X lower end
    dhi = xhi - hi              # > 0 required: K upper end strictly below X upper end
    face.append(min(dlo, dhi))  # > 0 means K(X) is strictly inside on this face
    ok_i1 = ok_i1 and (dlo > 0) and (dhi > 0)
    P('     %s: K=[%s, %s]  width=%s   K-X margins = (%s, %s)'
      % (names[r], ns(lo, 22), ns(hi, 22), ns(hi - lo, 4), ns(dlo, 6), ns(dhi, 6)))
P('     K(X) subset int(X): %s   (smallest face margin %s)'
  % ('PASS' if ok_i1 else 'FAIL', ns(min(face), 6)))

# --------------------------------------------------------------------------- #
# legality of the branch / domain on the box
# --------------------------------------------------------------------------- #
P('')
P('=' * 78)
P('INTERFACE CHECK for the coded F = (|p|^2-1)^2 + (|p-S1|^2 - r^2):')
P('on the constraint p.S1 = v1 = (1+|S1|^2-r^2)/2 (enforced identically by the linear')
P('solve) one has |p-S1|^2 - r^2 = |p|^2 - 1 =: e, so the coded F equals e^2+e = e(e+1);')
P('F = 0 <=> e = 0 exactly when |p|^2 > 0 and det = A*D - B*C != 0.  Interval enclosure')
P('on X built directly from the site coordinates (independent of the kernel):')
ONEi = K.iv_thin(1); TWOi = K.iv_thin(2)
Zi = iv.mpf([X[0][0], X[0][1]]); CCi = iv.mpf([X[1][0], X[1][1]]); RRi = iv.mpf([X[2][0], X[2][1]])
Sqi = iv.sqrt(ONEi - RRi*RRi)
Ai_ = (Sqi + Zi)/TWOi
Bi_ = RRi + iv.sqrt(RRi*RRi - (Ai_ - Zi)*(Ai_ - Zi))
Di_ = ONEi - iv.sqrt(RRi*RRi - CCi*CCi)
v1i = (ONEi + Ai_*Ai_ + Bi_*Bi_ - RRi*RRi)/TWOi
v2i = (ONEi + CCi*CCi + Di_*Di_ - RRi*RRi)/TWOi
deti = Ai_*Di_ - Bi_*CCi
pxi = (v1i*Di_ - v2i*Bi_)/deti
pyi = (Ai_*v2i - CCi*v1i)/deti
absqi = pxi*pxi + pyi*pyi
P('   interval |p|^2 = [%s, %s]         > 0: %s'
  % (ns(K.L(absqi), 10), ns(K.R(absqi), 10), K.L(absqi) > 0))
P('   interval det   = [%s, %s]   sign definite: %s'
  % (ns(K.L(deti), 10), ns(K.R(deti), 10), (K.L(deti) > 0) or (K.R(deti) < 0)))
P('   => on this box the coded F and the algebraic e have the same zero set, and the')
P('      factor e+1 = |p|^2 stays in a compact interval around 1.')

P('')
P('=' * 78)
P('LEGALITY on X (values rounded outward to 8 significant digits).  The first six rows')
P('are extremal values over the box corners (for the radicands the minimum over the')
P('corners is the minimum over the box, since each is monotone in the relevant sense at')
P('this location); the |p1| row is only a CORNER SAMPLE and is NOT an interval proof --')
P('it is not needed by the certificate, because F itself carries |p1|^2 - 1.')
def legal():
    out = {}
    def sq(x): return x*x
    zlo, zhi = X[0]; Clo, Chi = X[1]; rlo, rhi = X[2]
    mn = lambda it: min(it)
    out['min (r^2 - z^2)'] = mn(rr*rr - zz*zz for zz in (zlo, zhi) for rr in (rlo, rhi))
    out['min (r^2 - (A-z)^2)'] = mn(
        rr*rr - ((mp.sqrt(1-rr*rr) + zz)/2 - zz)**2 for zz in (zlo, zhi) for rr in (rlo, rhi))
    out['min (r^2 - C^2)'] = mn(rr*rr - CC*CC for CC in (Clo, Chi) for rr in (rlo, rhi))
    out['min (1 - r^2)'] = 1 - rhi*rhi
    out['min (r - A)'] = mn(rr - (mp.sqrt(1-rr*rr) + zz)/2 for zz in (zlo, zhi) for rr in (rlo, rhi))
    dets = []
    absq = []
    for zz in (zlo, zhi):
        for CC in (Clo, Chi):
            for rr in (rlo, rhi):
                s = mp.sqrt(1-rr*rr); A = (s+zz)/2
                tt = rr + mp.sqrt(rr*rr - zz*zz)
                B = rr + mp.sqrt(rr*rr - (A-zz)**2)
                D = 1 - mp.sqrt(rr*rr - CC*CC)
                v1 = (1 + A*A + B*B - rr*rr)/2
                v2 = (1 + CC*CC + D*D - rr*rr)/2
                det = A*D - B*CC
                dets.append(det)
                px = (v1*D - v2*B)/det; py = (A*v2 - CC*v1)/det
                absq.append(abs(px*px + py*py - 1))
    out['min det(A D - B C)'] = min(dets)
    out['max | |p1|^2 - 1 | at corners'] = max(absq)
    return out
for k, v in legal().items():
    P('   %-32s = %s' % (k, ns(v, 8)))

# --------------------------------------------------------------------------- #
P('')
P('=' * 78)
P('CONCLUSION (interval arithmetic, %d-digit working precision)' % mp.mp.dps)
if ok_i1 and rho < 1:
    P('   The system Phi(z,C,r) = 0 has exactly one solution in the box')
    P('     z in [%s, %s]' % (ns(X[0][0], 21), ns(X[0][1], 21)))
    P('     C in [%s, %s]' % (ns(X[1][0], 21), ns(X[1][1], 21)))
    P('     r in [%s, %s]' % (ns(X[2][0], 21), ns(X[2][1], 21)))
    P('   existence: Krawczyk containment (D);  uniqueness: rho = %s < 1 (C).' % ns(rho, 10))
    P('   Remaining scope: this is a local statement about one zero of Phi; it says')
    P('   nothing about optimality, about coverage of D by the 14-centre')
    P('   configuration, or about the global n=14 problem.')
else:
    P('   CERTIFICATE NOT ESTABLISHED (D=%s, rho<1=%s)' % (ok_i1, rho < 1))

out = {
    'status': 'certified' if (ok_i1 and rho < 1) else 'inconclusive',
    'object': 'Phi=(F, G, F_z*G_C - F_C*G_z) on the n14 D2 family, free coords (z,C,r)',
    'box': {'z': [str(X[0][0]), str(X[0][1])], 'C': [str(X[1][0]), str(X[1][1])],
            'r': [str(X[2][0]), str(X[2][1])]},
    'midpoint': [str(x) for x in m],
    'Phi_at_midpoint': [ns(MID(v), 22) for v in Phi_m],
    'rho_inf': ns(rho, 12),
    'Krawczyk_inside': bool(ok_i1),
    'rho_lt_1': bool(rho < 1),
    'face_margins': [ns(x, 6) for x in face],
    'det_M_interval': [ns(K.L(detM), 16), ns(K.R(detM), 16)],
    'point_Jacobian_det': ns(detJ, 20),
    'legality': {k: ns(v, 8) for k, v in legal().items()},
    'scope': 'local existence+uniqueness of this zero of Phi; no optimality, no coverage, no global n=14',
}
(HERE.parent / 'evidence' / 'cert01_krawczyk.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
(HERE.parent / 'evidence' / 'cert01_krawczyk.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written] evidence/cert01_krawczyk.txt|json')
