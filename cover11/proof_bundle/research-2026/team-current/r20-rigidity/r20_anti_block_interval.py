"""r20-rigidity (step 16): INTERVAL anti block on the lead's 12D root box, with r20-stress's
interval KKT weights (no frozen weights, no numeric rank / SVD used in any claim).

Objects (all interval, over the whole box):
  * A_anti(x)  : 8x11 orbit-representative anti gradient block of the 18 active branches
                 (7 TC chart variables + 11 anti amplitudes = 18 jet variables, so the values
                 stay on the reflection-symmetric slice);
  * explicit 8x8 witness minor -> interval determinant != 0  (rank >= 8; on the symmetric slice
    rank <= 8 by the orbit structure, hence rank = 8 and dim anti kernel = 3);
  * explicit kernel basis (rational function of x from the minor, NOT an SVD), the rotation
    direction removed explicitly -> 2-dimensional quotient;
  * weighted epsilon-epsilon Hessian  H_W = sum_i w_i d^2 f_i / d eps d eps  with w = stress's
    interval physical weights (mu_i c_i on faces, nu_j b_j on ties)
    -> interval 2x2 generalized-eigenvalue lower bound on the quotient.

Read-only inputs: ../lead/repaired_tc_krawczyk.json, ../r20-stress/out/phase7_interval_cyclic_nu.json.
Writes r20_anti_block_interval.json / .log.
"""
import json, os, sys, time
from pathlib import Path
import numpy as np
import scipy.linalg as sla
import mpmath as mp

P = Path(__file__).parent
LEAD = P.parent / 'lead'
STRESS = P.parent / 'r20-stress'
DPS = 60
mp.mp.dps = DPS
mp.iv.dps = DPS
N = 22
NC = 7
NV = 18                      # 7 chart variables + 11 anti amplitudes
OUT = {}
REP = []
POINT = os.environ.get('R20_POINT', '') == '1'


def say(s):
    print(s, flush=True)
    REP.append(s)


IVMF = type(mp.iv.mpf(0))
I0 = mp.iv.mpf(0)
I1 = mp.iv.mpf(1)


def ivp(x):
    return mp.iv.mpf(mp.mpf(x))


def EL(x):
    """exact lower endpoint of an ivmpf as mpf (.a is a degenerate interval)."""
    return mp.mpf(x.a)


def EH(x):
    return mp.mpf(x.b)


def EM(x):
    return mp.mpf(x.mid)


def isq(x):
    if isinstance(x, IVJ):
        return x._sqrt()
    return mp.iv.sqrt(x) if isinstance(x, IVMF) else mp.sqrt(x)


def icos(x):
    if isinstance(x, IVJ):
        return x._cos()
    return mp.iv.cos(x) if isinstance(x, IVMF) else mp.cos(x)


def isin(x):
    if isinstance(x, IVJ):
        return x._sin()
    return mp.iv.sin(x) if isinstance(x, IVMF) else mp.sin(x)


class IVJ(object):
    """interval value + interval gradient + interval Hessian, second-order Taylor arithmetic."""
    __slots__ = ('v', 'g', 'h', 'n')

    def __init__(self, v, g=None, h=None, n=NV):
        self.v = v
        self.n = n
        self.g = g if g is not None else mp.iv.matrix(n, 1)
        self.h = h if h is not None else mp.iv.matrix(n, n)

    @staticmethod
    def var(i, v, n=NV):
        g = mp.iv.matrix(n, 1)
        g[i, 0] = I1
        return IVJ(v, g, mp.iv.matrix(n, n), n)

    @staticmethod
    def const(v, n=NV):
        val = v if isinstance(v, IVMF) else mp.iv.mpf(mp.mpf(v))
        return IVJ(val, mp.iv.matrix(n, 1), mp.iv.matrix(n, n), n)

    def __add__(self, o):
        o = _v(o, self.n)
        return IVJ(self.v + o.v, self.g + o.g, self.h + o.h, self.n)

    __radd__ = __add__

    def __neg__(self):
        return IVJ(-self.v, -self.g, -self.h, self.n)

    def __sub__(self, o):
        return self + (-_v(o, self.n))

    def __rsub__(self, o):
        return _v(o, self.n) + (-self)

    def __mul__(self, o):
        o = _v(o, self.n)
        return IVJ(self.v * o.v, self.v * o.g + o.v * self.g,
                   self.v * o.h + o.v * self.h + self.g * o.g.T + o.g * self.g.T, self.n)

    __rmul__ = __mul__

    def __pow__(self, k):
        if k == 1:
            return self
        r = IVJ.const(1, self.n)
        for _ in range(k):
            r = r * self
        return r

    def _recip(self):
        r = I1 / self.v
        return IVJ(r, -self.g * r * r,
                   (self.g * self.g.T) * (2 * r ** 3) - self.h * (r * r), self.n)

    def __truediv__(self, o):
        return self * _v(o, self.n)._recip()

    def __rtruediv__(self, o):
        return _v(o, self.n) * self._recip()

    def _sqrt(self):
        s = mp.iv.sqrt(self.v)
        return IVJ(s, self.g / (2 * s),
                   self.h / (2 * s) - (self.g * self.g.T) / (4 * s ** 3), self.n)

    def _cos(self):
        return IVJ(mp.iv.cos(self.v), -mp.iv.sin(self.v) * self.g,
                   -mp.iv.cos(self.v) * (self.g * self.g.T) - mp.iv.sin(self.v) * self.h, self.n)

    def _sin(self):
        return IVJ(mp.iv.sin(self.v), mp.iv.cos(self.v) * self.g,
                   -mp.iv.sin(self.v) * (self.g * self.g.T) + mp.iv.cos(self.v) * self.h, self.n)


def _v(x, n=NV):
    return x if isinstance(x, IVJ) else IVJ.const(x, n)


# --------------------------------------------------------------------------- jet self-test
def jet_selftest():
    """analytic controls: 1/x and x/y with known Hessians (point intervals)."""
    def mag(x):
        return max(abs(EL(x)), abs(EH(x)))

    n = 3
    x = IVJ.var(0, ivp('1.7'), n)
    y = IVJ.var(1, ivp('0.9'), n)
    a = IVJ.const(1, n) / x
    b = x / y
    c = isq(x * x + y * y)
    r = []
    r.append(('1/x', max(mag(a.g[0, 0] + 1 / mp.mpf('1.7') ** 2),
                         mag(a.h[0, 0] - 2 / mp.mpf('1.7') ** 3), mag(a.h[0, 1]))))
    r.append(('x/y', max(mag(b.g[0, 0] - 1 / mp.mpf('0.9')),
                         mag(b.g[1, 0] + mp.mpf('1.7') / mp.mpf('0.9') ** 2),
                         mag(b.h[0, 1] + 1 / mp.mpf('0.9') ** 2),
                         mag(b.h[1, 1] - 2 * mp.mpf('1.7') / mp.mpf('0.9') ** 3))))
    R = mp.sqrt(mp.mpf('1.7') ** 2 + mp.mpf('0.9') ** 2)
    u0, u1 = mp.mpf('1.7') / R, mp.mpf('0.9') / R
    r.append(('sqrt', max(mag(c.h[0, 0] - (1 - u0 * u0) / R), mag(c.h[1, 1] - (1 - u1 * u1) / R),
                          mag(c.h[0, 1] + u0 * u1 / R))))
    rr = [(nm, mp.mpf(i)) for nm, i in r]
    return rr


_st = jet_selftest()
say('[A-1] jet self-test (1/x, x/y, sqrt) max error per case: '
    + ' ; '.join('%s %.2e' % (nm, float(e)) for nm, e in _st))
assert max(e for _, e in _st) < mp.mpf('1e-40'), _st


# --------------------------------------------------------------------------- branches
def face_branch(S, tri):
    a, b, c = tri
    ca, cb, cc = S[a], S[b], S[c]
    g1x, g1y = ca[0] - cb[0], ca[1] - cb[1]
    g2x, g2y = ca[0] - cc[0], ca[1] - cc[1]
    det = g1x * g2y - g1y * g2x
    b1 = -(g1x * g1x + g1y * g1y) / 2
    b2 = -(g2x * g2x + g2y * g2y) / 2
    wx = (b1 * g2y - b2 * g1y) / det
    wy = (g1x * b2 - g2x * b1) / det
    return (ca[0] + wx, ca[1] + wy), isq(wx * wx + wy * wy)


def tie_branch(S, k, sgn):
    ca, cb = S[k], S[(k + 1) % 9]
    dx, dy = cb[0] - ca[0], cb[1] - ca[1]
    D = dx * dx + dy * dy
    kap = ((cb[0] * cb[0] + cb[1] * cb[1]) - (ca[0] * ca[0] + ca[1] * ca[1])) / 2
    dl = isq(D)
    a0x, a0y = (kap / D) * dx, (kap / D) * dy
    t = sgn * isq(1 - (a0x * a0x + a0y * a0y))
    p = (a0x + t * (-dy / dl), a0y + t * (dx / dl))
    wx, wy = p[0] - ca[0], p[1] - ca[1]
    return p, isq(wx * wx + wy * wy)


def chart_sites_jet(z):
    a0, a1, a2, a3, y0, y1, R = z
    a4 = IVJ(mp.iv.pi, mp.iv.matrix(NC, 1), mp.iv.matrix(NC, NC), NC) - 2 * (a0 + a1 + a2 + a3)
    ak = [a0, a1, a2, a3, a4, a3, a2, a1, a0]
    th = [IVJ.const(0, NC)] * 9
    for k in range(5, 9):
        th[k] = th[k - 1] + ak[k - 1] + ak[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (ak[k] + ak[k + 1])
    rho = [icos(ak[k]) - isq(R * R - isin(ak[k]) ** 2) for k in range(9)]
    C = [(rho[k] * icos(th[k]), rho[k] * isin(th[k])) for k in range(9)]
    return C + [(y0, IVJ.const(0, NC)), (y1, IVJ.const(0, NC))]


FACES = [(1, 2, 10), (2, 3, 9), (3, 4, 9), (4, 5, 9), (5, 6, 9), (6, 7, 10), (8, 0, 10),
         (2, 9, 10), (6, 9, 10), (0, 1, 10), (7, 8, 10)]
ACTIVE_FACES = list(range(9))
PAIRED_FACE_REPS = [0, 1, 2, 7]
PAIRED_TIE_REPS = [0, 1, 2, 3]
# my face index -> r20-stress face_weight_9 index (checked against WI's face_labels:
#   stress order = fan(1,H1), fan(6,H1), fan(2,H0), fan(5,H0), fan(3,H0), fan(4,H0),
#                  fan(8,H1), central(C6), central(C2))
FACE_MAP = {0: 0, 5: 1, 1: 2, 4: 3, 2: 4, 3: 5, 6: 6, 8: 7, 7: 8}

# --------------------------------------------------------------------------- box
CERT = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text(encoding='utf-8'))
ROOT = [mp.mpf(s) for s in CERT['numeric_root']]
Z0 = ROOT[:NC]
RAD = 0.0 if POINT else float.fromhex(CERT['certificate']['radius_hex'])
R_STAR = Z0[6]
say('[A0] %s : lead root box radius %.6e ; R* = %s'
    % ('POINT MODE (control)' if POINT else 'box mode', RAD, mp.nstr(R_STAR, 30)))
CHV = [float.fromhex(v) for v in CERT['certificate']['center_hex'][:7]]
ZIV = [ivp(CHV[i]) + mp.iv.mpf([-RAD, RAD]) for i in range(NC)]

# centre-mode values for the frozen branch choices


def chart_sites_f(z):
    a0, a1, a2, a3, y0, y1, R = z
    a4 = mp.pi - 2 * (a0 + a1 + a2 + a3)
    ak = [a0, a1, a2, a3, a4, a3, a2, a1, a0]
    th = [mp.mpf(0)] * 9
    for k in range(5, 9):
        th[k] = th[k - 1] + ak[k - 1] + ak[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (ak[k] + ak[k + 1])
    rho = [mp.cos(ak[k]) - mp.sqrt(R * R - mp.sin(ak[k]) ** 2) for k in range(9)]
    C = [(rho[k] * mp.cos(th[k]), rho[k] * mp.sin(th[k])) for k in range(9)]
    return C + [(y0, mp.mpf(0)), (y1, mp.mpf(0))]


S0 = chart_sites_f(Z0)
TIEPICK = {}
for k in range(9):
    pick = None
    for sgn in (1, -1):
        p, f = tie_branch(S0, k, sgn)
        ds = sorted((mp.sqrt((p[0] - s[0]) ** 2 + (p[1] - s[1]) ** 2), i) for i, s in enumerate(S0))
        if set(i for _, i in ds[:2]) == {k, (k + 1) % 9}:
            pick = sgn
            break
    assert pick is not None, k
    TIEPICK[k] = pick
say('     frozen tie signs: %s' % [TIEPICK[k] for k in range(9)])

# --------------------------------------------------------------------------- 18-variable jets
BA = []
for k in range(4):
    j = 8 - k
    for t in range(2):
        sg = 1 if t == 0 else -1          # y flips under x -> x
        col = [0] * N
        col[2 * k + t] = 1
        col[2 * j + t] = -sg
        BA.append(col)
col = [0] * N; col[2 * 4 + 1] = 1; BA.append(col)
for s_ in (9, 10):
    col = [0] * N; col[2 * s_ + 1] = 1; BA.append(col)

t0 = time.time()
zJ = [IVJ.var(i, ZIV[i], NC) for i in range(NC)]
S7 = chart_sites_jet(zJ)
SJ = []
for i in range(11):
    for t in range(2):
        col = 2 * i + t
        g = mp.iv.matrix(NV, 1)
        for a in range(NC):
            g[a, 0] = S7[i][t].g[a, 0]
        for jj in range(11):
            g[NC + jj, 0] = ivp(BA[jj][col])
        h = mp.iv.matrix(NV, NV)
        for a in range(NC):
            for b in range(NC):
                h[a, b] = S7[i][t].h[a, b]
        SJ.append(IVJ(S7[i][t].v, g, h, NV))
SJL = [(SJ[2 * i], SJ[2 * i + 1]) for i in range(11)]
say('[A1] 18-variable jets built in %.1fs (7 chart + 11 anti amplitudes)' % (time.time() - t0))

BR = []
for i in ACTIVE_FACES:
    BR.append(('face', FACES[i], face_branch(SJL, FACES[i])))
for k in range(9):
    BR.append(('tie', (k, (k + 1) % 9), tie_branch(SJL, k, TIEPICK[k])))

A8 = mp.iv.matrix(8, 11)
anti_rows = PAIRED_FACE_REPS + [9 + k for k in PAIRED_TIE_REPS]
for i, r in enumerate(anti_rows):
    f = BR[r][2][1]
    for c in range(11):
        A8[i, c] = f.g[NC + c, 0]
say('[A2] anti 8x11 interval block (rows = orbit representatives %s)' % anti_rows)
# chart boundary ties B_k as plain intervals (same construction as the chart)
a4iv = mp.iv.pi - 2 * (ZIV[0] + ZIV[1] + ZIV[2] + ZIV[3])
akiv = [ZIV[0], ZIV[1], ZIV[2], ZIV[3], a4iv, ZIV[3], ZIV[2], ZIV[1], ZIV[0]]
thiv = [mp.iv.mpf(0)] * 9
for k in range(5, 9):
    thiv[k] = thiv[k - 1] + akiv[k - 1] + akiv[k]
for k in range(3, -1, -1):
    thiv[k] = thiv[k + 1] - (akiv[k] + akiv[k + 1])
tie_min, tie_id, tie_sep, tie_fail = None, [], None, None
_A4acc = {}
for k in range(9):
    p, f = tie_branch(SJL, k, TIEPICK[k])
    po, fo = tie_branch(SJL, k, -TIEPICK[k])
    dmin_other = None
    for q in range(11):
        if q in (k, (k + 1) % 9):
            continue
        dq2 = ((SJL[q][0] - p[0]) ** 2 + (SJL[q][1] - p[1]) ** 2).v
        m_ = EL(dq2) - EH((f * f).v)
        tie_min = m_ if tie_min is None else min(tie_min, m_)
        # A4 (stress): on the OTHER branch the nearest-two criterion must FAIL, i.e. the closest
        # other site must be strictly closer than the pair (squared-distance margin).
        dro2 = ((SJL[q][0] - po[0]) ** 2 + (SJL[q][1] - po[1]) ** 2).v
        v_ = EH(dro2)
        dmin_other = v_ if dmin_other is None else min(dmin_other, v_)
    ro2 = ((SJL[k][0] - po[0]) ** 2 + (SJL[k][1] - po[1]) ** 2).v
    f_ = EL(ro2) - dmin_other
    tie_fail = f_ if tie_fail is None else min(tie_fail, f_)
    # A2 (stress): the two radical-line intersections are separated
    dsep = ((p[0] - po[0]) ** 2 + (p[1] - po[1]) ** 2).v
    tie_sep = EL(dsep) if tie_sep is None else min(tie_sep, EL(dsep))
    Bk = (mp.iv.cos(thiv[k] + akiv[k]), mp.iv.sin(thiv[k] + akiv[k]))
    tie_id.append(max(abs(EH((p[0] - Bk[0]).v)), abs(EH((p[1] - Bk[1]).v)),
                      abs(EL((p[0] - Bk[0]).v)), abs(EL((p[1] - Bk[1]).v))))
say('     tie interface: min (other-site dist^2 - f^2) >= %.3e > 0 : %s ; max |p - B_k| <= %.2e'
    % (tie_min, bool(tie_min > 0), max(tie_id)))
say('     tie interface A2/A4: inf |p* - p_other|^2 >= %.6f > 0 ; other-branch nearest-pair failure'
    ' margin >= %.6f > 0 : %s' % (tie_sep, tie_fail, bool(tie_sep > 0 and tie_fail > 0)))
wd = max(float(EH(A8[i, j]) - EL(A8[i, j])) for i in range(8) for j in range(11))
say('     entry widths: max %.3e' % wd)

# --------------------------------------------------------------------------- witness minor
COLS = [2, 3, 4, 5, 7, 8, 9, 10]
FREE = [j for j in range(11) if j not in COLS]
M8 = mp.iv.matrix(8, 8)
for i in range(8):
    for j in range(8):
        M8[i, j] = A8[i, COLS[j]]
Mc = np.array([[float(EM(M8[i, j])) for j in range(8)] for i in range(8)])
# fixed pivot row order from the centre; row permutation applied consistently to M and every RHS
order, cur = [], Mc.copy()
for c in range(7):
    piv = max(range(c, 8), key=lambda r: abs(cur[r, c]))
    order.append(piv)
    cur[[c, piv], :] = cur[[piv, c], :]
    for r in range(c + 1, 8):
        fac = cur[r, c] / cur[c, c]
        cur[r, c:] -= fac * cur[c, c:]
order.append(7)
perm = list(range(8))
for c in range(7):
    if order[c] != c:
        perm[c], perm[order[c]] = perm[order[c]], perm[c]
nsign = sum(1 for c in range(7) if order[c] != c)
# rhs = A_anti restricted to the free columns (M X = A_free)
RHS = mp.iv.matrix(8, 3)
for i in range(8):
    for t, fc in enumerate(FREE):
        RHS[i, t] = A8[perm[i], fc]
MP = mp.iv.matrix(8, 8)
for i in range(8):
    for j in range(8):
        MP[i, j] = M8[perm[i], j]
# Gauss-Jordan with the fixed pivot order (interval arithmetic, outward rounding).
# Guards (stress audit F-now-2): every pivot must exclude 0 and be finite, otherwise an interval
# division can return +-inf and a det-product sign test would pass falsely.
PIVOT_BAD, PIVOT_MIN = [], None
for c in range(8):
    pv = MP[c, c]
    p_lo, p_hi = EL(pv), EH(pv)
    ok_p = mp.isfinite(p_lo) and mp.isfinite(p_hi) and p_lo * p_hi > 0
    if not ok_p:
        PIVOT_BAD.append(c)
    else:
        m_ = min(abs(p_lo), abs(p_hi))
        PIVOT_MIN = m_ if PIVOT_MIN is None else min(PIVOT_MIN, m_)
    for r in range(8):
        if r == c:
            continue
        fac = MP[r, c] / pv
        for cc in range(8):
            MP[r, cc] = MP[r, cc] - fac * MP[c, cc]
        for t in range(3):
            RHS[r, t] = RHS[r, t] - fac * RHS[c, t]
X = mp.iv.matrix(8, 3)
for i in range(8):
    for t in range(3):
        X[i, t] = RHS[i, t] / MP[i, i]
det_iv = I1
for c in range(8):
    det_iv = det_iv * MP[c, c]
if nsign % 2:
    det_iv = -det_iv
DET_FIN = bool(mp.isfinite(EL(det_iv)) and mp.isfinite(EH(det_iv)))
DET_OK = bool(not PIVOT_BAD and DET_FIN and EL(det_iv) * EH(det_iv) > 0)
say('[A3] pivot guards: bad pivots %s ; min |pivot| >= %s ; det finite %s'
    % (PIVOT_BAD, ('%.6e' % PIVOT_MIN) if PIVOT_MIN is not None else 'n/a', DET_FIN))
say('     witness minor cols %s : interval det = [%s, %s] non-zero = %s'
    % (COLS, mp.nstr(EL(det_iv), 12), mp.nstr(EH(det_iv), 12), DET_OK))

# --------------------------------------------------------------------------- explicit kernel (from the Gauss-Jordan solve, no SVD)
KV = []
for t, fc in enumerate(FREE):
    v = mp.iv.matrix(11, 1)
    for i in range(8):
        v[COLS[i], 0] = -X[i, t]
    v[fc, 0] = I1
    KV.append(v)
resk = mp.mpf(0)
for t in range(3):
    for i in range(8):
        acc = I0
        for j in range(11):
            acc = acc + A8[i, j] * KV[t][j, 0]
        resk = max(resk, max(abs(EL(acc)), abs(EH(acc))))
say('     kernel dim 3 (free columns %s); max |A_anti k| <= %.3e (interval residual, contains 0)'
    % (FREE, resk))

# rotation direction (purely anti at symmetric configurations); coefficients in the integer basis
# are computed with the metric: rot_a = (BA^T BA)^{-1} BA^T rot22
rot22 = []
for i in range(11):
    rot22.append(-SJ[2 * i + 1].v)
    rot22.append(SJ[2 * i].v)
gdiag = [2] * 8 + [1, 1, 1]                      # BA^T BA is diagonal (paired |.|^2=2, self/hub =1)
rot_a = mp.iv.matrix(11, 1)
for c in range(11):
    acc = I0
    for j in range(N):
        acc = acc + ivp(BA[c][j]) * rot22[j]
    rot_a[c, 0] = acc * ivp(mp.mpf(1) / gdiag[c])

# --------------------------------------------------------------------------- weights from stress (import-safe module)
sys.path.insert(0, str(STRESS))
import weights_interface as WI            # noqa: E402  (read-only, no side effects)

WW = WI.physical_weights()
w_face = [None] * 9
for mine, thr in FACE_MAP.items():
    w_face[mine] = WW['face_weight_9'][thr]
W = list(w_face) + list(WW['tie_weight'])
wsum = I0
for w in W:
    wsum = wsum + w
wmin = min(EL(w) for w in W)
say('[A4] weights from r20-stress/weights_interface.py:physical_weights() (read-only)')
say('     all 18 strictly positive: %s (min lower endpoint %.12f)'
    % (all(EL(w) > 0 for w in W), wmin))
say('     sum of the 18 interval weights = [%s, %s] contains 1: %s'
    % (mp.nstr(EL(wsum), 20), mp.nstr(EH(wsum), 20), bool(EL(wsum) <= 1 <= EH(wsum))))
HASHES = {}
try:
    HASHES = json.loads((STRESS / 'out' / 'weights_interface_hashes.json').read_text(encoding='utf-8'))
except Exception as e:
    say('     (hashes file not read: %s)' % e)
lam_np = json.loads((P / 'r20_physical_kkt_kernel.json').read_text(encoding='utf-8'))['lambda']['values']
bad = [(i, lam_np[i], mp.nstr(EL(W[i]), 12), mp.nstr(EH(W[i]), 12)) for i in range(18)
       if not (EL(W[i]) - mp.mpf('1e-9') <= lam_np[i] <= EH(W[i]) + mp.mpf('1e-9'))]
say('     control: numeric Danskin lambda inside the interval weights: %s%s'
    % (not bad, '' if not bad else ' MISMATCH ' + str(bad[:5])))

# --------------------------------------------------------------------------- weighted eps-eps Hessian
Heps = []
for r in range(18):
    f = BR[r][2][1]
    H = mp.iv.matrix(11, 11)
    for a in range(11):
        for b in range(11):
            H[a, b] = f.h[NC + a, NC + b]
    Heps.append(H)
HW = mp.iv.matrix(11, 11)
for a in range(11):
    for b in range(11):
        acc = I0
        for r in range(18):
            acc = acc + W[r] * Heps[r][a, b]
        HW[a, b] = acc
say('[A5] weighted eps-eps Hessian assembled (18 branches x 11x11)')

# --------------------------------------------------------------------------- quotient + 2x2 bound
# anti basis is the INTEGER basis (entries +-1), so the Euclidean metric on the anti coordinates is
# the diagonal Gram GEPS = BA^T BA = diag(2,...,2,1,1,1) : keep it explicitly in every inner product.
GEPS = mp.iv.matrix(11, 11)
for c1 in range(11):
    for c2 in range(11):
        acc = I0
        for a in range(N):
            acc = acc + ivp(BA[c1][a] * BA[c2][a])
        GEPS[c1, c2] = acc
gs = [EL(GEPS[c, c]) for c in range(11)]
say('     Gram of the integer anti basis: diag %s (off-diagonal max %.1e)'
    % ([int(x) for x in gs], max(abs(EL(GEPS[c1, c2])) for c1 in range(11) for c2 in range(11) if c1 != c2)))
G3 = mp.iv.matrix(3, 3)
B3 = mp.iv.matrix(3, 3)
for a in range(3):
    for b in range(3):
        acc = I0
        for j1 in range(11):
            for j2 in range(11):
                acc = acc + KV[a][j1, 0] * GEPS[j1, j2] * KV[b][j2, 0]
        G3[a, b] = acc
        acc = I0
        for j1 in range(11):
            for j2 in range(11):
                acc = acc + KV[a][j1, 0] * HW[j1, j2] * KV[b][j2, 0]
        B3[a, b] = acc
# coefficients of the rotation in the 3D kernel basis: exactly c*_t = rot_a[FREE[t]]
# (because the free block of every KV is the identity: KV[t][FREE[s]] = delta_ts).
cstar = [rot_a[FREE[t], 0] for t in range(3)]
say('     rotation kernel coefficients c* = rot_a[FREE] = [%s, %s, %s]'
    % tuple(mp.nstr(cstar[t], 14) for t in range(3)))
KTr = mp.iv.matrix(3, 1)
for a in range(3):
    KTr[a, 0] = cstar[a]
# quotient constraint for the diagnostic pencil:  u^T (G3 c*) = 0
G3c = mp.iv.matrix(3, 1)
for a in range(3):
    acc = I0
    for j in range(3):
        acc = acc + G3[a, j] * cstar[j]
    G3c[a, 0] = acc
say('     (diagnostic) quotient constraint G3 c* = [%s, %s, %s]'
    % tuple(mp.nstr(G3c[i, 0], 12) for i in range(3)))
# U (3x2) with (G3 c*)^T U = 0 : u1 = (l2, -l1, 0), u2 = (l3, 0, -l1)
l1, l2, l3 = G3c[0, 0], G3c[1, 0], G3c[2, 0]
U = mp.iv.matrix(3, 2)
U[0, 0] = l2; U[1, 0] = -l1; U[2, 0] = I0
U[0, 1] = l3; U[1, 1] = I0; U[2, 1] = -l1
B2 = mp.iv.matrix(2, 2)
G2 = mp.iv.matrix(2, 2)
for a in range(2):
    for b in range(2):
        acc = I0
        for i in range(3):
            for j in range(3):
                acc = acc + U[i, a] * B3[i, j] * U[j, b]
        B2[a, b] = acc
        acc = I0
        for i in range(3):
            for j in range(3):
                acc = acc + U[i, a] * G3[i, j] * U[j, b]
        G2[a, b] = acc


def lo(x):
    return EL(x)


def hi(x):
    return EH(x)


b11, b22 = lo(B2[0, 0]), lo(B2[1, 1])
b12 = max(abs(lo(B2[0, 1])), abs(hi(B2[0, 1])))
blo = (b11 + b22) / 2 - mp.sqrt(((b11 - b22) / 2) ** 2 + b12 ** 2)
gmax = hi(G2[0, 0]) + hi(G2[1, 1])
say('[A6] diagnostic only (not the certificate): eigenvalue bound lambda_min(B2) >= %s / tr(G2) <= %s'
    % (mp.nstr(blo, 18), mp.nstr(gmax, 18)))
say('     (eigenvalue/Gram arithmetic with rounded mp endpoints is a diagnostic; the certificate is [A7])')

# ---- [A7] lead's shortest quotient certificate: explicit rotation-free complement, Sylvester on
# interval endpoints only (no eigenvalues, no metric arithmetic for the claim).
# j* is selected from the 3D KERNEL coefficients c* = rot_a[FREE] (stress audit F-now-1).
cabs = [max(abs(lo(cstar[t])), abs(hi(cstar[t]))) for t in range(3)]
jstar = int(np.argmax(cabs))
say('[A7] rotation kernel coefficients |c*| = %s ; j* = %d (index of the largest);'
    % (' '.join('%.6f' % x for x in cabs), jstar))
c_lo, c_hi = lo(cstar[jstar]), hi(cstar[jstar])
TRANS_OK = bool((c_lo > 0) or (c_hi < 0))          # exact sign test: 0 not in the interval
rot_marg = min(abs(c_lo), abs(c_hi))
say('     c*[j*] interval = [%s, %s] ; 0 not contained (sign test) : %s ; margin >= %.6e'
    % (mp.nstr(c_lo, 16), mp.nstr(c_hi, 16), TRANS_OK, rot_marg))
comp = [i for i in range(3) if i != jstar]
for (a_, b_) in ((comp[0], comp[1]), (comp[1], comp[0])):
    Baa, Bbb, Bab, Bba = B3[a_, a_], B3[b_, b_], B3[a_, b_], B3[b_, a_]
    B12m = max(abs(lo(Bab)), abs(hi(Bab)), abs(lo(Bba)), abs(hi(Bba)))
    detl = mp.iv.mpf(lo(Baa)) * mp.iv.mpf(lo(Bbb)) - mp.iv.mpf(B12m) ** 2
    fin = bool(mp.isfinite(EL(detl)) and mp.isfinite(EH(detl)) and mp.isfinite(lo(Baa)) and mp.isfinite(hi(Baa)))
    ok_det = bool(fin and EL(detl) > 0)
    ok_lead = bool(fin and lo(Baa) > 0)
    say('     complement basis (KV[%d], KV[%d]) : B11 = [%s, %s] > 0 : %s ; |B12| <= %.6e ; finite %s'
        % (a_, b_, mp.nstr(lo(Baa), 12), mp.nstr(hi(Baa), 12), ok_lead, B12m, fin))
    say('        det >= [%s, %s] > 0 : %s  ->  2x2 form PD on this complement: %s'
        % (mp.nstr(EL(detl), 12), mp.nstr(EH(detl), 12), ok_det, bool(ok_det and ok_lead)))
    if (a_, b_) == (comp[0], comp[1]):
        VERDICT = bool(ok_det and ok_lead)
        DETL = detl
        B11L = Baa
# merged verdict (lead): rank witness + pivot guards + transversality + Sylvester, not PD alone
VERDICT = bool(DET_OK and not PIVOT_BAD and TRANS_OK and VERDICT)
say('     MERGED VERDICT (minor 0-not-in-det: %s ; pivots ok: %s ; transversality: %s ; Sylvester: %s) = %s'
    % (DET_OK, not PIVOT_BAD, TRANS_OK, bool(EL(DETL) > 0 and lo(B11L) > 0), VERDICT))
say('     VERDICT (anti quotient PD on the explicit rotation-free 2D complement, whole box): %s'
    % VERDICT)

# centre control: point-mode generalized eigenvalues vs the numeric run
if POINT:
    B2n = np.array([[float(EM(B2[i, j])) for j in range(2)] for i in range(2)])
    G2n = np.array([[float(EM(G2[i, j])) for j in range(2)] for i in range(2)])
    ev = sla.eigh(B2n, G2n)[0]
    say('     control (point mode): generalized eigenvalues %s (numeric run: 0.16490, 0.25496)'
        % ' '.join('%.6f' % x for x in ev))
    # independent route: 22D kernel -> orthonormal quotient -> restricted form via the eps-block
    BAn = np.array([[float(BA[j][i]) for j in range(11)] for i in range(N)])
    rot22n = np.array([float(EM(x)) for x in rot22])
    rot22n = rot22n / np.linalg.norm(rot22n)
    KVn = [np.array([float(EM(KV[t][i, 0])) for i in range(11)]) for t in range(3)]
    KV22 = [BAn @ v for v in KVn]
    Q = []
    for v in KV22:
        w = v - (v @ rot22n) * rot22n
        for cq in Q:
            w = w - (cq @ w) * cq
        if np.linalg.norm(w) > 1e-9:
            Q.append(w / np.linalg.norm(w))
    HWn = np.array([[float(EM(HW[i, j])) for j in range(11)] for i in range(11)])
    coef = [np.linalg.lstsq(BAn, q, rcond=None)[0] for q in Q]
    Bq = np.array([[c1 @ HWn @ c2 for c2 in coef] for c1 in coef])
    say('     control 2 (22D orthonormal quotient, dim %d): eigenvalues %s'
        % (len(Q), ' '.join('%.6f' % x for x in np.linalg.eigvalsh(Bq))))
    B3n = np.array([[float(EM(B3[i, j])) for j in range(3)] for i in range(3)])
    G3n = np.array([[float(EM(G3[i, j])) for j in range(3)] for i in range(3)])
    say('     control 3 (3D kernel pencil (B3,G3), symmetric generalized solver): %s'
        % ' '.join('%.6f' % x for x in sla.eigh(B3n, G3n)[0]))
    Un = np.array([[float(EM(U[i, j])) for j in range(2)] for i in range(3)])
    hwr = [sum(HW[i, j] * rot_a[j, 0] for j in range(11)) for i in range(11)]
    b3c = [sum(B3[i, j] * cstar[j] for j in range(3)) for i in range(3)]
    say('     diag: max |HW rot_a| = %.3e ; max |B3 c*| = %.3e ; c* = %s'
        % (max(max(abs(EL(x)), abs(EH(x))) for x in hwr),
           max(max(abs(EL(x)), abs(EH(x))) for x in b3c),
           ' '.join('%.6f' % float(EM(cstar[j])) for j in range(3))))
    Uc = Un / np.linalg.norm(Un, axis=0)
    Qc = np.array([np.linalg.lstsq(np.array([[float(EM(KV[t][i, 0])) for t in range(3)] for i in range(11)]),
                                   np.linalg.lstsq(BAn, q, rcond=None)[0], rcond=None)[0] for q in Q])
    say('     subspace: coefficient reps of the 22D quotient Q = %s'
        % str(np.round(Qc, 5).tolist()))
    say('     check Qc G3 Qc^T (should be I): %s' % str(np.round(Qc @ G3n @ Qc.T, 6).tolist()))
    say('     check Qc B3 Qc^T (should equal the control-2 form %s): %s'
        % (str(np.round(Bq, 6).tolist()), str(np.round(Qc @ B3n @ Qc.T, 6).tolist())))
    say('     control 4 (eigenvectors of the 3D pencil, coefficient space): %s'
        % str(np.round(np.linalg.eig(np.linalg.solve(G3n, B3n))[1], 4).tolist()))
    say('     subspace check |proj_U(x)| for the two positive eigenvectors: %s'
        % str([round(float(np.linalg.norm(Un @ np.linalg.lstsq(Un, v, rcond=None)[0] - v)), 6) for v in
               np.linalg.eig(np.linalg.solve(G3n, B3n))[1][:, 1:] .T]))

OUT = {
    'mode': 'point' if POINT else 'box',
    'box_radius_hex': CERT['certificate']['radius_hex'],
    'weight_source': 'r20-stress/weights_interface.py::physical_weights()  (hashes below)',
    'source_hashes': HASHES,
    'weight_sum_interval': [mp.nstr(EL(wsum), 24), mp.nstr(EH(wsum), 24)],
    'weight_sum_contains_one': bool(EL(wsum) <= 1 <= EH(wsum)),
    'all_weights_strictly_positive': bool(all(EL(w) > 0 for w in W)),
    'numeric_lambda_inside_weights': (not bad),
    'minor_cols': COLS, 'minor_det': [mp.nstr(EL(det_iv), 24), mp.nstr(EH(det_iv), 24)],
    'minor_nonzero': DET_OK,
    'pivots': {'bad': PIVOT_BAD, 'min_abs_pivot': (mp.nstr(PIVOT_MIN, 12) if PIVOT_MIN is not None else None),
               'det_finite': DET_FIN},
    'kernel_free_cols': FREE, 'kernel_residual_bound': mp.nstr(resk, 8),
    # full interval endpoints of the quotient pencil (basis Gram / lambda matrix difference):
    # with these the safe bound lambda_min(B,G) >= det(B)_lo/(tr(B)_hi tr(G)_hi) is recomputable
    # without hand-copied endpoints.
    'B2_entries': [[[mp.nstr(EL(B2[i, j]), 22), mp.nstr(EH(B2[i, j]), 22)] for j in range(2)] for i in range(2)],
    'G2_entries': [[[mp.nstr(EL(G2[i, j]), 22), mp.nstr(EH(G2[i, j]), 22)] for j in range(2)] for i in range(2)],
    'B_PD_sylvester': {'B11_lower': mp.nstr(EL(B2[0, 0]), 22), 'B22_lower': mp.nstr(EL(B2[1, 1]), 22),
                       'det_lower': mp.nstr(EL(B2[0, 0] * B2[1, 1] - B2[0, 1] * B2[1, 0]), 22)},
    'B3_entries': [[[mp.nstr(EL(B3[i, j]), 22), mp.nstr(EH(B3[i, j]), 22)] for j in range(3)] for i in range(3)],
    'G3_entries': [[[mp.nstr(EL(G3[i, j]), 22), mp.nstr(EH(G3[i, j]), 22)] for j in range(3)] for i in range(3)],
    'tie_interface': {'A1_max_abs_p_minus_Bk': float(max(tie_id)),
                      'A3_min_othersite_sq_margin': mp.nstr(tie_min, 12),
                      'A2_min_intersection_separation_sq': mp.nstr(tie_sep, 12),
                      'A4_other_branch_failure_margin': mp.nstr(tie_fail, 12),
                      'note': 'A3/A4 are squared-distance margins; independent stress audit '
                              'audit_tie_branch_identity.json (A2 >= 3.78374) agrees'},
    'rotation_kernel_coeffs': [mp.nstr(cstar[t], 20) for t in range(3)],
    'rotation_index_jstar': jstar,
    'rotation_jstar_margin': mp.nstr(rot_marg, 20),
    'certificate': {
        'name': 'explicit rotation-free complement + Sylvester on interval endpoints',
        'complement_basis': [int(comp[0]), int(comp[1])],
        'B11_interval': [mp.nstr(lo(B11L), 20), mp.nstr(hi(B11L), 20)],
        'det_interval': [mp.nstr(EL(DETL), 20), mp.nstr(EH(DETL), 20)],
        'det_positive': bool(EL(DETL) > 0),
        'B11_positive': bool(lo(B11L) > 0),
        'anti_quotient_PD': VERDICT,
    },
    'diagnostics': {'eigen_bound_blo': mp.nstr(blo, 20), 'trace_G2_upper': mp.nstr(gmax, 20),
                    'note': 'eigenvalue/Gram arithmetic with rounded mp endpoints: diagnostic only'},
    'repro': 'py -3 -B -X utf8 r20_anti_block_interval.py   (R20_POINT=1 for the point control)',
}
name = 'r20_anti_block_interval_point.json' if POINT else 'r20_anti_block_interval.json'
(P / name).write_text(json.dumps(OUT, indent=2))
(P / (name.replace('.json', '.log'))).write_text('\n'.join(REP) + '\n')
say('\nwritten %s' % name)
