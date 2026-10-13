"""r20-rigidity: interval lower bound for sigma_17(J) from a 17x17 square minor of the physical full J.

Method (lead, 2026-09-25): for any square submatrix M of J,  sigma_min(M) >= 1/||M^{-1}||_F  (no sqrt;
the sqrt appears only in the Gram form).  Since the rotation lies in ker J, any nonzero singular value
of J agrees with the corresponding value of the physical J restricted to the rotation slice, so a
17x17 minor of the full 18x22 physical J gives  sigma_17(J) >= sigma_min(M) >= 1/||M^{-1}||_F.

Implementation: interval enclosures of the 18 branch gradient rows over the 22D hull box of the lead's
chart image (a superset of the symmetric slice, hence conservative); interval Gauss-Jordan inversion of
the chosen 17x17 minor with pivot guards; Frobenius upper bound from the entry magnitudes.

NOT a certificate for mu yet: it yields the interval input sigma_min >= s_lo, which is to be inserted
into mu = w_min * sigma/2 (the chain's accepted margin).  Writes r20_anti_sigma_interval.json/.log.
"""
import json, itertools
from pathlib import Path
import mpmath as mp

P = Path(__file__).parent
LEAD = P.parent / 'lead'
mp.mp.dps = 40
mp.iv.dps = 40
N, NC = 22, 7
REP = []


def say(s):
    print(s, flush=True)
    REP.append(s)


IV = type(mp.iv.mpf(0))
I0, I1 = mp.iv.mpf(0), mp.iv.mpf(1)


def EL(x):
    return mp.mpf(x.a)


def EH(x):
    return mp.mpf(x.b)


class J(object):
    __slots__ = ('v', 'g')

    def __init__(self, v, g=None):
        self.v = v
        self.g = g if g is not None else mp.iv.matrix(N, 1)

    @staticmethod
    def var(i, v):
        g = mp.iv.matrix(N, 1)
        g[i, 0] = I1
        return J(v, g)

    @staticmethod
    def const(v):
        return J(v if isinstance(v, IV) else mp.iv.mpf(mp.mpf(v)), mp.iv.matrix(N, 1))

    def __add__(self, o):
        o = _j(o)
        return J(self.v + o.v, self.g + o.g)

    __radd__ = __add__

    def __neg__(self):
        return J(-self.v, -self.g)

    def __sub__(self, o):
        return self + (-_j(o))

    def __rsub__(self, o):
        return _j(o) + (-self)

    def __mul__(self, o):
        o = _j(o)
        return J(self.v * o.v, self.v * o.g + o.v * self.g)

    __rmul__ = __mul__

    def __truediv__(self, o):
        return self * _j(o)._recip()

    def _recip(self):
        r = I1 / self.v
        return J(r, -self.g * r * r)

    def _sqrt(self):
        s = mp.iv.sqrt(self.v)
        return J(s, self.g / (2 * s))


def _j(x):
    return x if isinstance(x, J) else J.const(x)


def SQ(x):
    return x._sqrt() if isinstance(x, J) else mp.iv.sqrt(x) if isinstance(x, IV) else mp.sqrt(x)


def face(S, tri):
    a, b, c = tri
    ca, cb, cc = S[a], S[b], S[c]
    g1x, g1y = ca[0] - cb[0], ca[1] - cb[1]
    g2x, g2y = ca[0] - cc[0], ca[1] - cc[1]
    d = g1x * g2y - g1y * g2x
    b1 = -(g1x * g1x + g1y * g1y) / 2
    b2 = -(g2x * g2x + g2y * g2y) / 2
    wx = (b1 * g2y - b2 * g1y) / d
    wy = (g1x * b2 - g2x * b1) / d
    return (ca[0] + wx, ca[1] + wy), SQ(wx * wx + wy * wy)


def tie(S, k, sgn):
    ca, cb = S[k], S[(k + 1) % 9]
    dx, dy = cb[0] - ca[0], cb[1] - ca[1]
    D = dx * dx + dy * dy
    kap = ((cb[0] * cb[0] + cb[1] * cb[1]) - (ca[0] * ca[0] + ca[1] * ca[1])) / 2
    dl = SQ(D)
    a0x, a0y = (kap / D) * dx, (kap / D) * dy
    t = sgn * SQ(1 - (a0x * a0x + a0y * a0y))
    p = (a0x + t * (-dy / dl), a0y + t * (dx / dl))
    wx, wy = p[0] - ca[0], p[1] - ca[1]
    return p, SQ(wx * wx + wy * wy)


FACES = [(1, 2, 10), (2, 3, 9), (3, 4, 9), (4, 5, 9), (5, 6, 9), (6, 7, 10), (8, 0, 10),
         (2, 9, 10), (6, 9, 10)]
CERT = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text(encoding='utf-8'))
RAD_ = float.fromhex(CERT['certificate']['radius_hex'])
CHV = [float.fromhex(v) for v in CERT['certificate']['center_hex'][:7]]
Z = [mp.iv.mpf(CHV[i]) + mp.iv.mpf([-RAD_, RAD_]) for i in range(7)]
a0, a1, a2, a3, y0, y1, R = Z
a4 = mp.iv.pi - 2 * (a0 + a1 + a2 + a3)
ak = [a0, a1, a2, a3, a4, a3, a2, a1, a0]
th = [mp.iv.mpf(0)] * 9
for k in range(5, 9):
    th[k] = th[k - 1] + ak[k - 1] + ak[k]
for k in range(3, -1, -1):
    th[k] = th[k + 1] - (ak[k] + ak[k + 1])
rho = [mp.iv.cos(ak[k]) - mp.iv.sqrt(R * R - mp.iv.sin(ak[k]) ** 2) for k in range(9)]
C = [(rho[k] * mp.iv.cos(th[k]), rho[k] * mp.iv.sin(th[k])) for k in range(9)]
SIV = C + [(y0, mp.iv.mpf(0)), (y1, mp.iv.mpf(0))]
BX = []
for s in SIV:
    BX.append(mp.iv.mpf([min(EL(s[0]), EH(s[0])), max(EL(s[0]), EH(s[0]))]))
    BX.append(mp.iv.mpf([min(EL(s[1]), EH(s[1])), max(EL(s[1]), EH(s[1]))]))
say('[S0] 22D hull box of the chart image (superset of the symmetric slice); widths max %.2e'
    % max(float(EH(b) - EL(b)) for b in BX))

# centre tie signs (numeric choice)
mp.mp.dps = 40


def chartf(z):
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


ROOT = [mp.mpf(s) for s in CERT['numeric_root'][:7]]
S0 = chartf(ROOT)
TP = {}
for k in range(9):
    for sgn in (1, -1):
        p, f = tie(S0, k, sgn)
        ds = sorted((mp.sqrt((p[0] - s[0]) ** 2 + (p[1] - s[1]) ** 2), i) for i, s in enumerate(S0))
        if set(i for _, i in ds[:2]) == {k, (k + 1) % 9}:
            TP[k] = sgn
            break
SJ = [(J.var(2 * i, BX[2 * i]), J.var(2 * i + 1, BX[2 * i + 1])) for i in range(11)]
BR = [face(SJ, FACES[i]) for i in range(9)] + [tie(SJ, k, TP[k]) for k in range(9)]
Jm = mp.iv.matrix(18, N)
for r, (p, f) in enumerate(BR):
    for a in range(N):
        Jm[r, a] = f.g[a, 0]
say('[S1] interval 18x22 physical gradient map assembled (all directions, hull box)')
# convenience export: exact-formula J at the box centre (the interval enclosures above are the
# bearing object; this npy is for other members' independent cross-checks)
import hashlib
import numpy as _np
_np.save(P / 'r20_J_exact_18x22.npy',
         _np.array([[float((EL(Jm[r, a]) + EH(Jm[r, a])) / 2) for a in range(N)] for r in range(18)]))
say('     exported r20_J_exact_18x22.npy (sha256 %s)'
    % hashlib.sha256((P / 'r20_J_exact_18x22.npy').read_bytes()).hexdigest()[:32])

# centre (numeric) matrix for the greedy minor selection and the pivot order
Jc = mp.matrix(18, N)
for r in range(18):
    for a in range(N):
        Jc[r, a] = (EL(Jm[r, a]) + EH(Jm[r, a])) / 2
import numpy as np
Jnp = np.array([[float(Jc[r, a]) for a in range(N)] for r in range(18)])
rows, cols = [], []
for i in range(18):
    if len(rows) < 17 and np.linalg.matrix_rank(Jnp[rows + [i], :], tol=1e-8) > len(rows):
        rows.append(i)
for j in range(N):
    if len(cols) < 17 and np.linalg.matrix_rank(Jnp[np.ix_(rows, cols + [j])], tol=1e-8) > len(cols):
        cols.append(j)
say('[S2] 17x17 minor: rows %s ; cols %s' % (rows, cols))
M = mp.iv.matrix(17, 17)
for i, r in enumerate(rows):
    for j, c in enumerate(cols):
        M[i, j] = Jm[r, c]
Mc = np.array([[float((EL(M[i, j]) + EH(M[i, j])) / 2) for j in range(17)] for i in range(17)])
# pivot order from the centre
order, cur = [], Mc.copy()
for c in range(16):
    piv = max(range(c, 17), key=lambda r: abs(cur[r, c]))
    order.append(piv)
    cur[[c, piv], :] = cur[[piv, c], :]
    for r in range(c + 1, 17):
        fac = cur[r, c] / cur[c, c]
        cur[r, c:] -= fac * cur[c, c:]
order.append(16)
perm = list(range(17))
for c in range(16):
    if order[c] != c:
        perm[c], perm[order[c]] = perm[order[c]], perm[c]
MP = mp.iv.matrix(17, 17)
for i in range(17):
    for j in range(17):
        MP[i, j] = M[perm[i], j]
RHS = mp.iv.matrix(17, 17)
for i in range(17):
    for j in range(17):
        RHS[i, j] = I1 if perm[i] == j else I0
bad, pmin = [], None
for c in range(17):
    pv = MP[c, c]
    p_lo, p_hi = EL(pv), EH(pv)
    if not (mp.isfinite(p_lo) and mp.isfinite(p_hi) and p_lo * p_hi > 0):
        bad.append(c)
    else:
        m_ = min(abs(p_lo), abs(p_hi))
        pmin = m_ if pmin is None else min(pmin, m_)
    for r in range(17):
        if r == c:
            continue
        fac = MP[r, c] / pv
        for cc in range(17):
            MP[r, cc] = MP[r, cc] - fac * MP[c, cc]
        for t in range(17):
            RHS[r, t] = RHS[r, t] - fac * RHS[c, t]
INV = mp.iv.matrix(17, 17)
for i in range(17):
    for j in range(17):
        INV[i, j] = RHS[i, j] / MP[i, i]
fro2 = I0
fin_bad = 0
for i in range(17):
    for j in range(17):
        e = INV[i, j]
        if not (mp.isfinite(EL(e)) and mp.isfinite(EH(e))):
            fin_bad += 1
        fro2 = fro2 + mp.iv.mpf([min(abs(EL(e)), 0) ** 2, max(abs(EL(e)), abs(EH(e))) ** 2])
fro_ub = mp.sqrt(EH(fro2))
sig_lo = 1 / fro_ub if fro_ub > 0 else mp.mpf(0)
say('[S3] interval inverse: bad pivots %s ; min|pivot| >= %s ; non-finite entries %d'
    % (bad, ('%.4e' % pmin) if pmin is not None else 'n/a', fin_bad))
say('     ||M^{-1}||_F upper bound = %.6e  =>  sigma_min(M) >= %.6e  =>  sigma_17(J) >= %.6e'
    % (fro_ub, sig_lo, sig_lo))
w_min = mp.mpf('0.0098946876')          # stress interface lower endpoint
mu_lo = w_min * sig_lo / 2              # chain's accepted margin mu = w_min sigma / 2
say('[S4] chain margin candidate: mu = w_min * sigma/2 >= %.6e (conditional: w_min from the stress '
    'interface, sigma now an interval lower bound from the 17x17 minor)' % mu_lo)

OUT = {'rows': rows, 'cols': cols, 'bad_pivots': bad, 'min_abs_pivot': (mp.nstr(pmin, 12) if pmin else None),
       'nonfinite_entries': fin_bad, 'inv_fro_upper': mp.nstr(fro_ub, 20),
       'sigma17_lower': mp.nstr(sig_lo, 20), 'w_min': mp.nstr(w_min, 12), 'mu_lower_candidate': mp.nstr(mu_lo, 20),
       'status': 'interval lower bound from a square minor of the physical J; mu candidate uses the '
                 'stress w_min endpoint; no claim added',
       'repro': 'py -3 -B -X utf8 r20_anti_sigma_interval.py'}
(P / 'r20_anti_sigma_interval.json').write_text(json.dumps(OUT, indent=2))
(P / 'r20_anti_sigma_interval.log').write_text('\n'.join(REP) + '\n')
say('\nwritten r20_anti_sigma_interval.json / .log')
