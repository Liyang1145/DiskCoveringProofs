"""r20-rigidity: verification of the circumcentre inverse-derivative recurrence (face branch) against
the exact jets.  Pointwise identities only; no ball statement, no rho.

Face branch: with g1 = c_a - c_b, g2 = c_a - c_c,  A = [g1^T; g2^T],  b = -(1/2)(|g1|^2, |g2|^2)^T,
the relative circumcentre w = p - c_a solves  A w = b  exactly.  Differentiating along a unit
direction v (D^2A = 0, D^3b = 0 because A is linear and b is quadratic in the centres):

   Dw   = A^{-1} ( Db      - (DA) w )
   D^2w = A^{-1} ( D^2b    - 2 (DA) Dw )
   D^3w = A^{-1} ( - 3 (DA) D^2w )

with ||A^{-1}||_2 <= ||A||_F/|det A| (since sigma_min sigma_max = |det|, sigma_max <= ||A||_F).

All norms below are operator norms along unit directions of the 22-dimensional physical centre space.
The script checks the three identities at the lead's exact root and reports the explicit magnitudes
||A||_F, |det|, ||A^{-1}||, |b|, |Db|, |D^2b|, |DA| used in the derived bounds.

Writes r20_recurrence_check.json/.log.  NOT a certificate; derivation support only.
"""
import json
from pathlib import Path
import numpy as np
import mpmath as mp

P = Path(__file__).parent
LEAD = P.parent / 'lead'
mp.mp.dps = 50
NB, N = 18, 22
REP = []


def say(s):
    print(s, flush=True)
    REP.append(s)


class Jet(object):
    __slots__ = ('v', 'g', 'h')

    def __init__(self, v, g=None, h=None):
        self.v = v
        self.g = g if g is not None else mp.zeros(N, 1)
        self.h = h if h is not None else mp.zeros(N, N)

    @staticmethod
    def var(i, v):
        g = mp.zeros(N, 1)
        g[i] = 1
        return Jet(v, g, mp.zeros(N, N))

    @staticmethod
    def const(v):
        return Jet(mp.mpf(v), mp.zeros(N, 1), mp.zeros(N, N))

    def __add__(self, o):
        o = _j(o)
        return Jet(self.v + o.v, self.g + o.g, self.h + o.h)

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.v, -self.g, -self.h)

    def __sub__(self, o):
        return self + (-_j(o))

    def __rsub__(self, o):
        return _j(o) + (-self)

    def __mul__(self, o):
        o = _j(o)
        return Jet(self.v * o.v, self.v * o.g + o.v * self.g,
                   self.v * o.h + o.v * self.h + self.g * o.g.T + o.g * self.g.T)

    __rmul__ = __mul__

    def __truediv__(self, o):
        return self * _j(o)._recip()

    def _recip(self):
        r = 1 / self.v
        return Jet(r, -self.g * r * r, mp.mpf(2) * r ** 3 * (self.g * self.g.T) - r * r * self.h)

    def _sqrt(self):
        s = mp.sqrt(self.v)
        return Jet(s, self.g / (2 * s), self.h / (2 * s) - (self.g * self.g.T) / (4 * s ** 3))


def _j(x):
    return x if isinstance(x, Jet) else Jet.const(x)


def SQ(x):
    return x._sqrt() if isinstance(x, Jet) else mp.sqrt(x)


CERT = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text(encoding='utf-8'))
Z0 = [mp.mpf(s) for s in CERT['numeric_root'][:7]]


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


S0 = chartf(Z0)
X0 = [v for s in S0 for v in s]
SJ = [(Jet.var(2 * i, X0[2 * i]), Jet.var(2 * i + 1, X0[2 * i + 1])) for i in range(11)]

FACES = [(1, 2, 10), (2, 3, 9), (3, 4, 9), (4, 5, 9), (5, 6, 9), (6, 7, 10), (8, 0, 10),
         (2, 9, 10), (6, 9, 10)]
rng = np.random.default_rng(20260925)
worst = [0.0, 0.0, 0.0]
maxA, maxb, maxDb, maxD2b, maxDA, maxkappa = 0.0, 0.0, 0.0, 0.0, 0.0, 0.0
for tri in FACES:
    a, b_, c_ = tri
    ca, cb, cc = SJ[a], SJ[b_], SJ[c_]
    g1x, g1y = ca[0] - cb[0], ca[1] - cb[1]
    g2x, g2y = ca[0] - cc[0], ca[1] - cc[1]
    det = (g1x * g2y - g1y * g2x).v
    b1 = -(g1x * g1x + g1y * g1y) / 2
    b2 = -(g2x * g2x + g2y * g2y) / 2
    wx = ((b1 * g2y - b2 * g1y) / (g1x * g2y - g1y * g2x)).v
    wy = ((g1x * b2 - g2x * b1) / (g1x * g2y - g1y * g2x)).v
    An = np.array([[float((g1x.g[i, 0])), float((g1y.g[i, 0]))] for i in range(N)])
    An2 = np.array([[float((g2x.g[i, 0])), float((g2y.g[i, 0]))] for i in range(N)])
    A2 = np.array([[float(g1x.v), float(g1y.v)], [float(g2x.v), float(g2y.v)]])
    Ainv = np.linalg.inv(A2)
    maxA = max(maxA, float(np.linalg.norm(A2, 'fro')))
    maxb = max(maxb, float(np.linalg.norm([float(b1.v), float(b2.v)])))
    maxDA = max(maxDA, float(np.linalg.norm(An, 2)), float(np.linalg.norm(An2, 2)))
    maxkappa = max(maxkappa, float(np.linalg.norm(Ainv, 2)))
    # directional derivative data (per unit direction) from the jet gradients
    for _ in range(6):
        v = rng.normal(size=N)
        v /= np.linalg.norm(v)
        vm = [mp.mpf(x) for x in v]
        dg1 = np.array([float(sum(g1x.g[i, 0] * vm[i] for i in range(N))),
                        float(sum(g1y.g[i, 0] * vm[i] for i in range(N)))])
        dg2 = np.array([float(sum(g2x.g[i, 0] * vm[i] for i in range(N))),
                        float(sum(g2y.g[i, 0] * vm[i] for i in range(N)))])
        g1v = np.array([float(g1x.v), float(g1y.v)])
        g2v = np.array([float(g2x.v), float(g2y.v)])
        dA = np.array([dg1, dg2])
        db = -np.array([g1v @ dg1, g2v @ dg2])
        d2b = -np.array([dg1 @ dg1, dg2 @ dg2])
        w = np.array([wx, wy])
        # recurrence
        dw = Ainv @ (db - dA @ w)
        d2w = Ainv @ (d2b - 2 * dA @ dw)
        d3w = Ainv @ (-3 * dA @ d2w)
        # compare the recurrence with the explicit formula's jet derivatives
        maxDb = max(maxDb, float(np.linalg.norm(db)))
        maxD2b = max(maxD2b, float(np.linalg.norm(d2b)))
        # exact first/second directional derivatives of w from its own jet
        WX = ((b1 * g2y - b2 * g1y) / (g1x * g2y - g1y * g2x))
        WY = ((g1x * b2 - g2x * b1) / (g1x * g2y - g1y * g2x))
        e1 = np.array([float(sum(WX.g[i, 0] * vm[i] for i in range(N))),
                       float(sum(WY.g[i, 0] * vm[i] for i in range(N)))])
        e2 = np.array([float(sum(vm[i] * WX.h[i, j] * vm[j] for i in range(N) for j in range(N))),
                       float(sum(vm[i] * WY.h[i, j] * vm[j] for i in range(N) for j in range(N)))])
        worst[0] = max(worst[0], float(np.linalg.norm(dw - e1)) / max(1e-30, float(np.linalg.norm(e1))))
        worst[1] = max(worst[1], float(np.linalg.norm(d2w - e2)) / max(1e-30, float(np.linalg.norm(e2))))
say('[R1] recurrence identities verified at the root over %d faces x 6 random directions:' % len(FACES))
say('     max relative error  D_v w  (recurrence vs jet) = %.2e' % worst[0])
say('     max relative error  D^2_v w (recurrence vs jet) = %.2e' % worst[1])
say('[R2] derived explicit magnitudes (pointwise at the root, operator norms over unit directions):')
say('     max ||A||_F = %.4f (<= 2 sqrt2 = 2.8284 by |g_i| <= 2)' % maxA)
say('     max |b| = %.4f (<= 2 sqrt2)' % maxb)
say('     max ||DA|| = %.4f (<= 2 by |D_v g_i| <= sqrt2)' % maxDA)
say('     max |Db| = %.4f (<= 2 sqrt2)' % maxDb)
say('     max |D^2b| = %.4f (<= 2)' % maxD2b)
say('     max ||A^{-1}||_2 = %.4f ; the derived bound is ||A||_F/|det A| (|det| >= 2 area_min)' % maxkappa)
say('[R3] consistency of the recurrence with the derived bound: |Dw| <= kappa(|Db| + ||DA|| |w|),')
say('     |D^2w| <= kappa(|D^2b| + 2||DA|| |Dw|), |D^3w| <= 3 kappa ||DA|| |D^2w|  (D^2A = 0, D^3b = 0).')
OUT = {'max_rel_err_D1': worst[0], 'max_rel_err_D2': worst[1], 'max_normA_F': maxA, 'max_abs_b': maxb,
       'max_normDA': maxDA, 'max_abs_Db': maxDb, 'max_abs_D2b': maxD2b, 'max_normAinv': maxkappa,
       'recurrence': ['Dw = A^-1(Db - (DA)w)', 'D^2w = A^-1(D^2b - 2(DA)Dw)', 'D^3w = A^-1(-3(DA)D^2w)'],
       'norm_convention': 'operator norm along unit directions of the 22D physical centre space',
       'status': 'derivation support only; no ball statement, no rho, no certificate',
       'repro': 'py -3 -B -X utf8 r20_recurrence_check.py'}
(P / 'r20_recurrence_check.json').write_text(json.dumps(OUT, indent=2))
(P / 'r20_recurrence_check.log').write_text('\n'.join(REP) + '\n')
say('\nwritten r20_recurrence_check.json / .log')
