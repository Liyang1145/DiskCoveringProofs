"""r20-rigidity (pilot): bounded numeric constants for the quantitative no-improvement neighbourhood.

Design: R20-QUANTITATIVE-NEIGHBORHOOD.md (P-quant).  Computes, at the exact C891/C892 root:
  mu  = transverse rate  min_{v in T^perp, |v|=1} max_i grad f_i . v            (LP / vertex enum)
  lam = weighted-Hessian margin on the centred kernel (numeric; certified blocks elsewhere)
  L2  = max_i ||H_i|| at the root (Hessian bound proxy)
  D3  = max over test directions of |v^T D^3 f_i(v,v,v)| (directional third derivatives,
        from exact-Hessian jets at x* +- h v; no finite differencing of the branch values)
and reports the implied thresholds rho_transverse = 2 mu / L2, rho_kernel = 3 lam / D3, the growth
constant c = min(mu/2, lam/4) and the boundary margin at the threshold.

Bounded pilot only: no 22Dx22Dx22D interval AD, no global claim, no re-run of the local certificates.
Writes r20_quant_pilot.json / .log.
"""
import json, itertools
from pathlib import Path
import numpy as np
import mpmath as mp

P = Path(__file__).parent
LEAD = P.parent / 'lead'
mp.mp.dps = 50
NB, N, NC = 18, 22, 7
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
    return (ca[0] + wx, ca[1] + wy), SQ(wx * wx + wy * wy)


def tie_branch(S, k, sgn):
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


def chart(z):
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


FACES = [(1, 2, 10), (2, 3, 9), (3, 4, 9), (4, 5, 9), (5, 6, 9), (6, 7, 10), (8, 0, 10),
         (2, 9, 10), (6, 9, 10), (0, 1, 10), (7, 8, 10)]
CERT = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text(encoding='utf-8'))
ROOT = [mp.mpf(s) for s in CERT['numeric_root']]
Z0 = ROOT[:NC]
S0 = chart(Z0)
X0 = [v for s in S0 for v in s]
TIEPICK = {}
for k in range(9):
    for sgn in (1, -1):
        p, f = tie_branch(S0, k, sgn)
        ds = sorted((mp.sqrt((p[0] - s[0]) ** 2 + (p[1] - s[1]) ** 2), i) for i, s in enumerate(S0))
        if set(i for _, i in ds[:2]) == {k, (k + 1) % 9}:
            TIEPICK[k] = sgn
            break
say('[Q0] anchor root, R* = %s ; tie signs %s' % (mp.nstr(Z0[6], 24), [TIEPICK[k] for k in range(9)]))

SJ = [(Jet.var(2 * i, X0[2 * i]), Jet.var(2 * i + 1, X0[2 * i + 1])) for i in range(11)]
BR = [face_branch(SJ, FACES[i]) for i in range(9)] + [tie_branch(SJ, k, TIEPICK[k]) for k in range(9)]
Jm = mp.matrix(NB, N)
Hm = []
for r, (p, f) in enumerate(BR):
    H = mp.matrix(N, N)
    for a in range(N):
        Jm[r, a] = f.g[a]
        for b in range(N):
            H[a, b] = f.h[a, b]
    Hm.append(H)
say('[Q1] exact-formula gradients/Hessians at the root (18 branches, dps=50)')

Jf = np.array([[float(Jm[r, a]) for a in range(N)] for r in range(NB)])
Hf = np.array([[[float(Hm[r][a, b]) for b in range(N)] for a in range(N)] for r in range(NB)])
u, s, vt = np.linalg.svd(Jf)
say('     sv(J): s_17 = %.6e  s_18 = %.3e' % (s[16], s[17]))
KER = [vt[17 + t] for t in range(5)]
KER = [k / np.linalg.norm(k) for k in KER]
resK = max(abs(sum(mp.mpf(Jf[r, a]) * mp.mpf(kk[a]) for a in range(N))) for r in range(NB) for kk in KER)
rot = np.array([x for i in range(11) for x in (-X0[2 * i + 1], X0[2 * i])], dtype=float)
rot /= np.linalg.norm(rot)
say('     kernel dim 5 (numeric), max |J k| at dps=50 = %.2e ; |J rot| = %.2e' % (resK, np.abs(Jf @ rot).max()))
lam_np = json.loads((P / 'r20_physical_kkt_kernel.json').read_text(encoding='utf-8'))['lambda']['values']
HW = np.einsum('i,iab->ab', np.array(lam_np), Hf)
Q = [k - (k @ rot) * rot for k in KER]
Q = [q for q in Q if np.linalg.norm(q) > 1e-9]
Qo = []
for q in Q:                                       # Gram-Schmidt -> orthonormal quotient basis
    w = q.copy()
    for c in Qo:
        w -= (c @ w) * c
    if np.linalg.norm(w) > 1e-9:
        Qo.append(w / np.linalg.norm(w))
Q = np.array(Qo)
ev = np.linalg.eigvalsh(Q @ HW @ Q.T)
lam_num = float(ev.min())
say('[Q2] weighted form on the centred kernel (orthonormal basis, numeric): eig %s ; min = %.6f'
    % (' '.join('%.6f' % x for x in ev), lam_num))

# ---- mu: min over unit v in T^perp of max_i grad f_i . v  (complete vertex enumeration)
Hbp = vt[:17]                                    # right singular vectors with nonzero singular values
A = np.array([[float(sum(Hbp[t, i] * Jf[r, i] for i in range(N))) for t in range(len(Hbp))]
              for r in range(NB)])
best, bestv, feas = 0.0, None, 0
for sub in itertools.combinations(range(NB), len(Hbp)):
    M = A[list(sub), :]
    try:
        vv = np.linalg.solve(M, np.ones(len(Hbp)))
    except np.linalg.LinAlgError:
        continue
    if (A @ vv > 1 + 1e-6).any():
        continue
    feas += 1
    nv = np.linalg.norm(vv)
    if nv > best:
        best, bestv = nv, sub
mu = 1.0 / best
say('[Q3] transverse rate: dim T^perp = %d ; feasible vertices %d ; max ||v|| = %.6f -> mu = %.8f'
    % (len(Hbp), feas, best, mu))

# ---- L2 and directional third derivatives
L2 = max(np.linalg.norm(Hf[r], 2) for r in range(NB))
say('[Q4] L2 proxy = max_i ||H_i||_2 = %.6f' % L2)
h = mp.mpf('1e-5')
dirs = [('kernel%d' % t, vv) for t, vv in enumerate(Q)] + \
       [('trans%d' % t, np.array([float(Hbp[t, i]) for i in range(N)])) for t in range(4)]
D3 = {}
for name, vv in dirs:
    xp = [X0[i] + h * mp.mpf(vv[i]) for i in range(N)]
    xm = [X0[i] - h * mp.mpf(vv[i]) for i in range(N)]
    Sp = [(Jet.var(2 * i, xp[2 * i]), Jet.var(2 * i + 1, xp[2 * i + 1])) for i in range(11)]
    Sm = [(Jet.var(2 * i, xm[2 * i]), Jet.var(2 * i + 1, xm[2 * i + 1])) for i in range(11)]
    BP = [face_branch(Sp, FACES[i]) for i in range(9)] + [tie_branch(Sp, k, TIEPICK[k]) for k in range(9)]
    BM = [face_branch(Sm, FACES[i]) for i in range(9)] + [tie_branch(Sm, k, TIEPICK[k]) for k in range(9)]
    vmp = [mp.mpf(x) for x in vv]
    mx = mp.mpf(0)
    for r in range(NB):
        hp = sum(vmp[a] * BP[r][1].h[a, b] * vmp[b] for a in range(N) for b in range(N))
        hm = sum(vmp[a] * BM[r][1].h[a, b] * vmp[b] for a in range(N) for b in range(N))
        mx = max(mx, abs(hp - hm) / (2 * h))
    D3[name] = float(mx)
say('[Q5] directional |v^T D^3 f(v,v,v)| (max over the 18 branches): ' +
    ' ; '.join('%s %.4f' % (k, v) for k, v in D3.items()))
D3max = max(D3.values())
rho_t = 2 * mu / L2
rho_k = 3 * lam_num / D3max
c_growth = min(mu / 2, lam_num / 4)
rr = min(rho_t, rho_k)
say('[Q6] thresholds: rho_transverse = 2 mu/L2 = %.3e ; rho_kernel = 3 lam/D3 = %.3e' % (rho_t, rho_k))
say('     implied box radius rho = %.3e ; growth c = min(mu/2, lam/4) = %.6e' % (rr, c_growth))
for tf in (1.0, 0.5, 0.25):
    t_ = rr * tf
    say('     t = %.2f rho = %.3e : transverse bound t mu - (L2/2) t^2 = %.3e ;'
        ' kernel bound (lam/2) t^2 - (D3/6) t^3 = %.3e'
        % (tf, t_, t_ * mu - L2 / 2 * t_ ** 2, lam_num / 2 * t_ ** 2 - D3max / 6 * t_ ** 3))
d_bound = min(rr / 2 * mu - L2 / 2 * (rr / 2) ** 2, lam_num / 2 * (rr / 2) ** 2 - D3max / 6 * (rr / 2) ** 3)

OUT = {'anchor': 'lead/repaired_tc_krawczyk.json (root box)', 'mu': mu, 'lambda_numeric': lam_num,
       'kernel_eig': [float(x) for x in ev], 'L2': float(L2), 'D3': D3, 'D3max': D3max,
       'rho_transverse': rho_t, 'rho_kernel': rho_k, 'rho': min(rho_t, rho_k),
       'c_growth': c_growth, 'sv_J': [float(x) for x in s[16:]],
       'repro': 'py -3 -B -X utf8 r20_quant_pilot.py'}
(P / 'r20_quant_pilot.json').write_text(json.dumps(OUT, indent=2))
(P / 'r20_quant_pilot.log').write_text('\n'.join(REP) + '\n')
say('\nwritten r20_quant_pilot.json / .log')
