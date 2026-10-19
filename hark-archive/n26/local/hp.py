"""High-precision (arb ball) evaluation of the 134-rod Schur energy near the
candidate theta*.  PROPOSAL/diagnostic tool; verdicts go through rigorous
checkers only.  Weights: rational, >=0, rods with zero weight dropped; free
vertices with no weighted rod dropped (energy unchanged)."""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import json
from fractions import Fraction as F
import flint
from flint import arb, fmpq, arb_mat
flint.ctx.prec = 320
ROOT = DCP_N26
E = [tuple(e) for e in json.load(open(ROOT + '/model134.json'))['edges']]
K = json.load(open(ROOT + '/kkt2_122.json'))
ACT = K['A']; LIVE = K['live']; nX = 2 * len(LIVE)
THSTAR = [F(x) for x in K['z'][:15]]            # 58-digit rational approx of theta*
LAM0 = [F(0)] * 134
for e, x in zip(ACT, K['z'][15 + nX:15 + nX + len(ACT)]):
    LAM0[e] = F(x) if F(x) > F(1, 10**40) else F(0)
RSTAR_UP = F("0.234700090400448239616790133776692127560495963654971391785925")
RUP2 = RSTAR_UP ** 2
PI = arb.pi()

def A(x): return arb(fmpq(x.numerator, x.denominator))

def pairs_arb(w):
    """Schur pair weights c_ij (arb balls) for rational weights w (list of 134 Fractions)."""
    use = [k for k in range(134) if w[k] != 0]
    fv = sorted({v for k in use for v in E[k] if v >= 16})
    ix = {v: i for i, v in enumerate(fv)}; n = len(fv)
    LFF = arb_mat(n, n); LFA = arb_mat(n, 16); LAA = [[arb(0)] * 16 for _ in range(16)]
    for k in use:
        u, v = E[k]; x = A(w[k])
        for a, b in ((u, v), (v, u)):
            if a >= 16:
                LFF[ix[a], ix[a]] += x
                if b >= 16: LFF[ix[a], ix[b]] -= x
                else: LFA[ix[a], b] -= x
            else:
                LAA[a][a] += x
                if b < 16: LAA[a][b] -= x
    X = LFF.solve(LFA)
    S = [[LAA[i][j] - sum((LFA[k, i] * X[k, j] for k in range(n)), arb(0)) for j in range(16)] for i in range(16)]
    return {(i, j): -S[i][j] for i in range(16) for j in range(i + 1, 16)}, sum(w, F(0))

def phi_g_H(c, th):
    """value, gradient (15), Hessian (15x15) of Phi at turns th (15 Fractions or arbs)."""
    t = [arb(0)] + [A(x) if isinstance(x, F) else x for x in th]
    phi = arb(0); g = [arb(0)] * 16; H = [[arb(0)] * 16 for _ in range(16)]
    for (i, j), cij in c.items():
        d = 2 * PI * (t[j] - t[i]); cs = d.cos(); sn = d.sin()
        phi += 2 * cij * (1 - cs)
        gd = 4 * PI * cij * sn; g[j] += gd; g[i] -= gd
        h = 8 * PI * PI * cij * cs
        H[i][i] += h; H[j][j] += h; H[i][j] -= h; H[j][i] -= h
    return phi, g[1:], [r[1:] for r in H[1:]]

def margin(c, W, th):
    return phi_g_H(c, th)[0] - A(W) * A(RUP2)
