"""Fresh, self-contained rigorous energy certificates for root25 OPEN boxes.

Model (n26model.py / model134.json): 16 unit-circle anchors at turns theta_0=0,
theta_1..15 (box coordinates), 26 centers, 34 face witnesses, 134 rods each of
length <= rho for any real cover of radius rho (interface argument of the
archive, NOT re-proved here).  For ANY nonnegative weights w with the free block
G = L_FF positive definite:
    W rho^2 >= sum_e w_e |p_u-p_v|^2 >= Phi_w(theta)
              = sum_{i<j} 2 c_ij (1-cos 2pi(theta_j-theta_i)),   c = -Schur(L)_ij.
So if  Phi_w(theta) > W * RSTAR_UP^2  on the whole closed box, no cover of radius
< R* has anchor turns in that box (within this model).

Certificate per (sub)box:  rational weights w (exact Schur via python-flint fmpq),
then a rigorous lower bound of Phi_w on the box:
    Phi(m+d) >= Phi(m) + g.d + 1/2 d^T Hq d - eps*(sum|d|)^2 - cubic
with Phi(m), g, H enclosed in arb balls, Hq a rational PSD matrix (exact LDL)
with |H-Hq| <= eps entrywise, cubic = sum c_ij (8/3) pi^3 (r_i+r_j)^3, and the
convex quadratic minimised over the box with an exact supporting-hyperplane
lower bound.  No floating point quantity enters a verdict: floats only PROPOSE
weights, the evaluation point and the QP minimiser.
"""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import json, math, sys, time
from fractions import Fraction as F
import numpy as np
import flint
from flint import arb, fmpq, fmpq_mat, fmpz
import cvxpy as cp

flint.ctx.prec = 200
M = json.load(open(DCP_N26+'/model134.json'))
E = [tuple(e) for e in M['edges']]
RSTAR_UP = F("0.234700090400448239616790133776692127560495963654971391785925")
RUP2 = RSTAR_UP ** 2
PI = arb.pi()


# ---------------- exact kernel ----------------
def exact_pairs(wq):
    """wq: list of 134 positive Fractions. Returns (pairs dict (i,j)->Fraction, W)."""
    n = 76
    L = [[F(0)] * n for _ in range(n)]
    for (u, v), w in zip(E, wq):
        L[u][u] += w; L[v][v] += w; L[u][v] -= w; L[v][u] -= w
    def fm(rows):
        return fmpq_mat(len(rows), len(rows[0]), [fmpq(x.numerator, x.denominator) for r in rows for x in r])
    LFF = fm([row[16:] for row in L[16:]])
    LFA = fm([row[:16] for row in L[16:]])
    LAA = fm([row[:16] for row in L[:16]])
    X = LFF.solve(LFA)               # exact: LFF X = LFA
    assert LFF * X == LFA
    S = LAA - LFA.transpose() * X     # exact Schur complement
    pairs = {}
    for i in range(16):
        rs = fmpq(0)
        for j in range(16):
            rs += S[i, j]
            if j > i and S[i, j] != 0:
                assert S[i, j] < 0 and S[i, j] == S[j, i]
                v = -S[i, j]; pairs[(i, j)] = F(int(v.p), int(v.q))
        assert rs == 0
    # G positive definite: exact LDL pivots of LFF
    assert all(p > 0 for p in ldl_pivots_fmpq(LFF))
    return pairs, sum(wq, F(0))


def ldl_pivots_fmpq(A):
    n = A.nrows(); A = [[A[i, j] for j in range(n)] for i in range(n)]
    piv = []
    for k in range(n):
        p = A[k][k]; piv.append(p)
        if p <= 0: return piv
        for i in range(k + 1, n):
            if A[i][k] != 0:
                f = A[i][k] / p
                for j in range(k + 1, n):
                    A[i][j] -= f * A[k][j]
    return piv


# ---------------- numerical proposals ----------------
U = np.array([e[0] for e in E]); V = np.array([e[1] for e in E])


def fit_weights(theta):
    """dual weights of min s s.t. |p_u-p_v|^2<=s at fixed anchors."""
    th = np.concatenate([[0.0], theta])
    A = np.stack([np.cos(2 * np.pi * th), np.sin(2 * np.pi * th)], 1)
    X = cp.Variable((60, 2)); s = cp.Variable()
    cons = []
    for (u, v) in E:
        pu = A[u] if u < 16 else X[u - 16]
        pv = A[v] if v < 16 else X[v - 16]
        cons.append(cp.sum_squares(pu - pv) <= s)
    pr = cp.Problem(cp.Minimize(s), cons)
    pr.solve(solver='CLARABEL')
    lam = np.array([max(float(np.ravel(c.dual_value)[0]), 0.0) for c in cons])
    return lam / lam.sum(), float(s.value)


def rationalize_weights(lam, floor=1e-7, den=10 ** 12):
    return [F(int(round((max(x, 0) + floor) * den)), den) for x in lam]


# ---------------- rigorous bound ----------------
def A(x):
    return arb(fmpq(x.numerator, x.denominator)) if isinstance(x, F) else arb(x)


def box_bound(pairs, W, lo, hi):
    """rigorous lower bound (Fraction) of Phi_w - W*RUP2 over closed box [lo,hi] (Fractions, 15)."""
    m = [(a + b) / 2 for a, b in zip(lo, hi)]
    r = [(b - a) / 2 for a, b in zip(lo, hi)]
    mt = [F(0)] + m; rt = [F(0)] + r
    phi = arb(0); g = [arb(0)] * 16
    H = [[arb(0)] * 16 for _ in range(16)]
    cubic = F(0)
    for (i, j), c in pairs.items():
        ca = A(c); d = A(mt[j] - mt[i])
        cs = (2 * PI * d).cos(); sn = (2 * PI * d).sin()
        phi += 2 * ca * (1 - cs)
        gd = 4 * PI * ca * sn            # d/d(theta_j)
        g[j] += gd; g[i] -= gd
        h = 8 * PI * PI * ca * cs         # second derivative wrt d
        H[i][i] += h; H[j][j] += h; H[i][j] -= h; H[j][i] -= h
        cubic += c * (rt[i] + rt[j]) ** 3
    cub = A(cubic) * 8 * PI ** 3 / 3
    # reduce to 15 free coords (theta_0 fixed)
    g15 = g[1:]; H15 = [row[1:] for row in H[1:]]
    # rational midpoint Hq and entrywise error
    Hq = [[to_frac(H15[a][b].mid()) for b in range(15)] for a in range(15)]
    eps = F(0)
    for a in range(15):
        for b in range(15):
            e = arb_upper(abs(H15[a][b] - A(Hq[a][b])))
            eps = max(eps, e)
    # make Hq symmetric PSD by shifting diagonal if needed
    for a in range(15):
        for b in range(a):
            Hq[a][b] = Hq[b][a]
    Hf0 = np.array([[float(x) for x in row] for row in Hq])
    lmin = float(np.linalg.eigvalsh((Hf0 + Hf0.T) / 2).min())
    scaleH = max(1.0, float(np.abs(Hf0).max()))
    shift = F(lmin - 1e-9 * scaleH).limit_denominator(10 ** 15) if lmin < 1e-9 * scaleH else F(0)
    tries = 0
    while not psd_exact(Hq, shift):
        shift -= F(1, 10 ** 6) * F(scaleH).limit_denominator(10 ** 6) * (2 ** tries); tries += 1
        if tries > 40: return None, 'H-not-psd'
    Hs = [[Hq[a][b] - (shift if a == b else 0) for b in range(15)] for a in range(15)]
    neg_pen = (shift / 2) * sum(x * x for x in r) if shift < 0 else F(0)
    # numeric QP: min g.d + 1/2 d^T Hs d over box |d|<=r
    gf = np.array([float(x.mid()) for x in g15]); Hf = np.array([[float(x) for x in row] for row in Hs])
    rf = np.array([float(x) for x in r])
    dvar = cp.Variable(15)
    Hpsd = (Hf + Hf.T) / 2
    w_, Vv = np.linalg.eigh(Hpsd); w_ = np.maximum(w_, 0); Hpsd = (Vv * w_) @ Vv.T
    try:
        cp.Problem(cp.Minimize(gf @ dvar + 0.5 * cp.quad_form(dvar, cp.psd_wrap(Hpsd))), [cp.abs(dvar) <= rf]).solve(solver='CLARABEL')
        ds = [F(float(x)).limit_denominator(10 ** 18) for x in dvar.value]
    except Exception:
        ds = [F(0)] * 15
    ds = [max(-ri, min(ri, x)) for x, ri in zip(ds, r)]
    # exact convex lower bound: q(d) >= q(ds) + grad q(ds).(d-ds), with g as arb
    gq = [to_frac(x.mid()) for x in g15]
    gerr = [arb_upper(abs(x - A(q))) for x, q in zip(g15, gq)]
    Hd = [sum(Hs[a][b] * ds[b] for b in range(15)) for a in range(15)]
    qds = sum(gq[a] * ds[a] for a in range(15)) + sum(ds[a] * Hd[a] for a in range(15)) / 2
    lin = F(0)
    for a in range(15):
        grad = gq[a] + Hd[a]
        lin += min(grad * (-r[a] - ds[a]), grad * (r[a] - ds[a]))
    qlow = qds + lin - sum(e * ri for e, ri in zip(gerr, r))
    l1 = sum(r)
    total = A(qlow + neg_pen) + phi - A(eps * l1 * l1 / 2) - cub - A(W * RUP2)
    return arb_lower(total), 'ok'


def to_frac(x):
    """exact Fraction of an exact dyadic arb (midpoint/endpoint)."""
    m, e = x.man_exp(); m = int(m); e = int(e)
    return F(m * 2 ** e) if e >= 0 else F(m, 2 ** (-e))


def arb_upper(x):
    return to_frac(x.upper())


def arb_lower(x):
    return to_frac(x.lower())


def psd_exact(Hq, shift):
    n = len(Hq)
    A_ = [[Hq[a][b] - (shift if a == b else 0) for b in range(n)] for a in range(n)]
    for k in range(n):
        p = A_[k][k]
        if p < 0: return False
        if p == 0:
            if any(A_[i][k] != 0 for i in range(k + 1, n)): return False
            continue
        for i in range(k + 1, n):
            if A_[i][k]:
                f = A_[i][k] / p
                for j in range(k + 1, n):
                    A_[i][j] -= f * A_[k][j]
    return True
