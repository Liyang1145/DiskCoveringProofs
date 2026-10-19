#!/usr/bin/env python3
"""Exact-rational replay of N11Formalization.Paid16CellCertificate.Valid
(transcribed field-for-field from the WIP Lean sources; see SOURCES below).
Every comparison uses fractions.Fraction. Returns per-field verdicts and margins.

SOURCES (wip/lean/N11Formalization/):
  Paid16CellCertificate.lean (Valid), CosineLinePacket.lean (line Valid, IncArc/DecArc,
  piLower/piUpper), ConvexMinorantCore.lean (endpointLo, g, cl, cv, f0Lo),
  DBMMinorantDual.lean (rowA, db, rho, lamB, lower), DBMAngleProvider.lean (slo, shi),
  FlashCosineLeaf318.lean (Lq, LQ, Dq, DQ), Interval/Trig.lean (piLo, piHi),
  FlashCosineLeaf284Bridge.lean (iOf, jOf, T), IntervalsHigh(.Lag).lean (sinTQ, cosTQ,
  sinLoNLag, sinHiNLag, cosHiNLag), RoundedPaid16.lean (weight, mix).
"""
from fractions import Fraction as F
from math import factorial
import json

piLo = F(314159265358979323846, 10**20)
piHi = F(314159265358979323847, 10**20)
Lq = 2 * F(1150475603510479590494077, 2951479051793528258560000)
LQ = 2 * F(449404532622434011541355675101, 1152921504606846976000000000000)
Dq = 9 * Lq - 2 * piHi
DQ = 9 * LQ - 2 * piLo
T = F(1899919265599193545242591, 5000000000000000000000000)
T2 = T * T
PAIRS = [(i, j) for i in range(9) for j in range(i + 1, 9)]  # iOf/jOf, k=0..35
assert len(PAIRS) == 36 and PAIRS[7] == (0, 8) and PAIRS[8] == (1, 2) and PAIRS[35] == (7, 8)
F29 = F(factorial(29)); F28 = F(factorial(28))
SIN_DEN = [F(factorial(2 * k + 1)) for k in range(14)]
COS_DEN = [F(factorial(2 * k)) for k in range(14)]

def sinTQ(q):
    q2 = q * q; p = q; s = F(0)
    for k in range(14):
        s += (p if k % 2 == 0 else -p) / SIN_DEN[k]; p *= q2
    return s
def cosTQ(q):
    q2 = q * q; p = F(1); s = F(0)
    for k in range(14):
        s += (p if k % 2 == 0 else -p) / COS_DEN[k]; p *= q2
    return s
def sinLo(q): return sinTQ(q) - abs(q) ** 29 / F29
def sinHi(q): return sinTQ(q) + abs(q) ** 29 / F29
def cosHi(q): return cosTQ(q) + abs(q) ** 28 / F28

def endpointLo(a, b, x): return x * (a if x >= 0 else b)
def piLower(x): return endpointLo(piLo, piHi, x)
def piUpper(x): return -piLower(-x)
def incArc(a, b, m): return min(a - piUpper(2 * m - F(1, 2)), piLower(2 * m + F(1, 2)) - b)
def decArc(a, b, m): return min(a - piUpper(2 * m + F(1, 2)), piLower(2 * m + F(3, 2)) - b)

def line_margin(p):
    """min slack of CosineLinePacket.Valid (>=0 iff valid). Returns (margin, detail)."""
    a, b, s, c, t, e, m, r = p['a'], p['b'], p['s'], p['c'], p['t'], p['e'], p['shift'], p['rule']
    sl = [b - a]
    if r == 'tangent':
        sl += [incArc(a, b, m), t - a, b - t, e, sinLo(t) - (s - e), (s + e) - sinHi(t),
               (1 - cosHi(t) - s * t - e * (b - a)) - c]
    elif r == 'decreasing':
        sl += [decArc(a, b, m), (1 - cosHi(a) - s * a) - c, (1 - cosHi(b) - s * b) - c]
    elif r == 'left':
        sl += [incArc(a, b, m), sinLo(a) - s, (1 - cosHi(a) - s * a) - c]
    elif r == 'right':
        sl += [incArc(a, b, m), s - sinHi(b), (1 - cosHi(b) - s * b) - c]
    else:
        raise ValueError(r)
    return min(sl)

class Ctx:
    def __init__(self, parsed):
        self.tree = parsed['tree']
        self.wt = [[F(x, 10**12) for x in row] for row in parsed['weights']]
    def db(self, n, i, j): return F(self.tree[n]['db'][i][j], 4096)
    def slo(self, n, k):
        i, j = PAIRS[k]; return max(-self.db(n, j, i), F(0))
    def shi(self, n, k):
        i, j = PAIRS[k]; return self.db(n, i, j)
    def mix(self, beta, k): return sum((beta[f] * self.wt[f][k] for f in range(16)), F(0))

def rowA(i, j, q): return (1 if q < j else 0) - (1 if q < i else 0)

def check(ctx, p, fast_lines=False):
    """Return dict of per-field min slack (strict for numeric). Valid iff all >= 0 and numeric > 0."""
    n = p['nodeID']; beta = p['beta']; L = p['line']; lam = p['lam']; rf = p['rowFrom']; rt = p['rowTo']
    res = {}
    res['beta_nonneg'] = min(beta)
    res['beta_sum'] = 0 if sum(beta, F(0)) == 1 else -1
    res['lines'] = min(line_margin(l) for l in L)
    ep = []
    for k in range(36):
        i, j = PAIRS[k]
        ep.append((F(i - j) * LQ + Dq * ctx.slo(n, k)) - L[k]['a'])
        ep.append(L[k]['b'] - (F(i - j) * Lq + DQ * ctx.shi(n, k)))
    res['endpoints'] = min(ep)
    res['lam_nonneg'] = min(lam) if lam else F(0)
    w = [ctx.mix(beta, k) for k in range(36)]
    s = [l['s'] for l in L]; c = [l['c'] for l in L]
    g = [sum((w[k] * s[k] for k in range(36) if PAIRS[k][0] <= q < PAIRS[k][1]), F(0)) for q in range(9)]
    rho = [sum((lam[a] * rowA(rf[a], rt[a], q) for a in range(len(lam))), F(0)) for q in range(9)]
    res['reduced'] = min(endpointLo(Dq, DQ, g[q]) + rho[q] - p['rmin'] for q in range(9))
    cl = sum((w[k] * s[k] * (PAIRS[k][0] - PAIRS[k][1]) for k in range(36)), F(0))
    cv = sum((w[k] * c[k] for k in range(36)), F(0))
    f0 = cv + endpointLo(Lq, LQ, cl)
    lamB = sum((lam[a] * ctx.db(n, rf[a], rt[a]) for a in range(len(lam))), F(0))
    low = f0 - lamB + p['rmin']
    res['numeric'] = low - T2
    res['terminal'] = 0 if ctx.tree[n]['terminal'] else -1
    res['rows_le7'] = 0 if len(lam) <= 7 else -1
    ok = all(v >= 0 for kk, v in res.items() if kk != 'numeric') and res['numeric'] > 0
    return ok, res, low

def load_parsed(path='/workspace/work/dcp-n11-lean/energy/parsed.json'):
    d = json.load(open(path))
    def dec(x):
        if isinstance(x, str) and '/' in x:
            a, b = x.split('/'); return F(int(a), int(b))
        if isinstance(x, dict): return {k: dec(v) for k, v in x.items()}
        if isinstance(x, list): return [dec(v) for v in x]
        return x
    d['G'] = dec(d['G']); d['B22'] = dec(d['B22'])
    return d
