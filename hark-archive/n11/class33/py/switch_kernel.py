"""Exact Fraction transcription of the WIP switch direct leaf:
SharedMomentFactorIntervalCertificate.switchDirectUpperQ with RatInterval.{ofRat,add,mul} (Interval/Core.lean),
RationalTrigCellBounds.{sinCell,squareCell,midpoint,halfWidth}, IntervalsHighLag.{sinLoNLag,sinHiNLag},
IntervalsHigh.sinTQ, CompactQuadraticMomentMaximum.maximumQ.  Plus a tree generator in the batch shape
(switchCell lo hi, dyadic bisection, root [0,1571/1000])."""
from fractions import Fraction as F
from math import factorial
import functools
F29 = F(factorial(29))
FACT = [F(factorial(2 * k + 1)) for k in range(14)]
def sinTQ14(q):
    s = F(0); q2 = q * q; p = q
    for k in range(14):
        s += (p / FACT[k]) if k % 2 == 0 else -(p / FACT[k])
        p *= q2
    return s
def sinLo(q): return sinTQ14(q) - abs(q) ** 29 / F29
def sinHi(q): return sinTQ14(q) + abs(q) ** 29 / F29
def iv(a, b): return (a, b)
def ofRat(q): return (q, q)
def add(A, B): return (A[0] + B[0], A[1] + B[1])
def mul(A, B):
    c = (A[0] * B[0], A[0] * B[1], A[1] * B[0], A[1] * B[1])
    return (min(min(c[0], c[1]), min(c[2], c[3])), max(max(c[0], c[1]), max(c[2], c[3])))
def mid(I): return (I[0] + I[1]) / 2
def hw(I): return (I[1] - I[0]) / 2
def sinCell(I): return (max(F(-1), sinLo(mid(I)) - hw(I)), min(F(1), sinHi(mid(I)) + hw(I)))
def squareCell(I):
    if 0 <= I[0]: return (I[0] ** 2, I[1] ** 2)
    if I[1] <= 0: return (I[1] ** 2, I[0] ** 2)
    return (F(0), max(I[0] ** 2, I[1] ** 2))
def maximumQ(A, B):
    if A < 0 and 0 < B and B < -2 * A: return -B ** 2 / (4 * A)
    return max(F(0), A + B)
R2H = F(19, 50) ** 2 / 2
def switchDirectUpperQ(p, q, b, d2, d1, lo, hi):
    B0 = (lo, hi)
    s1 = sinCell(B0)
    quadC = add(add(mul(ofRat(R2H), sinCell(mul(ofRat(F(2)), B0))), mul(ofRat(q), squareCell(s1))), ofRat(d2))
    linC = add(mul(ofRat(b), s1), ofRat(d1))
    return mul(ofRat(p), B0)[1] + maximumQ(quadC[1], linC[1])

ROOT_HI = F(1571, 1000)
def gen_tree(c, M, max_nodes=200000, min_width=F(1, 10**7)):
    """Return list of accepted leaves (lo,hi) by DFS bisection at midpoints, or None if a cell below
    min_width fails.  Leaves are in left-to-right order and tile [0, ROOT_HI]."""
    leaves = []; stack = [(F(0), ROOT_HI)]; n = 0
    while stack:
        lo, hi = stack.pop(); n += 1
        if n > max_nodes: return None, n
        if switchDirectUpperQ(c['p'], c['q'], c['b'], c['d2'], c['d1'], lo, hi) <= M:
            leaves.append((lo, hi)); continue
        if hi - lo < min_width: return None, n
        m = (lo + hi) / 2
        stack.append((m, hi)); stack.append((lo, m))
    return leaves, n
