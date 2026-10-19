"""Exact Fraction transcription of the WIP sector direct leaf:
MetricSectorRationalCellCertificate.{qRawCell,qCell,BoundsValid,triangleCell,penaltyCell,sectorDirectUpperQ},
MetricSectorRationalNodes.signedWidthUpperQ, RationalTrigCellBounds.{sinCell,squareCell}, IntervalsHighLag.sin{Lo,Hi}NLag.
Cell = ((alo,ahi),(ulo,uhi),(vlo,vhi)).  K = (chordLo, chordHi, hwLo, hwHi).
Python pre-validation only (not Lean evidence)."""
from fractions import Fraction as F
from math import factorial, isqrt, asin, sqrt, sin, cos, pi
import functools
F29 = factorial(29)
FACT = [factorial(2 * k + 1) for k in range(14)]
PIHI = F(314159265358979323847, 10**20)
R2H = F(19, 50) ** 2 / 2

@functools.lru_cache(maxsize=1 << 18)
def sinTQ14(q):
    s = F(0); q2 = q * q; p = q
    for k in range(14):
        t = p / FACT[k]
        s = s + t if k % 2 == 0 else s - t
        p = p * q2
    return s
def qabs(q): return -q if q < 0 else q
@functools.lru_cache(maxsize=1 << 18)
def sinLoHi(q):
    t = sinTQ14(q); r = qabs(q) ** 29 / F29
    return (t - r, t + r)
def sinLo(q): return sinLoHi(q)[0]
def sinHi(q): return sinLoHi(q)[1]
def ofRat(q): return (q, q)
def add(A, B): return (A[0] + B[0], A[1] + B[1])
def sub(A, B): return (A[0] - B[1], A[1] - B[0])
def mul(A, B):
    c = (A[0] * B[0], A[0] * B[1], A[1] * B[0], A[1] * B[1])
    return (min(c), max(c))
def sinCell(I):
    m = (I[0] + I[1]) / 2; h = (I[1] - I[0]) / 2
    lo, hi = sinLoHi(m)
    return (max(F(-1), lo - h), min(F(1), hi + h))
def squareCell(I):
    if 0 <= I[0]: return (I[0] ** 2, I[1] ** 2)
    if I[1] <= 0: return (I[1] ** 2, I[0] ** 2)
    return (F(0), max(I[0] ** 2, I[1] ** 2))
def qRawCell(B):
    h = mul(ofRat(F(1, 2)), B[0])
    return add(squareCell(sub(B[1], B[2])), mul(mul(ofRat(F(4)), mul(B[1], B[2])), squareCell(sinCell(h))))
def qCell(B):
    r = qRawCell(B); return (max(F(0), r[0]), min(F(4), r[1]))
def boundsValid(B, K):
    cl, ch, hl, hh = K
    q = qCell(B)
    return (0 <= B[0][0] <= B[0][1] and 0 <= B[1][0] <= B[1][1] <= 1 and 0 <= B[2][0] <= B[2][1] <= 1 and
            0 <= cl and 0 <= ch and cl * cl <= q[0] and q[1] <= ch * ch and
            0 <= hl <= 1 and 0 <= hh <= 1 and sinHi(hl) <= F(19, 100) * cl and F(19, 100) * ch <= sinLo(hh))
def signedWidthUpperQ(C, K):
    return C * (2 * K[3] if C >= 0 else 2 * K[2])
def pen(c, I): return mul(ofRat(-c), I)
def sectorDirectUpperQ(co, B, K):
    C, mu, dL, dR, bL, bR = co
    tri = mul(mul(ofRat(R2H), mul(B[1], B[2])), sinCell(B[0]))
    return (tri[1] + (2 * K[3] - sinLo(2 * K[3])) / 2 + signedWidthUpperQ(C, K) + pen(mu, B[0])[1] +
            pen(dL, squareCell(B[1]))[1] + pen(dR, squareCell(B[2]))[1] + pen(bL, B[1])[1] + pen(bR, B[2])[1])

def fsqrt_dy(x, P, up):
    """dyadic (denominator 2^P) lower/upper sqrt of nonneg Fraction x"""
    N = 1 << P
    n = (x.numerator * N * N) // x.denominator
    r = isqrt(n)
    if up:
        if F(r * r, N * N) < x: r += 1
    return F(r, N)
def chooseK(B, P=20):
    q = qCell(B)
    cl = fsqrt_dy(q[0], P, False); ch = fsqrt_dy(q[1], P, True)
    N = 1 << P
    # hwLo: largest n/N with sinHi(n/N) <= .19*cl
    tgt = F(19, 100) * cl
    n = int(asin(min(1.0, float(tgt))) * N) + 1
    n = min(n, N)
    while n > 0 and sinHi(F(n, N)) > tgt: n -= 1
    hl = F(n, N)
    tgt2 = F(19, 100) * ch
    n = int(asin(min(1.0, float(tgt2))) * N)
    n = max(0, n - 1)
    while n < N and sinLo(F(n, N)) < tgt2: n += 1
    hh = F(n, N)
    return (cl, ch, hl, hh)
def leafBound(co, B, P=20):
    K = chooseK(B, P)
    if not boundsValid(B, K): return None, K
    return sectorDirectUpperQ(co, B, K), K

# ---- float shadow (guide only) ----
def fl_bound(cf, lo, hi):
    """cf floats (C,mu,dL,dR,bL,bR); lo,hi tuples of floats; returns approx direct upper bound"""
    C, mu, dL, dR, bL, bR = cf
    a0, a1 = lo[0], hi[0]; u0, u1 = lo[1], hi[1]; v0, v1 = lo[2], hi[2]
    am = (a0 + a1) / 2; ah = (a1 - a0) / 2
    s_lo = max(-1.0, sin(am) - ah); s_hi = min(1.0, sin(am) + ah)
    # sin cell of a more precisely: use true range
    # true sin range on [a0,a1]
    cands = [sin(a0), sin(a1)]
    if a0 <= pi / 2 <= a1: cands.append(1.0)
    s_hi = min(s_hi, max(cands)); s_lo = max(s_lo, min(cands))
    c = [R2H.numerator / R2H.denominator * x for x in (u0 * v0, u0 * v1, u1 * v0, u1 * v1)]
    pr = (min(c), max(c))
    t = [pr[0] * s_lo, pr[0] * s_hi, pr[1] * s_lo, pr[1] * s_hi]
    tri = max(t)
    # chord^2 interval
    sd = (u0 - v1, u1 - v0)
    sq = (0.0 if sd[0] <= 0 <= sd[1] else min(sd[0] ** 2, sd[1] ** 2), max(sd[0] ** 2, sd[1] ** 2))
    hm = am / 2; hh = ah / 2
    h_lo = max(-1.0, sin(hm) - hh); h_hi = min(1.0, sin(hm) + hh)
    cand = [sin(a0 / 2), sin(a1 / 2)]
    if a0 / 2 <= pi / 2 <= a1 / 2: cand.append(1.0)
    h_lo = max(h_lo, min(cand)); h_hi = min(h_hi, max(cand))
    sq2 = (0.0 if h_lo <= 0 <= h_hi else min(h_lo ** 2, h_hi ** 2), max(h_lo ** 2, h_hi ** 2))
    uv = (u0 * v0, u1 * v1)
    q_lo = sq[0] + 4 * uv[0] * sq2[0]; q_hi = sq[1] + 4 * uv[1] * sq2[1]
    q_lo = max(0.0, q_lo); q_hi = min(4.0, q_hi)
    cl = sqrt(q_lo); ch = sqrt(q_hi)
    hl = asin(min(1.0, 0.19 * cl)); hhi = asin(min(1.0, 0.19 * ch)) + 1e-9
    sgw = C * (2 * hhi if C >= 0 else 2 * hl)
    w2 = 2 * hhi
    seg = (w2 - sin(w2)) / 2 + (w2 ** 29 / factorial(29)) / 2  # lo-bound error negligible
    pen_mu = max(-mu * a0, -mu * a1)
    def sqI(x0, x1): return (0.0 if x0 <= 0 <= x1 else min(x0 * x0, x1 * x1), max(x0 * x0, x1 * x1))
    s1 = sqI(u0, u1); s2 = sqI(v0, v1)
    pen_dL = max(-dL * s1[0], -dL * s1[1]); pen_dR = max(-dR * s2[0], -dR * s2[1])
    pen_bL = max(-bL * u0, -bL * u1); pen_bR = max(-bR * v0, -bR * v1)
    return tri + seg + sgw + pen_mu + pen_dL + pen_dR + pen_bL + pen_bR
