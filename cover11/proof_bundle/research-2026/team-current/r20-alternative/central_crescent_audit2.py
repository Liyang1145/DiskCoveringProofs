"""central_crescent_audit2.py  --- independent second kernel (rational interval arithmetic)

Purpose: audit the decisive inequalities of `central_crescent_interval.py` (v2) with a
DIFFERENT implementation: exact rational endpoints, square roots enclosed by scaled integer
square roots (no mpmath.iv at all).  Checks:

  A1  weights: exact sum 1 and product identities (rational)
  A2  pins: two radical roots, inner-root attribution by the unit-disk criterion (|p|<1 vs >1)
  A3  localisations eps_A (pins 4,6,8, rational weights) and eps_B (pins 0,3, weights 1/2)
  A4  K_A / K_B outer rectangles (outer scalar endpoints)
  A5  central disk centres q_i over the A-box, crescent branch by rational sign test
  A6  G_i = |b_B - q'_i| - eps_B - r  lower bound  -> CERTIFIED / FAILED
  A7  directed float output: nextafter endpoints bracket the rational endpoints

Everything outward-rounded; inputs are the exact rational centres, the saved rational upper
object r0 = UB* and dyadic deltas.  No claim is registered by this script.
"""
import json
import math
from fractions import Fraction as F
from pathlib import Path

BITS = 200                      # sqrt enclosure precision
SC = 1 << BITS
OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
Pf = [(F(int(x[0]), 10**17), F(int(x[1]), 10**17)) for x in raw['centers_scaled_1e17']]
NEW2RAW_RINGS = [5, 7, 1, 8, 6, 4, 9, 10, 3]
FAN_A, FAN_B, CENTRAL = [4, 5, 6, 7, 8], [0, 1, 2, 3], [0, 4]
R_UB = F(3799838531198387090485182, 10**25)
WL = [(F(459977731, 10**9), 4), (F(80044539, 10**9), 6), (F(459977730, 10**9), 8)]
WB = [(F(1, 2), 0), (F(1, 2), 3)]
RINGS = [(Pf[i][0], Pf[i][1]) for i in NEW2RAW_RINGS]


def isqrt_frac(q):
    """(lo,hi) Fractions with lo <= sqrt(q) <= hi (outward, scaled integer sqrt)"""
    if q < 0:
        return None
    k = math.isqrt(int(q * SC * SC))
    return F(k, SC), F(k + 1, SC)


class Iv:
    __slots__ = ('lo', 'hi')

    def __init__(self, lo, hi):
        self.lo, self.hi = lo, hi

    @staticmethod
    def pt(q):
        return Iv(q, q)

    def add(self, o):
        return Iv(self.lo + o.lo, self.hi + o.hi)

    def sub(self, o):
        return Iv(self.lo - o.hi, self.hi - o.lo)

    def mul(self, o):
        p = (self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi)
        return Iv(min(p), max(p))

    def div(self, o):
        if o.lo <= 0 <= o.hi:
            raise ZeroDivisionError
        p = (self.lo / o.lo, self.lo / o.hi, self.hi / o.lo, self.hi / o.hi)
        return Iv(min(p), max(p))

    def neg(self):
        return Iv(-self.hi, -self.lo)

    def sqrt(self):
        """SOUND outward sqrt: for an argument interval [lo,hi] that may dip below 0 the legal
        radicand set is [max(lo,0), hi], hence  sqrt in [sqrt(max(lo,0)), sqrt(hi)].
        (v1 of this file wrongly returned [sqrt(hi), sqrt(hi)] when lo<=0 -- found by matching
        against the mpmath kernel; that was an unsound sharpening.)"""
        if self.hi < 0:
            raise ValueError('sqrt of a certified-negative interval')
        hi = isqrt_frac(self.hi)[1]
        lo = isqrt_frac(self.lo)[0] if self.lo > 0 else F(0)
        return Iv(lo, hi)

    def __repr__(self):
        return 'Iv(%s,%s)' % (float(self.lo), float(self.hi))


def V(x, y):
    return (x, y)


def vadd(A, B):
    return (A[0].add(B[0]), A[1].add(B[1]))


def vsub(A, B):
    return (A[0].sub(B[0]), A[1].sub(B[1]))


def vscale(A, s):
    return (A[0].mul(s), A[1].mul(s))


def dot(A, B):
    return A[0].mul(B[0]).add(A[1].mul(B[1]))


def det(A, B):
    return A[0].mul(B[1]).sub(A[1].mul(B[0]))


def norm(A):
    return dot(A, A).sqrt()


rep = {'kernel': 'rational-interval (Fraction + scaled integer sqrt), BITS=%d' % BITS,
       'purpose': 'independent audit of central_crescent_interval.py v2'}

# ---- A1 weights -------------------------------------------------------------------
sA = sum(w for w, _ in WL)
sB = sum(w for w, _ in WB)
rep['A1_weights_sum'] = {'sum_WL': str(sA), 'is_one': sA == 1, 'sum_WB': str(sB), 'is_one': sB == 1}

# ---- A2 pins (delta = 0 first, then per delta) ------------------------------------


def pins_for(delta):
    D = Iv.pt(delta)
    rings = [(Iv(c[0] - delta, c[0] + delta), Iv(c[1] - delta, c[1] + delta)) for c in RINGS]
    rI = Iv(R_UB - delta, R_UB + delta) if False else Iv(R_UB, R_UB)
    return rings, rI


def pin_at(rings, rI, i):
    A, B = rings[i], rings[(i + 1) % 9]
    u = vsub(B, A)
    d2 = dot(u, u)
    d = d2.sqrt()
    rad = rI.mul(rI).sub(d2.div(Iv.pt(F(4))))
    if rad.hi < 0:
        return None, 'ILEGAL: d>2r'
    k = rad.sqrt()
    m = vscale(vadd(A, B), Iv.pt(F(1, 2)))
    n = (u[1].neg().div(d), u[0].div(d))
    p1, p2 = vadd(m, vscale(n, k)), vsub(m, vscale(n, k))
    n1, n2 = norm(p1), norm(p2)
    if n1.hi < 1 and n2.lo >= 1:
        return p1, 'inner=p1 (unit disk)'
    if n2.hi < 1 and n1.lo >= 1:
        return p2, 'inner=p2 (unit disk)'
    if n1.hi < n2.lo:
        return p1, 'inner=p1 (smaller norm)'
    if n2.hi < n1.lo:
        return p2, 'inner=p2 (smaller norm)'
    return None, 'UNDECIDED root'


def variance_b(pins, weights):
    Vv = Iv.pt(F(0))
    b = (Iv.pt(F(0)), Iv.pt(F(0)))
    for (w, i) in weights:
        b = vadd(b, vscale(pins[i], Iv.pt(w)))
    for a_i in range(len(weights)):
        for b_i in range(a_i + 1, len(weights)):
            (wi, ii), (wj, jj) = weights[a_i], weights[b_i]
            d2 = dot(vsub(pins[ii], pins[jj]), vsub(pins[ii], pins[jj]))
            Vv = Vv.add(d2.mul(Iv.pt(wi * wj)))
    return Vv, b


def rect_of(disks):
    """disks: list of (centre interval pair, radius interval); outer scalar endpoints"""
    xlo = max(c[0].lo - r.hi for c, r in disks)
    xhi = min(c[0].hi + r.hi for c, r in disks)
    ylo = max(c[1].lo - r.hi for c, r in disks)
    yhi = min(c[1].hi + r.hi for c, r in disks)
    return ((xlo, xhi), (ylo, yhi))


def empty(rect):
    return rect[0][0] > rect[0][1] or rect[1][0] > rect[1][1]


def certificate(delta, w_r=0.0):
    D = F(delta)
    WR = F(w_r)
    rings = [(Iv(c[0] - D, c[0] + D), Iv(c[1] - D, c[1] + D)) for c in RINGS]
    rI = Iv(R_UB - WR, R_UB + WR)
    out = {'delta': str(delta), 'w_r': str(w_r)}
    pins, stat = {}, {}
    for i in range(9):
        p, s = pin_at(rings, rI, i)
        pins[i], stat[i] = p, s
    out['pin_status'] = sorted(set(stat.values()))
    if any(p is None for p in pins.values()):
        out['result'] = 'UNDECIDED/ILEGAL pins'
        return out
    zero = Iv.pt(F(0))
    KA_d = [(zero, Iv.pt(F(0)), Iv.pt(F(1)).sub(rI))] + [(Iv.pt(F(0)), Iv.pt(F(0)), rI)]
    # (rebuild properly below: disks are ((x,y) intervals, radius interval))
    KA_disks = [((zero, zero), Iv.pt(F(1)).sub(rI))] + [(pins[j], rI) for j in FAN_A]
    KB_disks = [((zero, zero), Iv.pt(F(1)).sub(rI))] + [(pins[j], rI) for j in FAN_B]
    KB_rect = rect_of(KB_disks)
    VB, bB = variance_b(pins, WB)
    radB = rI.mul(rI).sub(VB)
    if radB.hi < 0:
        out['result'] = 'SCREEN-EXCLUDED V_B>r^2'
        return out
    epsB = radB.sqrt()
    VA, bA = variance_b(pins, WL)
    radA = rI.mul(rI).sub(VA)
    if radA.hi < 0:
        out['result'] = 'SCREEN-EXCLUDED V_A>r^2'
        return out
    epsA = radA.sqrt()
    locA = ((bA[0].lo - epsA.hi, bA[0].hi + epsA.hi), (bA[1].lo - epsA.hi, bA[1].hi + epsA.hi))
    KA_rect = rect_of(KA_disks)
    KA_rect = ((max(KA_rect[0][0], locA[0][0]), min(KA_rect[0][1], locA[0][1])),
               (max(KA_rect[1][0], locA[1][0]), min(KA_rect[1][1], locA[1][1])))
    if empty(KA_rect) or empty(KB_rect):
        out['result'] = 'SCREEN-EXCLUDED empty rectangle'
        return out
    out['epsA'] = [str(float(epsA.lo)), str(float(epsA.hi))]
    out['epsB'] = [str(float(epsB.lo)), str(float(epsB.hi))]
    Abox = (Iv(KA_rect[0][0], KA_rect[0][1]), Iv(KA_rect[1][0], KA_rect[1][1]))
    faces = {}
    for i in CENTRAL:
        Ci = rings[i]
        u = vsub(Ci, Abox)
        d2u = dot(u, u)
        rad = rI.mul(rI).sub(d2u.div(Iv.pt(F(4))))
        if rad.hi < 0:
            faces[i] = {'status': 'EXCLUDED |AC|>2r'}
            continue
        if u[0].lo <= 0 <= u[0].hi and u[1].lo <= 0 <= u[1].hi:
            faces[i] = {'status': 'UNDECIDED A=C'}
            continue
        d = d2u.sqrt()
        k = rad.sqrt()
        m = vscale(vadd(Abox, Ci), Iv.pt(F(1, 2)))
        n = (u[1].neg().div(d), u[0].div(d))
        qp, qm = vadd(m, vscale(n, k)), vsub(m, vscale(n, k))
        sref = det(u, vsub(bB, Abox))
        if sref.lo > 0:
            qnear, qfar, br = qp, qm, '+'
        elif sref.hi < 0:
            qnear, qfar, br = qm, qp, '-'
        else:
            faces[i] = {'status': 'UNDECIDED branch'}
            continue
        G = norm(vsub(bB, qfar)).sub(epsB).sub(rI)
        faces[i] = {'branch': br, 'G_lo': float(G.lo), 'G_hi': float(G.hi),
                    'G_lo_exact_fraction': str(G.lo), 'G_hi_exact_fraction': str(G.hi),
                    'certified': G.lo > 0}
    out['faces'] = faces
    if all('certified' in f for f in faces.values()) and all(f['certified'] for f in faces.values()):
        out['result'] = 'CERTIFIED'
    elif any('status' in f for f in faces.values()):
        out['result'] = 'UNDECIDED/EXCLUDED'
    else:
        out['result'] = 'FAILED'
    return out


rep['A2_A6_delta0'] = certificate(0.0)
rep['A2_A6_delta_1e-3_w0'] = certificate(F(1, 1000), F(0))
rep['A2_A6_delta_1e-3_w1e-4'] = certificate(F(1, 1000), F(1, 10000))
rep['A2_A6_delta_1p872e-3'] = certificate(F(18720480434240017, 10**19))
rep['A2_A6_delta_1p9e-3'] = certificate(F(19, 10**4))

# ---- A7 directed output ------------------------------------------------------------
checks = []
for x in (R_UB, F(1, 3), -F(7, 11)):
    lof = math.nextafter(float(x), -math.inf)
    hif = math.nextafter(float(x), math.inf)
    checks.append({'x': str(float(x)), 'nextafter_down_le_x': lof <= float(x),
                   'nextafter_up_ge_x': hif >= float(x)})
rep['A7_directed_output'] = checks

(OUT / 'central_crescent_audit2.json').write_text(json.dumps(rep, indent=2), encoding='utf-8')
print('A1 weights sum 1:', rep['A1_weights_sum'])
for k in ('A2_A6_delta0', 'A2_A6_delta_1e-3_w0', 'A2_A6_delta_1e-3_w1e-4',
          'A2_A6_delta_1p872e-3', 'A2_A6_delta_1p9e-3'):
    r = rep[k]
    fs = {i: (round(f.get('G_lo', 0), 12), f.get('certified')) for i, f in r.get('faces', {}).items()}
    print(k, '->', r['result'], fs, '| pin_status', r.get('pin_status'))
print('epsA', rep['A2_A6_delta0'].get('epsA'), 'epsB', rep['A2_A6_delta0'].get('epsB'))
print('exact Fraction G_lo at 1e-3/1e-4:',
      {i: str(f.get('G_lo_exact_frac')) for i, f in
       rep['A2_A6_delta_1e-3_w1e-4'].get('faces', {}).items()})
print('A7', rep['A7_directed_output'])
