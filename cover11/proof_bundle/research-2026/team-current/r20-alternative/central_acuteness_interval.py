"""central_acuteness_interval.py  (r20-alternative; sole write, no child)

Lead structural observation (priority test): the two central triangles are ACUTE at the candidate.
Since MEC(sites) = Rc on the acute domain, and the MEC condition "exists q with
|q-a|,|q-b|,|q-c| <= r" is the PROJECTION OF AN SOC (convex!), uniform acuteness over the box
would give:

     { (a,b) in K_A x K_B : Rc(a,b,c_i) <= r }  =  { (a,b) : MEC(a,b,c_i) <= r }   (acute)
                                                = projection of a convex SOC  => CONVEX

hence the whole joint feasible set is convex in (a,b) in R^4 (no Hessian needed), and Helly-4 /
SOCP become available.

This script interval-certifies the three vertex dot products per central face over the ring box
(rings +/- 1/1000, r in [UB*-1e-4, UB*+1e-4]) with a in the K_A rectangle and b in the K_B
rectangle (chain pins + strict-hub ball + variance localisation, as in
central_crescent_interval.py v3).  Rational/mpmath.iv, outward.

Deliberately scoped: pilot over this ring box; NOT a global claim.
"""
import json
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp
from mpmath import iv

iv.dps = 40
mp.dps = 40
OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
Pf = [(F(int(v[0]), 10**17), F(int(v[1]), 10**17)) for v in raw['centers_scaled_1e17']]
NEW2RAW_RINGS = [5, 7, 1, 8, 6, 4, 9, 10, 3]
FAN_A, FAN_B, CENTRAL = [4, 5, 6, 7, 8], [0, 1, 2, 3], [0, 4]
R_UB = F(3799838531198387090485182, 10**25)
WL = [(F(459977731, 10**9), 4), (F(80044539, 10**9), 6), (F(459977730, 10**9), 8)]
WB = [(F(1, 2), 0), (F(1, 2), 3)]
D_FIX, W_FIX = F(1, 1000), F(1, 10000)


def M(fr):
    return iv.mpf(fr.numerator) / iv.mpf(fr.denominator)


def ep_lo(x):
    return mp.mpf(x.a)


def ep_hi(x):
    return mp.mpf(x.b)


def iv_str(x, d=25):
    return [mp.nstr(ep_lo(x), d), mp.nstr(ep_hi(x), d)]


def vadd(A, B):
    return (A[0] + B[0], A[1] + B[1])


def vsub(A, B):
    return (A[0] - B[0], A[1] - B[1])


def vscale(A, s):
    return (A[0] * s, A[1] * s)


def dot(A, B):
    return A[0] * B[0] + A[1] * B[1]


def isqrt_up(x):
    if ep_hi(x) < 0:
        return None
    lo = ep_lo(x) if ep_lo(x) > 0 else mp.mpf(0)
    return iv.sqrt(iv.mpf([lo, ep_hi(x)]))


C_NOM = [(M(Pf[i][0]), M(Pf[i][1])) for i in NEW2RAW_RINGS]
D_IV = M(D_FIX)
W_IV = M(W_FIX)
DW = iv.mpf([-ep_hi(D_IV), ep_hi(D_IV)])
WW = iv.mpf([-ep_hi(W_IV), ep_hi(W_IV)])
rings = [(c[0] + DW, c[1] + DW) for c in C_NOM]
rI = M(R_UB) + WW


def pin(i):
    A_, B_ = rings[i], rings[(i + 1) % 9]
    u = vsub(B_, A_)
    d = isqrt_up(dot(u, u))
    rad = rI * rI - dot(u, u) / 4
    k = iv.sqrt(iv.mpf([max(ep_lo(rad), 0), ep_hi(rad)]))
    m = vscale(vadd(A_, B_), M(F(1, 2)))
    n = (-u[1] / d, u[0] / d)
    p1, p2 = vadd(m, vscale(n, k)), vsub(m, vscale(n, k))
    n1, n2 = isqrt_up(dot(p1, p1)), isqrt_up(dot(p2, p2))
    if ep_hi(n1) < ep_lo(n2):
        return p1
    if ep_hi(n2) < ep_lo(n1):
        return p2
    raise RuntimeError('pin inner-root selection UNDECIDED in the box (guard added per lead)')


pins = {i: pin(i) for i in range(9)}


def rect_of(ds):
    # OUTWARD endpoints only (lead review: plain mp arithmetic below is not an interval bound)
    xlo = max((c[0] - rr).a for c, rr in ds)
    xhi = min((c[0] + rr).b for c, rr in ds)
    ylo = max((c[1] - rr).a for c, rr in ds)
    yhi = min((c[1] + rr).b for c, rr in ds)
    return ((iv.mpf([xlo, xhi]) if xlo <= xhi else None),
            (iv.mpf([ylo, yhi]) if ylo <= yhi else None))


def variance_b(weights):
    V = iv.mpf([0, 0])
    b = (iv.mpf([0, 0]), iv.mpf([0, 0]))
    for (w, i) in weights:
        b = vadd(b, vscale(pins[i], M(w)))
    for t in range(len(weights)):
        for u2 in range(t + 1, len(weights)):
            (wi, ii), (wj, jj) = weights[t], weights[u2]
            dv = vsub(pins[ii], pins[jj])
            V = V + M(wi * wj) * dot(dv, dv)
    return V, b


z = iv.mpf([0, 0])
KA_disks = [((z, z), M(F(1)) - rI)] + [(pins[j], rI) for j in FAN_A]
KB_disks = [((z, z), M(F(1)) - rI)] + [(pins[j], rI) for j in FAN_B]
VA, bA = variance_b(WL)
VA_rad = rI * rI - VA
epsA = iv.sqrt(iv.mpf([max(ep_lo(VA_rad), 0), ep_hi(VA_rad)]))
VB, bB = variance_b(WB)
VB_rad = rI * rI - VB
epsB = iv.sqrt(iv.mpf([max(ep_lo(VB_rad), 0), ep_hi(VB_rad)]))
KA_rect = rect_of(KA_disks)
KB_rect = rect_of(KB_disks)
loc = ((bA[0] - epsA, bA[0] + epsA), (bA[1] - epsA, bA[1] + epsA))
KA_rect = (iv.mpf([max(ep_lo(KA_rect[0]), ep_lo(loc[0][0])),
                    min(ep_hi(KA_rect[0]), ep_hi(loc[0][1]))]),
            iv.mpf([max(ep_lo(KA_rect[1]), ep_lo(loc[1][0])),
                    min(ep_hi(KA_rect[1]), ep_hi(loc[1][1]))]))
rep = {'kind': 'interval acuteness certification for the two central faces (pilot box)',
       'box': {'rings': '+/- 1/1000', 'r': 'UB* +/- 1/10000 (exact rationals)',
               'a in K_A rectangle': [[mp.nstr(ep_lo(KA_rect[0]), 18), mp.nstr(ep_hi(KA_rect[0]), 18)],
                                      [mp.nstr(ep_lo(KA_rect[1]), 18), mp.nstr(ep_hi(KA_rect[1]), 18)]],
               'b in K_B rectangle': [[mp.nstr(ep_lo(KB_rect[0]), 18), mp.nstr(ep_hi(KB_rect[0]), 18)],
                                      [mp.nstr(ep_lo(KB_rect[1]), 18), mp.nstr(ep_hi(KB_rect[1]), 18)]]}}
Abox = KA_rect
Bbox = KB_rect
res = {}
for i in CENTRAL:
    Ci = rings[i]
    d_ab = vsub(Abox, Bbox)              # a - b
    d_bc = vsub(Ci, Bbox)                # c - b
    d_ac = vsub(Ci, Abox)                # c - a
    dots = {'(a-b).(c-b) > 0  [vertex b]': dot(d_ab, d_bc),
            '(b-a).(c-a) > 0  [vertex a]': dot(vsub(Bbox, Abox), d_ac),
            '(c-a).(c-b) > 0  [vertex c]': dot(d_ac, d_bc)}
    res['face_%d' % i] = {k: {'interval': iv_str(v), 'lower_end_positive': bool(ep_lo(v) > 0)}
                          for k, v in dots.items()}
rep['faces'] = res
allpos = all(d['lower_end_positive'] for f in res.values() for d in f.values())
rep['uniform_acuteness_certified'] = bool(allpos)
rep['consequence'] = ('on the acute domain Rc = MEC, and {MEC <= r} is the projection of the SOC '
                      '{(a,b,q) : |q-a|,|q-b|,|q-c_i| <= r}, which is convex; hence over this box '
                      'the two central constraints are convex projections and the joint feasible '
                      'set in (a,b) is CONVEX (Helly-4 / SOCP available).'
                      if allpos else
                      'acuteness NOT certified on this box: joint-convex route via MEC not '
                      'established here.')
rep['scope'] = ('pilot over the stated ring box only (rings +/- 1/1000, r = UB* +/- 1e-4); the '
                'a/b ranges are the K_A / K_B rectangles; NOT a global claim')
(OUT / 'central_acuteness_interval.json').write_text(json.dumps(rep, indent=2), encoding='utf-8')
print(json.dumps(rep, indent=1))
