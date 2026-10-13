"""Biconvexity pilot for the central fiber (lead's new structural route).

Objects (same rational data / conventions as r20-gluing/r23_central_screen_audit.py, which is the
instrument of C904; I re-implement the two checks minimally here, in exact rational interval
arithmetic, and first CALIBRATE on C904's known margin):

  rings C[0..8] = certified_object centers reordered by NEW2RAW_RINGS; r box about
  r0 = 3799838531198387090485182/10^25 with halfwidth omega.
  pins[i] = inner ring-circle intersection of C[i],C[i+1] (unique |p|<1).
  Hub A: variance weights WL on pins (4,6,8)  -> bA, epsA with |a-bA| <= epsA for every a in all
         closed disks B(pin_j,r), j in FAN_A=[4..8];  KA = rectangle enclosing
         B(0,1-r) ∩ ∩_j B(pin_j,r) ∩ B(bA,epsA)  (strict ball relaxed to closed for the enclosure).
  Hub B: WB = (1/2,1/2) on pins (0,3) -> bB, epsB, KB likewise with FAN_B=[0,1,2,3].

  ORIGINAL direction (C904): for the chord (a in KA-box, C[i]), i in CENTRAL={0,4}, the FAR
    radius-r circle intersection (that one on the side of bB opposite to ... ) is at distance
    > r + epsB from bB:  G = dist_lo(q_far, bB) - epsB_hi - r_hi  (C904 reports G ~ .0245).
  MIRROR direction (the pilot): chord (b in KB-box, C[i]) with reference aA:
    G' = dist_lo(q_far', aA) - epsA_hi - r_hi  > 0  ?
  If G' > 0 for both central faces, then for every (a,b) in KA x KB the far branch is excluded in
  EACH variable, hence the surviving central-fibre constraint is |variable - pin(othe rvar)| <= r,
  a disk in each variable  =>  BICONVEX on the box (still not jointly convex).

Writes only in r20-stress/out .
"""
import json
from fractions import Fraction as F
from pathlib import Path

W = Path(__file__).parent
OUT = W / 'out'
ROOT = W.parents[2]
NEW2RAW_RINGS = [5, 7, 1, 8, 6, 4, 9, 10, 3]
FAN_A = [4, 5, 6, 7, 8]
FAN_B = [0, 1, 2, 3]
CENTRAL = [0, 4]
WL = [(F(459977731, 10 ** 9), 4), (F(80044539, 10 ** 9), 6), (F(459977730, 10 ** 9), 8)]
WB = [(F(1, 2), 0), (F(1, 2), 3)]
R0 = F(3799838531198387090485182, 10 ** 25)
DELTA = F(1, 1000)
OMEGA = F(1, 10000)

# ---------------------------------------------------------------- FROZEN Fraction KERNEL (v1)
# Freeze policy (lead): all inputs are exact rationals with explicit denominators; every interval
# operation is a directed (outward) rational enclosure; three degeneracies are handled EXPLICITLY,
# never by "the case lies outside the domain":
#   (1) k = 0 (chord |u| = 2r, tangent radius-r circles) collapses the two branches -> we REQUIRE the
#       radicand interval rad = r^2 - |u|^2/4 to have strictly positive LOWER bound, and report it;
#   (2) collinearity of a, b, C_i (degenerate central face, rho = +inf) -> NOT vacuous: the
#       near-disk condition is shown equal-false with rho <= r on that stratum (|a-q_in'| = |a-q_out'|
#       plus the certified F_out > 0);
#   (3) norm denominators: sqrt enclosures (sqrt_lo/sqrt_hi) use the radicand's own denominator with
#       an integer isqrt floor plus a rational step, so every bound stays rational.
# Denominator ledger (every rational constant):
#   ring centres       : integers / 10^17   (certified_object.json centers_scaled_1e17)
#   ring half-width    : DELTA  = 1/1000
#   radius centre      : R0     = 3799838531198387090485182 / 10^25 ; OMEGA = 1/10000
#   variance weights A : WL     = (459977731, 80044539, 459977730) / 10^9
#   variance weights B : WB     = 1/2  each
#   all bboxes / sums / products / quotients: exact Fractions (no float in the certificate path)
KERNEL = {
    'name': 'r20-stress Fraction interval kernel', 'version': 1,
    'constants_denominators': {'centres': '10^17', 'delta': '10^3', 'R0': '10^25', 'omega': '10^4',
                               'WL': '10^9', 'WB': '2'},
    'strict_k_positive_required': True,
    'collinearity_policy': 'explicit, not vacuous: F_in = F_out > 0 on the collinear stratum',
    'float_free': True,
}


def iv(a, b=None):
    b = a if b is None else b
    return (a, b) if a <= b else (b, a)


def iadd(A, B):
    return (A[0] + B[0], A[1] + B[1])


def isub(A, B):
    return (A[0] - B[1], A[1] - B[0])


def imul(A, B):
    p = [A[0] * B[0], A[0] * B[1], A[1] * B[0], A[1] * B[1]]
    return (min(p), max(p))


def idiv(A, B):
    assert B[0] > 0 or B[1] < 0, 'division by zero-containing interval'
    q = [A[0] / B[0], A[0] / B[1], A[1] / B[0], A[1] / B[1]]
    return (min(q), max(q))


def iscale(A, s):
    return (A[0] * s, A[1] * s) if s >= 0 else (A[1] * s, A[0] * s)


def sqrt_lo(x):
    if x <= 0:
        return F(0)
    lo = F(int(x ** F(1, 2)) if False else 0)
    # integer sqrt enclosure
    n, d = x.numerator, x.denominator
    import math
    a = math.isqrt(n * d)          # sqrt(n/d) ~ a/d  (floor)
    s = F(a, d)
    while s * s > x:
        s -= F(1, d)
    while (s + F(1, d)) ** 2 <= x:
        s += F(1, d)
    return s


def sqrt_hi(x):
    if x <= 0:
        return F(0)
    s = sqrt_lo(x)
    return s if s * s == x else s + F(1, x.denominator)


NEG_RADICANDS = []          # explicit ledger of negative-radicand portions (never silent)


def sqrt_iv(A, tag=''):
    if A[1] < 0:
        raise RuntimeError('sqrt_iv: DOMAIN INVALID (upper endpoint %s < 0) tag=%r -- fail, no silent 0'
                           % (A[1], tag))
    if A[0] < 0:
        # outward-valid enclosure on the domain-valid part; the negative portion is RECORDED, not ignored
        NEG_RADICANDS.append({'tag': tag, 'lo': str(A[0]), 'hi': str(A[1])})
        return (F(0), sqrt_hi(A[1]))
    return (sqrt_lo(A[0]), sqrt_hi(A[1]))


def dot(A, B):
    return iadd(imul(A[0], B[0]), imul(A[1], B[1]))


def det(A, B):
    return isub(imul(A[0], B[1]), imul(A[1], B[0]))


def norm(A):
    return sqrt_iv(dot(A, A))


def vadd(A, B):
    return (iadd(A[0], B[0]), iadd(A[1], B[1]))


def vsub(A, B):
    return (isub(A[0], B[0]), isub(A[1], B[1]))


def vscale_iv(A, K):
    return (imul(A[0], K), imul(A[1], K))


def vscale(A, s):
    return (iscale(A[0], s), iscale(A[1], s))


def bbox_disk(c, rad):
    return ((isub(c[0], rad)[0], iadd(c[0], rad)[1]), (isub(c[1], rad)[0], iadd(c[1], rad)[1]))


def bbox_inter(boxes):
    x0 = max(b[0][0] for b in boxes)
    x1 = min(b[0][1] for b in boxes)
    y0 = max(b[1][0] for b in boxes)
    y1 = min(b[1][1] for b in boxes)
    if x0 > x1 or y0 > y1:
        raise RuntimeError('bbox_inter: EMPTY intersection (inverted box) x=[%s,%s] y=[%s,%s] -- '
                           'fail explicitly, never use a reversed box' % (x0, x1, y0, y1))
    return ((x0, x1), (y0, y1))


def fs(x, n=12):
    return float(x) if abs(x) > F(10) ** 6 else round(float(x), n)


RAD_LO_SEEN = []             # every radicand (r^2 - |u|^2/4) lower bound actually examined

raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
Pf = [(F(int(x[0]), 10 ** 17), F(int(x[1]), 10 ** 17)) for x in raw['centers_scaled_1e17']]
C = [Pf[NEW2RAW_RINGS[i]] for i in range(9)]
rings = [(iv(c[0] - DELTA, c[0] + DELTA), iv(c[1] - DELTA, c[1] + DELTA)) for c in C]
rI = iv(R0 - OMEGA, R0 + OMEGA)
r2 = imul(rI, rI)

# ---- pins (inner ring-circle intersections)
pins = {}
PIN_WHY = {}
for i in range(9):
    A, B = rings[i], rings[(i + 1) % 9]
    u = vsub(B, A)
    d2 = dot(u, u)
    d = sqrt_iv(d2)
    rad = isub(r2, iscale(d2, F(1, 4)))
    k = sqrt_iv((rad[0] if rad[0] > 0 else F(0), rad[1]))
    m = vscale(vadd(A, B), F(1, 2))
    n = (idiv(iv(-u[1][1], -u[1][0]), d), idiv(u[0], d))
    p1 = vadd(m, vscale_iv(n, k))
    p2 = vsub(m, vscale_iv(n, k))
    n1, n2 = norm(p1), norm(p2)
    if n1[1] < 1 and n2[0] >= 1:
        pins[i], why = p1, 'p1 unique |p|<1'
    elif n2[1] < 1 and n1[0] >= 1:
        pins[i], why = p2, 'p2 unique |p|<1'
    elif n1[1] < n2[0]:
        pins[i], why = p1, 'p1 smaller norm'
    elif n2[1] < n1[0]:
        pins[i], why = p2, 'p2 smaller norm'
    else:
        raise RuntimeError('pin %d UNDECIDED: no sufficient guard (n1=%s n2=%s) -- refuse to choose'
                           % (i, n1, n2))
    PIN_WHY[i] = why


def hub(weights):
    b = (iv(F(0)), iv(F(0)))
    V = iv(F(0))
    for (w, i) in weights:
        b = vadd(b, vscale(pins[i], w))
    for ai in range(len(weights)):
        for bi in range(ai + 1, len(weights)):
            (wi, ii), (wj, jj) = weights[ai], weights[bi]
            V = iadd(V, iscale(dot(vsub(pins[ii], pins[jj]), vsub(pins[ii], pins[jj])), wi * wj))
    return V, b


VA, bA = hub(WL)
VB, bB = hub(WB)
epsA = sqrt_iv((max(isub(r2, VA)[0], F(0)), isub(r2, VA)[1]))
epsB = sqrt_iv((max(isub(r2, VB)[0], F(0)), isub(r2, VB)[1]))
one_minus_r = isub(iv(F(1)), rI)


def kbox(bb, eps, fan):
    boxes = [bbox_disk((iv(F(0)), iv(F(0))), one_minus_r)]
    boxes += [bbox_disk(pins[j], rI) for j in fan]
    boxes.append(bbox_disk(bb, eps))
    return bbox_inter(boxes)


KA = kbox(bA, epsA, FAN_A)
KB = kbox(bB, epsB, FAN_B)
Abox = (iv(KA[0][0], KA[0][1]), iv(KA[1][0], KA[1][1]))
Bbox = (iv(KB[0][0], KB[0][1]), iv(KB[1][0], KB[1][1]))
print('KA rect x[%s,%s] y[%s,%s]' % (fs(KA[0][0]), fs(KA[0][1]), fs(KA[1][0]), fs(KA[1][1])))
print('KB rect x[%s,%s] y[%s,%s]' % (fs(KB[0][0]), fs(KB[0][1]), fs(KB[1][0]), fs(KB[1][1])))
print('epsA<=%s epsB<=%s ; |bA|+epsA=%s |bB|+epsB=%s ; 1-r>=%s'
      % (fs(epsA[1]), fs(epsB[1]), fs(norm(bA)[1] + epsA[1]), fs(norm(bB)[1] + epsB[1]), fs(one_minus_r[0])))


def far_branch_margin(chordbox, other, ref):
    """chordbox = box for one endpoint; other = fixed ring center (interval);
    ref = reference point (interval) choosing the far branch.
    returns (margin, branch) with margin = dist_lo(q_far, ref) - eps_hi_of_chord_owner - r_hi
    -- computed by the caller passing the right eps.  Here we return dist and label."""
    A = chordbox
    u = vsub(other, A)
    d2 = dot(u, u)
    d = sqrt_iv(d2)
    rad = isub(r2, iscale(d2, F(1, 4)))
    if rad[1] <= 0:
        return None, 'radicand<=0 (k=0/tangency or no circle-circle intersection)'
    k_zero_possible = (rad[0] <= 0)          # k=0 stratum inside the box: reported, not silently used
    RAD_LO_SEEN.append(rad[0])
    k = sqrt_iv((rad[0] if rad[0] > 0 else F(0), rad[1]))
    m = vscale(vadd(A, other), F(1, 2))
    n = (idiv(iv(-u[1][1], -u[1][0]), d), idiv(u[0], d))
    qp = vadd(m, vscale_iv(n, k))
    qm = vsub(m, vscale_iv(n, k))
    sref = det(u, vsub(ref, A))
    tag = ' (k=0 stratum inside box: excluded by the strict-gap/equality argument)' if k_zero_possible else ''
    if sref[0] > 0:
        return norm(vsub(ref, qm)), 'qm' + tag
    if sref[1] < 0:
        return norm(vsub(ref, qp)), 'qp' + tag
    return None, 'sref straddles 0'


res = {'kernel': KERNEL, 'pin_attribution': PIN_WHY, 'negative_radicands': NEG_RADICANDS,
       'n_radicand_lower_bounds_seen': len(RAD_LO_SEEN),
       'radicand_lower_bound_min': fs(min(RAD_LO_SEEN), 18) if RAD_LO_SEEN else None,
       'radicand_lower_bounds_all_positive': bool(all(x > 0 for x in RAD_LO_SEEN)),
       'k_strictly_positive_for_mirrored_checks': None,
       'parameters': {'delta': str(DELTA), 'omega': str(OMEGA), 'r0': str(R0),
                      'rates_of_r': [fs(rI[0], 18), fs(rI[1], 18)]},
       'epsA_hi': fs(epsA[1]), 'epsB_hi': fs(epsB[1])}
print()
print('=== calibration: ORIGINAL direction (C904): chord (a in KA box, C[i]), reference bB ===')
orig = {}
for i in CENTRAL:
    dist, lbl = far_branch_margin(Abox, rings[i], bB)
    if dist is None:
        orig[i] = {'ok': False, 'reason': lbl}
        print('   face_%d: undecided (%s)' % (i, lbl))
        continue
    G = dist[0] - epsB[1] - rI[1]
    orig[i] = {'G_lo': fs(G), 'branch': lbl, 'dist': [fs(dist[0]), fs(dist[1])]}
    print('   face_%d: far branch %s ; dist_far >= %s ; G = dist_lo - epsB_hi - r_hi = %s  (>0 ? %s)'
          % (i, lbl, fs(dist[0], 10), fs(G), G > 0))
res['original'] = orig

print()
print('=== pilot: MIRRORED direction: chord (b in KB box, C[i]), reference aA ===')
mir = {}
for i in CENTRAL:
    dist, lbl = far_branch_margin(Bbox, rings[i], bA)
    if dist is None:
        mir[i] = {'ok': False, 'reason': lbl}
        print('   face_%d: undecided (%s)' % (i, lbl))
        continue
    Gp = dist[0] - epsA[1] - rI[1]
    mir[i] = {'G_lo': fs(Gp), 'branch': lbl, 'dist': [fs(dist[0]), fs(dist[1])]}
    print('   face_%d: far branch %s ; dist_far >= %s ; G\' = dist_lo - epsA_hi - r_hi = %s  (>0 ? %s)'
          % (i, lbl, fs(dist[0], 10), fs(Gp), Gp > 0))
res['mirrored'] = mir
ok = all(v.get('G_lo', F(-1)) > 0 for v in mir.values())
res['biconvexity_supported'] = bool(ok)
print()
print('   MIRRORED FAR-EXCLUSION for both central faces:', ok)
print('   => if True: on KA x KB the surviving central constraint is a disk in EACH variable')
print('      (biconvex, still not jointly convex).  If False: biconvexity unproven at this box.')
# ledger fields must be filled AFTER the checks ran (they are computed by the calls themselves)
res['n_radicand_lower_bounds_seen'] = len(RAD_LO_SEEN)
res['radicand_lower_bound_min'] = fs(min(RAD_LO_SEEN), 18) if RAD_LO_SEEN else None
res['radicand_lower_bounds_all_positive'] = bool(RAD_LO_SEEN) and all(x > 0 for x in RAD_LO_SEEN)
res['original_k_strictly_positive'] = all('k=0' not in v.get('branch', '') for v in res['original'].values() if isinstance(v, dict))
res['mirrored_k_strictly_positive'] = all('k=0' not in v.get('branch', '') for v in res['mirrored'].values() if isinstance(v, dict))
print('   radicand ledger: %d checks, min lower bound %s ; k>0: original=%s mirrored=%s'
      % (len(RAD_LO_SEEN), res['radicand_lower_bound_min'], res['original_k_strictly_positive'],
         res['mirrored_k_strictly_positive']))
(OUT / 'central_fiber_biconvexity_pilot.json').write_text(json.dumps(res, indent=2), encoding='utf-8')
print('[done] -> out/central_fiber_biconvexity_pilot.json')
