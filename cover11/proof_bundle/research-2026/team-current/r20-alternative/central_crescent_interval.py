"""central_crescent_interval.py  (r20-alternative)  --- v2 (lead code review applied)

Interval certificate for the central-face crescent interface over a RING BOX with a MOVING
hub-A piece, and the resulting 2-hub convex screen data.

v2 fixes (per lead review):
  * weights are EXACT rationals (iv.mpf(num)/iv.mpf(den)); no float() conversion anywhere in
    the constraint evaluation  -> the variance identity keeps its exact lambda (sum 1, products);
  * output is dumped as 30-digit endpoint strings AND directed floats (math.nextafter);
  * every square root has an explicit legality contract:
      - pin radicand r^2-d^2/4 : needs d<2r (C879 legality); if UB(radicand)<0 -> ILLEGAL
        (no pin exists in the box), returned as UNDECIDED, never silently clamped;
      - central-circle radicand r^2-|AC|^2/4 : if UB<0 the crescent is EMPTY for the whole box
        (|AC|>2r => rho>=|AC|/2>r) -> the box is EXCLUDED; if not decidable -> UNDECIDED;
      - localisation radicand r^2-V : V>=0 holds algebraically (nonneg weights), so clamping the
        lower end to 0 is justified; if UB(r^2-V)<0 -> V>r^2 for the whole box -> SCREEN-EXCLUDED
        (no feasible hub), otherwise eps = sqrt(UB) is an upper bound;
  * disk bounding boxes use OUTER SCALAR endpoints:  ((cx.a-rhi, cx.b+rhi),(cy.a-rhi, cy.b+rhi));
    box intersection is max/min over scalars, not over intervals;
  * r0 is the SAVED RATIONAL UPPER OBJECT (UB* / C529 line), NOT the exact root; no claim that
    any box covers the exact optimum (fixed-root inclusion unproven).

Conventions: R^2 vectors are pairs of intervals; lo/hi always mean directed outer endpoints.
"""
import json
import math
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp
from mpmath import iv

iv.dps = 40
mp.dps = 40
OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]

# ------------------------------------------------------------------ exact nominal data
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
Pf = [(F(int(x[0]), 10**17), F(int(x[1]), 10**17)) for x in raw['centers_scaled_1e17']]
NEW2RAW_RINGS = [5, 7, 1, 8, 6, 4, 9, 10, 3]
FAN_A, FAN_B, CENTRAL = [4, 5, 6, 7, 8], [0, 1, 2, 3], [0, 4]
R_UB = F(3799838531198387090485182, 10**25)      # SAVED RATIONAL UPPER OBJECT (UB*), NOT the root
WL = [(F(459977731, 10**9), 4), (F(80044539, 10**9), 6), (F(459977730, 10**9), 8)]
WB = [(F(1, 2), 0), (F(1, 2), 3)]


def M(fr):
    """exact enclosure of a rational (numerator/denominator are exact integers)"""
    return iv.mpf(fr.numerator) / iv.mpf(fr.denominator)


C_NOM = [(M(Pf[i][0]), M(Pf[i][1])) for i in NEW2RAW_RINGS]
R_NOMI = M(R_UB)


# ------------------------------------------------------------------ interval helpers
def I(x):
    return iv.mpf([x, x])


def vadd(A, B):
    return (A[0] + B[0], A[1] + B[1])


def vsub(A, B):
    return (A[0] - B[0], A[1] - B[1])


def vscale(A, s):
    return (A[0] * s, A[1] * s)


def dot(A, B):
    return A[0] * B[0] + A[1] * B[1]


def det(A, B):
    return A[0] * B[1] - A[1] * B[0]


def isqrt_up(x):
    """upper enclosure of sqrt on the legal set {arg >= 0}. None if arg < 0 is certified."""
    if x.b < 0:
        return None
    lo = x.a if x.a > 0 else iv.mpf(0)
    return iv.sqrt(iv.mpf([lo, x.b]))


def vnorm_up(A):
    return isqrt_up(dot(A, A))


def ep_lo(x):
    """scalar lower endpoint as mpf (iv.endpoints are degenerate intervals in this mpmath)"""
    return mp.mpf(x.a)


def ep_hi(x):
    return mp.mpf(x.b)


def fs_lo(x, digits=30):
    return mp.nstr(ep_lo(x), digits)


def fs_hi(x, digits=30):
    return mp.nstr(ep_hi(x), digits)


def fl_out(x):
    """directed float for the lower end (round down one ulp)"""
    return math.nextafter(float(ep_lo(x)), -math.inf)


def fu_out(x):
    """directed float for the upper end (round up one ulp)"""
    return math.nextafter(float(ep_hi(x)), math.inf)


def rect_str(box):
    return [[fs_lo(box[0][0]), fs_hi(box[0][1])], [fs_lo(box[1][0]), fs_hi(box[1][1])]]


def rect_float(box):
    return [[fl_out(box[0][0]), fu_out(box[0][1])], [fl_out(box[1][0]), fu_out(box[1][1])]]


def is_point_iv(x):
    """True iff x bounds a single scalar (degenerate interval) -- used to ASSERT that rectangle
    endpoints are scalars, not intervals."""
    return x.b - x.a == 0


def disk_bbox(center, radius):
    """OUTER axis-aligned rectangle of {|p-c| <= rho : c in center, rho in radius}, stored with
    SCALAR endpoints.  Each coordinate is computed as an interval and only then the outer
    endpoint is taken:  (cx - rho).a  and  (cx + rho).b  (same for y).
    (v2 stored possibly non-degenerate interval objects here -- lead review.)"""
    xlo = (center[0] - radius).a
    xhi = (center[0] + radius).b
    ylo = (center[1] - radius).a
    yhi = (center[1] + radius).b
    for v in (xlo, xhi, ylo, yhi):
        assert is_point_iv(v), 'bbox endpoint is not a scalar'
    return ((xlo, xhi), (ylo, yhi))


def bbox_intersection(boxes):
    """intersection of rectangles with scalar endpoints"""
    xlo = max(b[0][0] for b in boxes)
    xhi = min(b[0][1] for b in boxes)
    ylo = max(b[1][0] for b in boxes)
    yhi = min(b[1][1] for b in boxes)
    return ((xlo, xhi), (ylo, yhi))


def box_empty(box):
    return box[0][0] > box[0][1] or box[1][0] > box[1][1]


def box_bounds(box):
    """interval vector covering the scalar rectangle"""
    return (iv.mpf([box[0][0], box[0][1]]), iv.mpf([box[1][0], box[1][1]]))


def box_center_radius_up(box):
    """centre as scalars; radius as an OUTWARD upper bound sqrt(half-diagonal^2) (no re-wrapping
    of an interval inside a list, which is how v3 could shrink an endpoint)."""
    cx, cy = (box[0][0] + box[0][1]) / 2, (box[1][0] + box[1][1]) / 2
    dx = box[0][1] - box[0][0]
    dy = box[1][1] - box[1][0]
    rad = dx * dx / 4 + dy * dy / 4
    return (cx, cy), iv.sqrt(iv.mpf([mp.mpf(0), ep_hi(rad)]))


# ------------------------------------------------------------------ ring box and pins
def ring_box(delta_iv, w_iv):
    """delta_iv, w_iv are INTERVALS that CONTAIN the exact rational domain targets
    (e.g. M(F(1,1000))); the widening uses their outward endpoints only, so the returned ring
    box provably contains the exact rational box c_i +/- 1/1000, r0 +/- 1/10000."""
    dl = ep_hi(delta_iv)
    wl = ep_hi(w_iv)
    D = iv.mpf([-dl, dl])
    rings = [(c[0] + D, c[1] + D) for c in C_NOM]
    return rings, R_NOMI + iv.mpf([-wl, wl])


def pin_iv(rings, rI, i):
    """inner radical-line point p_in of ring pair (i,i+1) at radius r. Legality: d<2r."""
    A, B = rings[i], rings[(i + 1) % 9]
    u = vsub(B, A)
    d2 = dot(u, u)
    d = isqrt_up(d2)
    if d is None:
        return None, 'UNDECIDED: d^2<0'
    if not (ep_lo(d) > 0):
        return None, 'UNDECIDED: pair distance not certified >0 (interval correlation)'
    if not (ep_hi(d) < mp.inf):
        return None, 'UNDECIDED: pair distance not finite'
    rad = rI * rI - d2 / 4
    if rad.b < 0:
        return None, 'ILEGAL: d>2r in the box (no pin; C879 legality fails)'
    k = iv.sqrt(iv.mpf([ep_lo(rad) if ep_lo(rad) > 0 else mp.mpf(0), ep_hi(rad)]))
    m = vscale(vadd(A, B), M(F(1, 2)))
    n = (-u[1] / d, u[0] / d)
    p1, p2 = vadd(m, vscale(n, k)), vsub(m, vscale(n, k))
    n1, n2 = vnorm_up(p1), vnorm_up(p2)
    if n1 is None or n2 is None:
        return None, 'UNDECIDED: pin norm radicand'
    # root attribution.  C879 (legal tuple): one root p_in lies strictly inside the unit disk and
    # the other p_out is outside int D, so on legal tuples the inner root is the smaller-norm root
    # AND the unique root with |.| < 1.  We certify whichever of the two criteria is decidable on
    # the box; tuples where BOTH roots are inside the unit disk are NOT C879-legal and are outside
    # the claim (the certificate is only asserted for legal tuples of the box).
    if n1.b < 1 and n2.a >= 1:
        return p1, 'inner=p1 (unit-disk criterion)'
    if n2.b < 1 and n1.a >= 1:
        return p2, 'inner=p2 (unit-disk criterion)'
    if n1.b < n2.a:
        return p1, 'inner=p1 (smaller-norm criterion; C879 attribution for legal tuples)'
    if n2.b < n1.a:
        return p2, 'inner=p2 (smaller-norm criterion; C879 attribution for legal tuples)'
    return None, ('UNDECIDED: inner-root selection (both root conventions undecided; note tuples '
                  'with both roots inside the unit disk are not C879-legal and are excluded from '
                  'the claim)')


def variance_pair(pins, weights):
    """V = sum_{i<j} l_i l_j |p_i-p_j|^2 and b = sum l_i p_i, EXACT rational weights."""
    V = I(0)
    b = (I(0), I(0))
    for (wi, ii) in weights:
        b = vadd(b, vscale(pins[ii], M(wi)))
    for a_i in range(len(weights)):
        for b_i in range(a_i + 1, len(weights)):
            (wi, ii), (wj, jj) = weights[a_i], weights[b_i]
            V = V + M(wi * wj) * dot(vsub(pins[ii], pins[jj]), vsub(pins[ii], pins[jj]))
    return V, b


# ------------------------------------------------------------------ certificate
def certificate(delta, w):
    rings, rI = ring_box(delta, w)
    out = {'delta_interval_str': [fs_lo(delta), fs_hi(delta)],
           'w_interval_str': [fs_lo(w), fs_hi(w)],
           'r_upper_endpoint_str': fs_hi(rI, 25),
           'r_label': 'saved rational upper object UB* (C529 line), NOT the exact root; no claim '
                      'that this box covers the exact optimum'}
    pins, status = {}, {}
    for i in range(9):
        p, s = pin_iv(rings, rI, i)
        pins[i], status[i] = p, s
    out['pin_status'] = status
    if any(p is None for p in pins.values()):
        out['result'] = ('UNDECIDED/ILEGAL: pins ' +
                         ','.join(str(i) for i in pins if pins[i] is None))
        return out
    KA_boxes = [disk_bbox((I(0), I(0)), 1 - rI)] + [disk_bbox(pins[j], rI) for j in FAN_A]
    KB_boxes = [disk_bbox((I(0), I(0)), 1 - rI)] + [disk_bbox(pins[j], rI) for j in FAN_B]
    KB_bb = bbox_intersection(KB_boxes)
    # hub-B localisation: exact rational weights 1/2,1/2 on chain pins 0,3
    VB, bB = variance_pair(pins, WB)
    radB = rI * rI - VB
    if radB.b < 0:
        out['result'] = 'SCREEN-EXCLUDED: V_B>r^2 in the whole box (no feasible hub B)'
        return out
    epsB = iv.sqrt(iv.mpf([ep_lo(radB) if ep_lo(radB) > 0 else mp.mpf(0), ep_hi(radB)]))
    # hub-A piece = K_A bbox INTERSECT localisation ball (fixed rational weights on pins 4,6,8)
    VA, bA = variance_pair(pins, WL)
    radA = rI * rI - VA
    if radA.b < 0:
        out['result'] = 'SCREEN-EXCLUDED: V_A>r^2 in the whole box (no feasible hub A)'
        return out
    epsA = iv.sqrt(iv.mpf([ep_lo(radA) if ep_lo(radA) > 0 else mp.mpf(0), ep_hi(radA)]))
    locA = (((bA[0] - epsA).a, (bA[0] + epsA).b), ((bA[1] - epsA).a, (bA[1] + epsA).b))
    for v in (locA[0][0], locA[0][1], locA[1][0], locA[1][1]):
        assert is_point_iv(v), 'locA endpoint is not a scalar'
    KA_box = bbox_intersection(KA_boxes + [locA])
    if box_empty(KA_box) or box_empty(KB_bb):
        out['result'] = ('SCREEN-EXCLUDED: empty K_%s rectangle in this ring box'
                         % ('A' if box_empty(KA_box) else 'B'))
        return out
    out['hubA_localisation_eps'] = [fs_lo(epsA), fs_hi(epsA)]
    out['hubA_b'] = [fs_lo(bA[0]), fs_hi(bA[0]), fs_lo(bA[1]), fs_hi(bA[1])]
    out['hubB_localisation_eps'] = [fs_lo(epsB), fs_hi(epsB)]
    out['hubB_b'] = [fs_lo(bB[0]), fs_hi(bB[0]), fs_lo(bB[1]), fs_hi(bB[1])]
    out['K_A_rect_str'] = rect_str(KA_box)
    out['K_B_rect_str'] = rect_str(KB_bb)
    out['K_A_rect_float'] = rect_float(KA_box)
    out['K_B_rect_float'] = rect_float(KB_bb)
    Abox = box_bounds(KA_box)
    # --- structural calibrations requested by the independent auditor -----------------
    nbA, nbB = vnorm_up(bA), vnorm_up(bB)
    out['strict_hub_norm_margin'] = {
        '|bA|_up + epsA_up': fs_hi(nbA + epsA) if nbA is not None else None,
        '|bB|_up + epsB_up': fs_hi(nbB + epsB) if nbB is not None else None,
        '1 - r  low end': fs_lo(I(1) - rI),
        'note': '|h_A| <= |b_A| + eps_A and |h_B| <= |b_B| + eps_B for every feasible hub; both '
                'must be < 1 - r (strict hub). NOTE: |p_out| = 1 holds in the exact candidate CHART, not at the rounded nominal centres -- no equality is claimed at the nominal data, only the numerical margin below. '
                'so this strictness is load-bearing (C879 boundary case).'}
    out['radicand_branch_semantics'] = (
        'radicands may cross 0 on the box (central circle r^2-|AC|^2/4 and localisation r^2-V). '
        'The certificate is stated per tuple as a BRANCH: either (i) |AC| > 2r strictly, where the '
        'crescent is empty because rho >= |AC|/2 > r; or (ii) V > r^2, where no hub exists; or '
        '(iii) the corresponding exclusion holds with the clamped upper-end radius.  NOTE (auditor '
        'correction): the boundary case |AC| = 2r (k = 0) is NOT excluded by the rho-argument '
        '(rho >= r does not contradict rho <= r); there q_near = q_far = m, the product identity '
        'degenerates to 4y^2(rho^2-r^2) = (|b-m|^2-r^2)^2, and such tuples are excluded by the '
        'STRICT G bound itself (|b_B - m| - eps_B > r inside the localisation ball).  Collinear '
        '(a,b,c_i) tuples have no circumradius and lie outside the C900 all-cover-graph '
        'non-collinear necessary domain -- they are not treated as vacuously true.')
    _crad = [(rI * rI - dot(vsub(rings[i], Abox), vsub(rings[i], Abox)) / 4) for i in CENTRAL]
    out['central_radicand_boxes'] = [[fs_lo(c), fs_hi(c)] for c in _crad]
    faces = {}
    for i in CENTRAL:
        Ci = rings[i]
        u = vsub(Ci, Abox)
        d2u = dot(u, u)
        rad = rI * rI - d2u / 4
        if rad.b < 0:
            faces['face_%d' % i] = {'status': 'EXCLUDED: |AC|>2r STRICTLY in the box => crescent '
                                              'empty (rho >= |AC|/2 > r). The boundary case '
                                              '|AC| = 2r is not covered by this branch; there '
                                              'q_near = q_far = m and exclusion comes from the '
                                              'strict G bound (auditor correction).'}
            continue
        if u[0].a <= 0 <= u[0].b and u[1].a <= 0 <= u[1].b:
            faces['face_%d' % i] = {'status': 'UNDECIDED: A=C possible in the box'}
            continue
        d = isqrt_up(d2u)
        if d is None or not (ep_lo(d) > 0) or not (ep_hi(d) < mp.inf):
            faces['face_%d' % i] = {'status': 'UNDECIDED: |a-c_i| not certified positive finite'}
            continue
        k = iv.sqrt(iv.mpf([ep_lo(rad) if ep_lo(rad) > 0 else mp.mpf(0), ep_hi(rad)]))
        m = vscale(vadd(Abox, Ci), M(F(1, 2)))
        n = (-u[1] / d, u[0] / d)
        qp, qm = vadd(m, vscale(n, k)), vsub(m, vscale(n, k))
        sref = det(u, vsub(bB, Abox))
        if sref.a > 0:
            qnear, qfar, branch = qp, qm, '+'
        elif sref.b < 0:
            qnear, qfar, branch = qm, qp, '-'
        else:
            faces['face_%d' % i] = {'status': 'UNDECIDED: crescent branch (side of line AC)'}
            continue
        dd = vnorm_up(vsub(bB, qfar))
        if dd is None:
            faces['face_%d' % i] = {'status': 'UNDECIDED: distal-distance radicand'}
            continue
        G = dd - epsB - rI
        Qbox = ((qnear[0].a, qnear[0].b), (qnear[1].a, qnear[1].b))
        (qc, qrad) = box_center_radius_up(Qbox)
        faces['face_%d' % i] = {
            'branch': branch,
            'G_str': [fs_lo(G), fs_hi(G)],
            'G_lo_dyadic_exact': dyadic(G),
            'G_hi_dyadic_exact': dyadic_hi(G),
            'G_float_directed': [fl_out(G), fu_out(G)],
            'certified': bool(G.a > 0),
            'near_disk_centre_rect_str': rect_str(Qbox),
            'near_disk_centre_radius_up_str': fs_hi(qrad),
            'screen_disk_radius_up_str': fs_hi(rI + qrad)}
    out['faces'] = faces
    if any('status' in v for v in faces.values()):
        out['result'] = 'UNDECIDED/EXCLUDED: ' + '; '.join(
            v['status'] for v in faces.values() if 'status' in v)
    else:
        out['result'] = ('CERTIFIED (uniform distal exclusion, both central faces)'
                         if all(v.get('certified') for v in faces.values())
                         else 'FAILED (G lower end <= 0)')
    return out


# ------------------------------------------------------------------ driving
# Lead instruction: no fine delta-bisection down to 6e-13.  Round conservative boxes:
#   delta = 1/1000 (ring coordinates),  w = 1/10000 (r window);  plus delta = 0 as base
#   reading and a distal-FAIL control for criterion discrimination.
D_FIX = F(1, 1000)
W_FIX = F(1, 10000)


def dyadic(x):
    """EXACT binary endpoint dump (sign, mantissa, exponent, bits) of the LOWER endpoint.
    The 30-digit *_str fields are DISPLAY ONLY and are never exact endpoints."""
    return list(mp.mpf(ep_lo(x))._mpf_)


def dyadic_hi(x):
    """EXACT binary endpoint dump of the UPPER endpoint."""
    return list(mp.mpf(ep_hi(x))._mpf_)


def distal_fail_control():
    """Discrimination control for the criterion itself: POS = candidate data with the true b_B
    (G > 0); FAIL = the same data with b_B replaced by the distal centre q'_i, i.e.
    |b_B - q'_i| = 0 < eps_B + r  =>  G < 0."""
    rings, rI = ring_box(iv.mpf([mp.mpf(0), mp.mpf(0)]), iv.mpf([mp.mpf(0), mp.mpf(0)]))
    pins = {i: pin_iv(rings, rI, i)[0] for i in range(9)}
    VB, bB = variance_pair(pins, WB)
    radB = rI * rI - VB
    epsB = iv.sqrt(iv.mpf([ep_lo(radB) if ep_lo(radB) > 0 else mp.mpf(0), ep_hi(radB)]))
    KA_bb = bbox_intersection([disk_bbox((I(0), I(0)), 1 - rI)] +
                              [disk_bbox(pins[j], rI) for j in FAN_A])
    Abox = box_bounds(KA_bb)
    out = {}
    for i in CENTRAL:
        Ci = rings[i]
        u = vsub(Ci, Abox)
        d2u = dot(u, u)
        d = isqrt_up(d2u)
        rad = rI * rI - d2u / 4
        k = iv.sqrt(iv.mpf([ep_lo(rad) if ep_lo(rad) > 0 else mp.mpf(0), ep_hi(rad)]))
        m = vscale(vadd(Abox, Ci), M(F(1, 2)))
        n = (-u[1] / d, u[0] / d)
        qp, qm = vadd(m, vscale(n, k)), vsub(m, vscale(n, k))
        sref = det(u, vsub(bB, Abox))
        qfar = qm if ep_lo(sref) > 0 else qp
        G_pos = vnorm_up(vsub(bB, qfar)) - epsB - rI
        G_fail = vnorm_up(vsub(qfar, qfar)) - epsB - rI
        out['face_%d' % i] = {'POS_G_lo': fs_lo(G_pos), 'POS_certified': bool(ep_lo(G_pos) > 0),
                              'FAIL_G_hi': fs_hi(G_fail),
                              'FAIL_excluded': bool(ep_hi(G_fail) < 0)}
    out['verdict'] = ('criterion discriminates: POS>0 and FAIL<0'
                      if all(v['POS_certified'] and v['FAIL_excluded']
                             for kk, v in out.items() if kk.startswith('face'))
                      else 'CONTROL FAILED')
    return out


report = {'kind': 'interval certificate v3 (lead review: scalar bbox endpoints taken as .a/.b '
                  'AFTER the interval arithmetic, exact dyadic endpoint dumps, round '
                  'conservative boxes, no 6e-13 bisection)',
          'scope': 'q0(6,7) ring box around the SAVED RATIONAL UPPER OBJECT (UB*); no global '
                   'coverage claim, no exact-root inclusion claim',
          'note_display_strings': 'the 30-digit *_str fields are DISPLAY ONLY; the certified '
                                  'endpoints are the exact dyadic (sign, mantissa, exp, bits) '
                                  'tuples emitted in *_dyadic fields, and independently the exact '
                                  'Fraction endpoints of central_crescent_audit2.json'}
D_IV = M(D_FIX)          # interval enclosing the EXACT rational 1/1000
W_IV = M(W_FIX)          # interval enclosing the EXACT rational 1/10000
Z_IV = iv.mpf([mp.mpf(0), mp.mpf(0)])
report['domain_declared'] = {
    'delta': '1/1000 (exact rational)', 'w_r': '1/10000 (exact rational)',
    'note': 'the interval engine receives M(F) targets; ring_box widens only by their outward '
            'endpoints, so the computed box provably contains the exact rational box '
            'c_i +/- 1/1000, r0 +/- 1/10000'}
report['delta0_w0'] = certificate(Z_IV, Z_IV)
report['box_delta_1e-3_w0'] = certificate(D_IV, Z_IV)
report['box_delta_1e-3_w_1e-4'] = certificate(D_IV, W_IV)
report['distal_fail_control'] = distal_fail_control()
for key in ('delta0_w0', 'box_delta_1e-3_w0', 'box_delta_1e-3_w_1e-4'):
    box = report[key]
    if 'hubA_localisation_eps' not in box:
        continue
(OUT / 'central_crescent_interval.json').write_text(json.dumps(report, indent=2), encoding='utf-8')

print('delta0        :', report['delta0_w0']['result'])
print('1e-3 / w=0    :', report['box_delta_1e-3_w0']['result'])
print('1e-3 / 1e-4   :', report['box_delta_1e-3_w_1e-4']['result'])
print('control       :', report['distal_fail_control']['verdict'])
for key in ('delta0_w0', 'box_delta_1e-3_w0', 'box_delta_1e-3_w_1e-4'):
    for i in CENTRAL:
        f = report[key]['faces']['face_%d' % i]
        print('  %-18s face %d  G=[%s , %s]  certified=%s' % (
            key, i, f.get('G_str', ['-', '-'])[0], f.get('G_str', ['-', '-'])[1],
            f.get('certified')))
    print('      eps_A =', report[key].get('hubA_localisation_eps'),
          ' eps_B =', report[key].get('hubB_localisation_eps'))
for i in CENTRAL:
    f = report['distal_fail_control']['face_%d' % i]
    print('  control face %d: POS_G_lo=%s certified=%s | FAIL_G_hi=%s excluded=%s' % (
        i, f['POS_G_lo'], f['POS_certified'], f['FAIL_G_hi'], f['FAIL_excluded']))
print('  screen radii (1e-3/1e-4):',
      [report['box_delta_1e-3_w_1e-4']['faces']['face_%d' % i].get('screen_disk_radius_up_str')
       for i in CENTRAL])
