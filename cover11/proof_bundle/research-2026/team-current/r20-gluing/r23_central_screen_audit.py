# -*- coding: utf-8 -*-
"""r23_central_screen_audit.py — INDEPENDENT read-only audit computation for
r20-alternative/central_crescent_interval.py (v3, pinned by sha256 below).

Self-contained: exact rational interval arithmetic + integer square-root bounds.
NO mpmath, NO shared helpers with the audited file.

Independent derivations (my own):
  * variance identity: for weights l_j >= 0, sum l_j = 1, any b in all B(p_j, r):
        sum_j l_j |b-p_j|^2 = |b - b0|^2 + V,  b0 = sum l_j p_j,  V = sum_{j<k} l_j l_k |p_j-p_k|^2
    => |b - b0| <= sqrt(r^2 - V) =: eps            (variance route; b in all disks)
  * triangle inequality: |hub - q_far| >= |q_far - bB| - eps_B, so the distal disk is excluded
    from the localisation ball whenever |bB - q_far| > eps_B + r.
  * the orientation-preserving branch (near/far) is decided by the sign of det(u, bB - A) over the
    whole A-region -- the same convention as the audited file (never by comparing distances).
  * central-face activity re-checked with my own circumcentre computation (not needed for the
    screen, recorded as cross-check).

Audited revision (pin):
  py  sha256 dcffaf1798728b570db141d3674a56c8fe643e8029314f6bbf028c03f4d27d60
  json sha256 22a78b344c8eccbd5be10e41b5dc54a8ada39ff0d6142a961b2f8563c683c96d
If the audited file changes, re-pin and re-run.
"""
import json
from fractions import Fraction as F
from math import isqrt
from pathlib import Path

HERE = Path(__file__).parent
ROOT = HERE.parents[2] if (HERE.parents[2] / 'n11').exists() else Path(r'C:\Users\袁力阳\Desktop\ai4math2')
S = 10 ** 20
R_UB = F(3799838531198387090485182, 10 ** 25)
NEW2RAW_RINGS = [5, 7, 1, 8, 6, 4, 9, 10, 3]
FAN_A, FAN_B, CENTRAL = [4, 5, 6, 7, 8], [0, 1, 2, 3], [0, 4]
WL = [(F(459977731, 10 ** 9), 4), (F(80044539, 10 ** 9), 6), (F(459977730, 10 ** 9), 8)]
WB = [(F(1, 2), 0), (F(1, 2), 3)]


# ---------------- my own rational interval helpers ----------------
def iv(a, b=None):
    return (F(a), F(a) if b is None else F(b))


def iadd(A, B):
    return (A[0] + B[0], A[1] + B[1])


def isub(A, B):
    return (A[0] - B[1], A[1] - B[0])


def imul(A, B):
    p = [A[0] * B[0], A[0] * B[1], A[1] * B[0], A[1] * B[1]]
    return (min(p), max(p))


def idiv(A, B):
    assert B[0] > 0 or B[1] < 0, 'interval division by a set containing 0'
    p = [A[0] / B[0], A[0] / B[1], A[1] / B[0], A[1] / B[1]]
    return (min(p), max(p))


def iscale(A, s):
    return (A[0] * s, A[1] * s)


def sqrt_lo(x):
    n = x.numerator * x.denominator * S * S
    return F(isqrt(n), x.denominator * S)


def sqrt_hi(x):
    n = x.numerator * x.denominator * S * S
    return F(isqrt(n) + 1, x.denominator * S)


def sqrt_iv(A):
    a0 = A[0] if A[0] > 0 else F(0)
    assert A[1] >= 0, 'sqrt of negative interval'
    return (sqrt_lo(a0), sqrt_hi(A[1]))


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


def vscale(A, s):
    return (iscale(A[0], s), iscale(A[1], s))


def vscale_iv(A, K):
    return (imul(A[0], K), imul(A[1], K))


def fs(x, n=12):
    return '%.*g' % (n, float(F(x)))


def bbox_disk(c, rad):
    return ((isub(c[0], rad)[0], iadd(c[0], rad)[1]), (isub(c[1], rad)[0], iadd(c[1], rad)[1]))


def bbox_inter(boxes):
    return ((max(b[0][0] for b in boxes), min(b[0][1] for b in boxes)),
            (max(b[1][0] for b in boxes), min(b[1][1] for b in boxes)))


# ---------------- the screen at a given exact-rational box ----------------
def screen(C, delta, omega, verbose=True):
    """delta, omega : exact Fractions (ring half-width, r half-width)."""
    rings = [(iv(c[0] - delta, c[0] + delta), iv(c[1] - delta, c[1] + delta)) for c in C]
    rI = iv(R_UB - omega, R_UB + omega)
    r2 = imul(rI, rI)
    out = {'delta': str(delta), 'omega': str(omega), 'r_box': [fs(rI[0], 18), fs(rI[1], 18)]}

    # pins (inner root: C879 attribution = unique |p|<1, else smaller norm)
    pins, pininfo = {}, {}
    d2_lowers = []
    for i in range(9):
        A, B = rings[i], rings[(i + 1) % 9]
        u = vsub(B, A); d2 = dot(u, u); d = sqrt_iv(d2)
        d2_lowers.append(d2[0])
        rad = isub(r2, iscale(d2, F(1, 4)))
        k = sqrt_iv((rad[0] if rad[0] > 0 else F(0), rad[1]))
        m = vscale(vadd(A, B), F(1, 2))
        n = (idiv(iv(-u[1][1], -u[1][0]), d), idiv(u[0], d))
        p1 = vadd(m, vscale_iv(n, k)); p2 = vsub(m, vscale_iv(n, k))
        n1, n2 = norm(p1), norm(p2)
        inner, why = None, 'UNDECIDED'
        if n1[1] < 1 and n2[0] >= 1:
            inner, why = p1, 'p1 unique |p|<1'
        elif n2[1] < 1 and n1[0] >= 1:
            inner, why = p2, 'p2 unique |p|<1'
        elif n1[1] < n2[0]:
            inner, why = p1, 'p1 smaller norm'
        elif n2[1] < n1[0]:
            inner, why = p2, 'p2 smaller norm'
        pins[i] = inner
        pininfo[i] = {'radicand': [fs(rad[0], 8), fs(rad[1], 8)], 'positive': bool(rad[0] > 0),
                      'attribution': why}
    out['pins'] = pininfo
    out['pins_decidable'] = all(pins[i] is not None for i in range(9))
    out['guard_pin_d2_min'] = fs(min(d2_lowers), 12)
    out['guard_pin_d2_positive'] = bool(min(d2_lowers) > 0)

    # variance route for both hubs (exact rational weights)
    def hub(weights):
        V, b = iv(0), (iv(0), iv(0))
        for (w, i) in weights:
            b = vadd(b, vscale(pins[i], w))
        for a_i in range(len(weights)):
            for b_i in range(a_i + 1, len(weights)):
                (wi, ii), (wj, jj) = weights[a_i], weights[b_i]
                V = iadd(V, iscale(dot(vsub(pins[ii], pins[jj]), vsub(pins[ii], pins[jj])), wi * wj))
        return V, b

    VA, bA = hub(WL)
    VB, bB = hub(WB)
    radA, radB = isub(r2, VA), isub(r2, VB)
    epsA = sqrt_iv((max(radA[0], F(0)), radA[1]))
    epsB = sqrt_iv((max(radB[0], F(0)), radB[1]))
    out['radA'] = [fs(radA[0], 8), fs(radA[1], 8)]
    out['radB'] = [fs(radB[0], 8), fs(radB[1], 8)]
    out['epsA'] = [fs(epsA[0], 8), fs(epsA[1], 8)]
    out['epsB'] = [fs(epsB[0], 8), fs(epsB[1], 8)]
    out['bB'] = [fs(bB[0][0], 10), fs(bB[0][1], 10), fs(bB[1][0], 10), fs(bB[1][1], 10)]

    # strict-interior requirement |hub| < 1-r for the C879 equivalence
    one_minus_r = isub(iv(1), rI)
    out['strict_interior'] = {
        'one_minus_r': [fs(one_minus_r[0], 10), fs(one_minus_r[1], 10)],
        'bA_plus_epsA': fs(norm(bA)[1] + epsA[1], 10),
        'bB_plus_epsB': fs(norm(bB)[1] + epsB[1], 10),
        'certified': bool(norm(bA)[1] + epsA[1] <= one_minus_r[0]
                          and norm(bB)[1] + epsB[1] <= one_minus_r[0])}

    # sound hub-A rectangle (same construction as the audited file)
    boxes = [bbox_disk((iv(0), iv(0)), isub(iv(1), rI))]
    boxes += [bbox_disk(pins[j], rI) for j in FAN_A]
    boxes.append(((isub(bA[0], epsA)[0], iadd(bA[0], epsA)[1]),
                  (isub(bA[1], epsA)[0], iadd(bA[1], epsA)[1])))
    KA = bbox_inter(boxes)
    out['K_A_rect'] = [[fs(KA[0][0], 12), fs(KA[0][1], 12)], [fs(KA[1][0], 12), fs(KA[1][1], 12)]]
    Abox = (iv(KA[0][0], KA[0][1]), iv(KA[1][0], KA[1][1]))

    faces = {}
    for i in CENTRAL:
        u = vsub(rings[i], Abox)
        d2u = dot(u, u)
        rad = isub(r2, iscale(d2u, F(1, 4)))
        d = sqrt_iv(d2u)
        k = sqrt_iv((max(rad[0], F(0)), rad[1]))
        m = vscale(vadd(Abox, rings[i]), F(1, 2))
        n = (idiv(iv(-u[1][1], -u[1][0]), d), idiv(u[0], d))
        qp = vadd(m, vscale_iv(n, k)); qm = vsub(m, vscale_iv(n, k))
        sref = det(u, vsub(bB, Abox))
        if sref[0] > 0:
            d_far, lbl = norm(vsub(bB, qm)), 'qm (sref>0)'
        elif sref[1] < 0:
            d_far, lbl = norm(vsub(bB, qp)), 'qp (sref<0)'
        else:
            d_far, lbl = None, 'UNDECIDED (sref straddles 0)'
        if d_far is None:
            faces['face_%d' % i] = {'certified': False, 'reason': lbl,
                                    'sref': [fs(sref[0], 8), fs(sref[1], 8)]}
            continue
        G = d_far[0] - epsB[1] - rI[1]
        faces['face_%d' % i] = {'branch': lbl, 'radicand': [fs(rad[0], 8), fs(rad[1], 8)],
                                'sref': [fs(sref[0], 10), fs(sref[1], 10)],
                                'k_interval': [fs(k[0], 10), fs(k[1], 10)],
                                'k_zero_attained': bool(k[0] == 0),
                                'd2u_lower': fs(d2u[0], 10),
                                'dist_far': [fs(d_far[0], 12), fs(d_far[1], 12)],
                                'G_lower': fs(G, 12), 'certified': bool(G > 0)}
    out['faces'] = faces
    out['certified'] = all(f.get('certified') for f in faces.values()) and out['pins_decidable'] \
        and out['strict_interior']['certified']
    if verbose:
        print('  delta=%s omega=%s : epsB<=%s epsA<=%s ; G(face0)=%s G(face4)=%s ; certified=%s'
              % (delta, omega, out['epsB'][1], out['epsA'][1],
                 faces['face_0']['G_lower'], faces['face_4']['G_lower'], out['certified']))
    return out


def main():
    raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
    Pf = [(F(int(x[0]), 10 ** 17), F(int(x[1]), 10 ** 17)) for x in raw['centers_scaled_1e17']]
    C = [Pf[NEW2RAW_RINGS[i]] for i in range(9)]
    hA, hB = Pf[0], Pf[2]
    rec = {'role': 'independent read-only audit of r20-alternative/central_crescent_interval.py',
           'audited_py_sha256': 'dcffaf1798728b570db141d3674a56c8fe643e8029314f6bbf028c03f4d27d60',
           'audited_json_sha256': '22a78b344c8eccbd5be10e41b5dc54a8ada39ff0d6142a961b2f8563c683c96d',
           'method': 'own rational interval arithmetic + integer sqrt bounds; variance identity + '
                     'triangle inequality; orientation-preserving branch by sign of det(u,bB-A)'}
    print('=== nominal box (delta=omega=0) ===')
    rec['nominal'] = screen(C, F(0), F(0))
    # central-face activity via my own circumcentre (cross-check)
    def circum_radius2(p, q, s):
        a2 = (q[0] - s[0]) ** 2 + (q[1] - s[1]) ** 2
        b2 = (s[0] - p[0]) ** 2 + (s[1] - p[1]) ** 2
        c2 = (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2
        cr = (q[0] - p[0]) * (s[1] - p[1]) - (q[1] - p[1]) * (s[0] - p[0])
        return None if cr == 0 else (a2 * b2 * c2) / (4 * cr * cr)
    act = {}
    for i in CENTRAL + [1, 2, 3, 5, 6, 7, 8]:
        r2v = circum_radius2(hA, hB, C[i])
        if r2v is not None:
            act['rho_%d_minus_r' % i] = fs(sqrt_lo(r2v) - R_UB, 6)
    rec['circumradius_crosscheck'] = act
    print('=== lead rational target box: delta=1/1000, omega=1/10000 ===')
    rec['box_1e-3_1e-4'] = screen(C, F(1, 1000), F(1, 10000))
    print('=== robustness: float delta (float(1/1000) > 1/1000) and omega ===')
    df = F(float(F(1, 1000)).as_integer_ratio()[0], float(F(1, 1000)).as_integer_ratio()[1])
    wf = F(float(F(1, 10000)).as_integer_ratio()[0], float(F(1, 10000)).as_integer_ratio()[1])
    rec['box_float_labelled'] = screen(C, df, wf)
    print('  float(1/1000) - 1/1000 = %s (box slightly WIDER; conclusion transports to the exact '
          'rational box)' % fs(df - F(1, 1000), 6))
    rec['float_delta_excess'] = fs(df - F(1, 1000), 6)
    (HERE / 'r23_central_screen_audit.json').write_text(json.dumps(rec, indent=2))
    print('\nsaved r23_central_screen_audit.json')


if __name__ == '__main__':
    main()
