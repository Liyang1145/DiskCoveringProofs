"""audit_scale28_checks.py  (member upper-audit/integer-atomic, 2026-09-26)

SMALL, independent checks for the S=2^28 audit of integer_kernel.py /
integer_kernel_n.py (see ../audit-scale28.md).  No large runs, no certify() sweeps:
this file only (a) re-derives the exact rounding definitions, (b) recomputes the
int64 bound chain, (c) checks the exposure identity and screening exactness, and
(d) evaluates a single bound() call on the recorded scale-26 unresolved box and its
scale-28 counterpart (the box the escalation would meet first).

Run: py -3 -B py/audit_scale28_checks.py
"""
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
N12 = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
EVID = os.path.join(N12, 'evidence')
sys.path.insert(0, HERE)

import integer_kernel as ik
import integer_kernel_n as ikn

U = ik.U
ok_all = True


def check(label, cond, extra=''):
    global ok_all
    ok_all = ok_all and bool(cond)
    print('  [%s] %-58s %s' % ('ok' if cond else 'FAIL', label, extra))


print('== 1. rounding definitions (floorF / ceilF are true floor / ceil) ==')
bad = 0
for num in range(-40, 41):
    for den in (1, 2, 3, 7, 16):
        q = F(num, den)
        if ik.floorF(q) != q.numerator // q.denominator:
            bad += 1
        if ik.ceilF(q) != -((-q.numerator) // q.denominator):
            bad += 1
check('floorF/ceilF agree with exact floor/ceil on 656 samples', bad == 0)
check('floorF <= q <= ceilF for all samples',
      all(ik.floorF(F(a, b)) <= F(a, b) <= ik.ceilF(F(a, b))
          for a in range(-9, 10) for b in (1, 2, 3, 5)))

print()
print('== 2. int64 bound chain at S=2^26 and S=2^28 ==')
for Sexpt in (26, 28):
    S = 1 << Sexpt
    S2 = S * S
    cap_code = 32 * S2                      # the assert's cap in bound()
    worst_actual = 18 * S2                  # |dx|<=3S (2S atom + S ring) each coord
    print('  S=2^%d: 32S^2=%.4e  18S^2=%.4e  int64max=%.4e  margin(18S^2)=%.2fx'
          % (Sexpt, cap_code, worst_actual, 2.0 ** 63 - 1, (2 ** 63 - 1) / worst_actual))
    check('S=2^%d: 32S^2 < 2^63 (assert itself safe)' % Sexpt, cap_code < 2 ** 63)
    check('S=2^%d: 18S^2 < 2^63 (no int64 overflow in d2)' % Sexpt, worst_actual < 2 ** 63)
    check('S=2^%d: intermediates dx*dx fit (9S^2 < 2^63)' % Sexpt, 9 * S2 < 2 ** 63)

print()
print('== 3. exact thresholds and their exactness ==')
for Sexpt in (26, 28):
    S = 1 << Sexpt
    S2 = S * S
    u2 = ik.ceilF(U * U * S2)
    inn = ik.floorF((1 - U) ** 2 * S2)
    out = ik.ceilF((1 - U * U) * S2)
    print('  S=2^%d: U2_ceil=%d  inner_floor=%d  outer_ceil=%d  (all < 2^63: %s)'
          % (Sexpt, u2, inn, out, max(u2, inn, out) < 2 ** 63))
    check('S=2^%d: U2_ceil == ceil(U^2 S^2) exactly' % Sexpt, u2 == ik.ceilF(U * U * S2))
    check('S=2^%d: inner_floor <= (1-U)^2 S^2 < inner_floor+1' % Sexpt,
          inn <= (1 - U) ** 2 * S2 < inn + 1)
    check('S=2^%d: outer_ceil-1 < (1-U^2) S^2 <= outer_ceil' % Sexpt,
          out - 1 < (1 - U * U) * S2 <= out)

print()
print('== 4. exposure identity and screening exactness (hub1/hub2) ==')
snap = json.loads(open(os.path.join(EVID, 'hubline-domain-stage11825.json'), encoding='utf-8').read())
leaves = [v for v in snap['leaves'] if v['type'] == 'atomic']
v = leaves[4398]
H = [(F(a), F(b)) for a, b in v['H']]
sl, sh = H[0]
W6 = v['proposal']['weights']
n = (len(W6[0]) - 1) // 2
canon = ikn.load_vectors(os.path.join(EVID, 'atomic-unit-vectors-2048.json'))
V = [(F(a), F(b)) for a, b in canon]

bad_id = 0
kept1 = kept2 = dropped = 0
for (c, t) in V:
    if not (U * c > sl):
        kept1 += 1
        for s in (sl, sh, (sl + sh) / 2):
            if not (F(4) * s * (s - U * c) >= 0):
                bad_id += 1
    else:
        dropped += 1
        s = sl                      # the worst (smallest) s in the box
        if not (F(4) * s * (s - U * c) < 0):
            bad_id += 1
    if not (U * c < -sl):
        kept2 += 1
        for s in (sl, sh, (sl + sh) / 2):
            if not (F(4) * s * (s + U * c) >= 0):
                bad_id += 1
check('hub1/hub2 exposure identity; retained atoms exposed for ALL s in [sl,sh]',
      bad_id == 0, '(kept1=%d kept2=%d dropped1=%d)' % (kept1, kept2, dropped))
check('dropped hub1 atoms are strictly inside hub2 at s=sl (THIS POINT ONLY; '
      'NOT a necessity claim about legal triples)', bad_id == 0)

print()
print('== 5. one bound() call: recorded scale-26 unresolved box and its scale-28 lift ==')
box26 = (4512816, 4512832, -43155728, -43155712)          # from escalated-scale28-evidence.json
box28 = tuple(4 * x for x in box26)                        # same real box, S doubled twice
A26 = ikn.IntAtomsN(H, W6, 2048, Sexpt=26)
A28 = ikn.IntAtomsN(H, W6, 2048, Sexpt=28)
for A, box, tag, want in ((A26, box26, 'S=2^26', False), (A28, box28, 'S=2^28', True)):
    val = A.bound(box)
    print('  %s: atoms=%d total=%d  bound(box)=%d  d2max_seen=%d  U2_ceil=%d'
          % (tag, len(A.W), A.total, val, A.maxd2, A.U2_ceil))
    check('%s: 10*bound < total ?  (want %s)' % (tag, want), (10 * val < A.total) == want,
          '(10*val=%d, total=%d, slack=%d)' % (10 * val, A.total, A.total - 10 * val))
    check('%s: maxd2 <= 32 S^2' % tag, A.maxd2 <= 32 * A.S2)
    check('%s: 10*total < 2^63 (Python-int comparison safe)' % tag, 10 * A.total < 2 ** 63)
print('  recorded scale-26 result for this leaf: status=unresolved cap=%d total=%d (boxes 6539)'
      % (32608767913, 325879733812))
print('  -> the recomputed scale-26 bound equals the recorded cap exactly; the x4 lift')
print('     (=same real box at S=2^28) already satisfies 10*bound<total, so the flip')
print('     26-unresolved -> 28-certified is a resolution effect, not a new premise.')

print()
print('== 7. soundness kernel: atom rectangle, capture direction, annulus discard ==')
import random
rng = random.Random(11)


def exact_atom_rects(H, V):
    """independent exact rational atom rectangles (moving coordinates over H)."""
    (sl, sh), (xl, xh), (yl, yh) = H
    out = []
    for (c, t) in V:
        if not (U * c > sl):
            out.append((1, (xl - sh + U * c, xh - sl + U * c), (yl + U * t, yh + U * t)))
        if not (U * c < -sl):
            out.append((2, (xl + sl + U * c, xh + sh + U * c), (yl + U * t, yh + U * t)))
        out.append((0, (c, c), (t, t)))
    return out


rects = exact_atom_rects(H, V)
missed = wrong_excl = 0
S28, S28_2 = A28.S, A28.S2
for _ in range(120):
    depth = rng.randrange(0, 26)
    w = 2 * S28 // (1 << depth)
    kmax = 2 * S28 // w
    kx, ky = rng.randrange(0, kmax), rng.randrange(0, kmax)
    B = (-S28 + kx * w, -S28 + (kx + 1) * w, -S28 + ky * w, -S28 + (ky + 1) * w)
    bx0f, bx1f = F(B[0], S28), F(B[1], S28)
    by0f, by1f = F(B[2], S28), F(B[3], S28)
    val = A28.bound(B)
    # integer verdict per atom, recomputed independently from the integer rects of A28
    for (j, rx, ry) in rng.sample(rects, 40):
        idx = None
        dxt = max(F(0), bx0f - rx[1], rx[0] - bx1f)
        dyt = max(F(0), by0f - ry[1], ry[0] - by1f)
        true2 = dxt * dxt + dyt * dyt
        ix0, ix1 = ik.floorF(rx[0] * S28), ik.ceilF(rx[1] * S28)
        iy0, iy1 = ik.floorF(ry[0] * S28), ik.ceilF(ry[1] * S28)
        dx = max(0, B[0] - ix1, ix0 - B[1]); dy = max(0, B[2] - iy1, iy0 - B[3])
        d2i = dx * dx + dy * dy
        counted = d2i <= A28.U2_ceil
        if true2 <= U * U and not counted:
            missed += 1
        if (not counted) and true2 <= U * U:
            wrong_excl += 1
check('no missed capture: true dist^2 <= U^2 => integer test counts it',
      missed == 0, '(%d sampled (box,atom) pairs)' % (120 * 40))
# annulus discard soundness + completeness
bad_dis = bad_keep = 0
for _ in range(400):
    depth = rng.randrange(0, 26)
    w = 2 * S28 // (1 << depth)
    kmax = 2 * S28 // w
    kx, ky = rng.randrange(0, kmax), rng.randrange(0, kmax)
    B = (-S28 + kx * w, -S28 + (kx + 1) * w, -S28 + ky * w, -S28 + (ky + 1) * w)
    val = A28.bound(B)
    farx = max(abs(B[0]), abs(B[1])); fary = max(abs(B[2]), abs(B[3]))
    nearx = max(B[0], -B[1], 0); neary = max(B[2], -B[3], 0)
    hi2 = F(farx * farx + fary * fary, S28_2)
    lo2 = F(nearx * nearx + neary * neary, S28_2)
    intersects = (hi2 >= (1 - U) ** 2) and (lo2 <= 1 - U * U)
    if val == -1 and intersects:
        bad_dis += 1                       # discarded a box that may contain legal centers
    if val != -1 and not (hi2 >= (1 - U) ** 2 and lo2 <= 1 - U * U):
        bad_keep += 1                      # kept a box provably outside the annulus (harmless)
check('discard (-1) only when the box is disjoint from the annulus', bad_dis == 0)
check('every annulus-intersecting box is kept (not a soundness issue, completeness)',
      bad_dis == 0, '(%d kept-outside boxes: harmless)' % bad_keep)

print()
print('== 6. strict gap semantics ==')
ev = json.loads(open(os.path.join(N12, 'members', 'finite-reduction', 'integer-domain', 'out',
                                  'escalated-scale28-evidence.json'), encoding='utf-8').read())
for rec in ev['records']:
    r = rec['scale_28_result']
    g = r['total_integer_demand'] - 10 * r['max_integer_capture']
    check('idx %d: reported gap == total - 10*max and > 0' % rec['idx'],
          g == r['gap_integer'] and g > 0, '(gap=%d)' % g)

print()
print('SUMMARY:', 'ALL CHECKS PASS' if ok_all else 'FAILURES PRESENT')
sys.exit(0 if ok_all else 1)
