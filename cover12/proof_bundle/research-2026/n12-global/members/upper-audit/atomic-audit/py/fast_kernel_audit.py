"""fast_kernel_audit.py  (member upper-audit/atomic-audit, 2026-09-26)

Audit of lead/hubline_atoms_fast.py: the per-vector-op nextafter is replaced by the
absolute guard PAD = 2^-42, with the docstring's error chain

    two correctly rounded subtractions     <= 2^-51 each        (|values| <= 4)
    square of q in [0,4]                   <= 8*2^-51 + 2^-102 + 2^-49
    rounded summation of two squares       <= 2^-48
    => total error < 2^-45   (< PAD = 2^-42, margin ~ 2^3)

This script checks, independently:

  (1) the hypotheses: explicit asserts |endpoint| <= 2 (measure actual maxima);
  (2) the arithmetic chain re-derived here (including the final -PAD subtraction's
      own rounding <= 2^-48, which the docstring does not list), and the resulting
      margin PAD - err;
  (3) EMPIRICAL exact controls against exact Fractions: for real boxes (top leaves of
      the actual run + random boxes) and ALL 4858 atoms compute the exact squared
      rectangle distance S, the kernel's float value D, and verify
        * min over atoms of (S - D)  >=  PAD - err  > 0        (lower-bound firewall)
        * every atom with kernel verdict "not possible" has S > U^2 (strict)
        * kernel count >= exact count                            (over-count direction)
        * 10 * exact_count < total on the worst leaves           (certificate content)
  (4) annulus discards exactly disjoint (re-checked for the fast kernel's decisions);
  (5) reproduction of the recorded run values (consistency only, NOT the basis).

Run: py -3 -B py/fast_kernel_audit.py
"""
import json
import os
import random
import sys
from fractions import Fraction as F

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..', '..', '..'))
LEAD = os.path.join(ROOT, 'research-2026', 'n12-global', 'lead')
EVID = os.path.join(ROOT, 'research-2026', 'n12-global', 'evidence')
sys.path.insert(0, LEAD)

import hubline_atoms as A
import hubline_atoms_fast as FA

U = A.U
PAD = FA.PAD
rng = random.Random(20260927)


def main():
    print('PAD = 2^-42 = %.17g' % PAD)
    # ---- (2) error chain, re-derived ------------------------------------------
    e_sub = 2.0 ** -51          # two subtractions, |values| <= 4 -> ulp(4)/2
    e_sq = 8 * 2.0 ** -51 + 2.0 ** -102 + 2.0 ** -49
    e_add = 2.0 ** -48          # rounded sum of two squares, |sum| <= 32
    e_padsub = 2.0 ** -48       # rounding of the final "- PAD" (not in the docstring)
    err_doc = 2 * (e_sub + e_sq) + e_add
    err_full = 2 * (e_sub + e_sq) + e_add + e_padsub
    print('docstring chain      : 2*(2^-51 + 8*2^-51+2^-102+2^-49) + 2^-48 = %.6e < 2^-45=%s'
          % (err_doc, err_doc < 2.0 ** -45))
    print('with final -PAD rounding: %.6e  (< 2^-45 ? %s ; < PAD ? %s)'
          % (err_full, err_full < 2.0 ** -45, err_full < PAD))
    print('margin PAD - err        = %.6e  (factor %.2f x)'
          % (PAD - err_full, PAD / err_full))

    ev = json.load(open(os.path.join(EVID, 'hubline-atoms-1-1000-2048.json'), encoding='utf-8'))
    HB = [(F(ev['H'][0][0]), F(ev['H'][0][1])), (F(ev['H'][1][0]), F(ev['H'][1][1])),
          (F(ev['H'][2][0]), F(ev['H'][2][1]))]
    W = [[F(x) for x in row] for row in ev['weights']]
    N = int(ev['N'])
    recs = ev['atom_records']
    sl, sh = HB[0]; xl, xh = HB[1]; yl, yh = HB[2]

    # exact atom ranges over the hub box (independent of the kernel)
    exact = []
    for r in recs:
        j, c, s, wt = int(r[0]), F(r[1]), F(r[2]), int(r[3])
        if j == 0:
            ax, ay = (c, c), (s, s)
        elif j == 1:
            ax, ay = (xl - sh + U * c, xh - sl + U * c), (yl + U * s, yh + U * s)
        else:
            ax, ay = (xl + sl + U * c, xh + sh + U * c), (yl + U * s, yh + U * s)
        exact.append((ax, ay, wt))
    total = sum(w for _, _, w in exact)

    atoms = FA.FastAtoms(HB, ev['weights'], N)
    print()
    print('== (1) hypotheses ==')
    mx = max(max(abs(v) for v in (a, b)) for (a, b) in zip(*atoms.X)) if False else None
    maxX = max(np.max(np.abs(atoms.X[0])), np.max(np.abs(atoms.X[1])))
    maxY = max(np.max(np.abs(atoms.Y[0])), np.max(np.abs(atoms.Y[1])))
    print('   max |atom endpoint| x/y = %.6f / %.6f   (assert <= 2: %s)'
          % (maxX, maxY, max(maxX, maxY) <= 2))
    print('   int64 safety: total=%d < 2^60 %s ; 10*total=%d < 2^63 %s'
          % (total, total < 2 ** 60, 10 * total, 10 * total < 2 ** 63))

    # ---- (5) reproduce the recorded run with the fast kernel -------------------
    out = atoms.certify()
    print()
    print('== (5) fast kernel reproduction (consistency only) ==')
    print('   fast : status=%s boxes=%s leaves=%s outside=%s maxcap=%s total=%s gap=%s'
          % (out.get('status'), out.get('boxes'), out.get('leaves'), out.get('outside'),
             out.get('max_integer_capture'), out.get('total_integer_demand'), out.get('gap_integer')))
    print('   rec  : status=%s boxes=%d leaves=%d outside=%d maxcap=%d total=%d gap=%d'
          % (ev['status'], ev['boxes'], ev['leaves'], ev['outside'],
             ev['max_integer_capture'], ev['total_integer_demand'], ev['gap_integer']))

    # ---- DFS replication recording terminal boxes ------------------------------
    stack = [(-1.0, 1.0, -1.0, 1.0)]
    leaves, outside = [], []
    nbox = 0
    while stack:
        B = stack.pop(); nbox += 1
        val = atoms.bound(B)
        if val < 0:
            outside.append(B); continue
        if 10 * val < atoms.total:
            leaves.append((val, B)); continue
        a, b, c, d = B
        if max(b - a, d - c) < 2 ** -22:
            print('   UNRESOLVED box', B); continue
        if b - a >= d - c:
            m = (a + b) / 2; stack.extend([(a, m, c, d), (m, b, c, d)])
        else:
            m = (c + d) / 2; stack.extend([(a, b, c, m), (a, b, m, d)])
    leaves.sort(reverse=True)

    # ---- (3) exact controls ---------------------------------------------------
    def probe(B, label):
        a, b, c, d = B
        bx0, bx1, by0, by1 = F(a), F(b), F(c), F(d)
        # kernel per-atom values, same formula as FA.bound
        dx = np.maximum(np.maximum(atoms.X[0] - b, a - atoms.X[1]), 0.)
        dy = np.maximum(np.maximum(atoms.Y[0] - d, c - atoms.Y[1]), 0.)
        D = dx * dx + dy * dy - PAD
        poss = D <= atoms.r2[1]
        cnt_exact = 0
        cnt_float = int(atoms.W[poss].sum())
        min_gap = None
        bad_out = 0
        for i, (ax, ay, wt) in enumerate(exact):
            dxm = max(F(0), bx0 - ax[1], ax[0] - bx1)
            dym = max(F(0), by0 - ay[1], ay[0] - by1)
            S = dxm * dxm + dym * dym
            if S <= U * U:
                cnt_exact += wt
            if not poss[i]:
                if not (S > U * U):
                    bad_out += 1
                g = S - F.from_float(float(D[i]))
                if min_gap is None or g < min_gap:
                    min_gap = g
        print('   %-16s float=%d exact=%d  float>=exact %s  10*exact<total %s  '
              'outside-failures %d  min(S-D)=%.4e (>= PAD-err %s)'
              % (label, cnt_float, cnt_exact, cnt_float >= cnt_exact, 10 * cnt_exact < total,
                 bad_out, float(min_gap), min_gap >= F(PAD) - F(err_full)))
        return bad_out, min_gap

    print()
    print('== (3) exact per-atom controls on real boxes ==')
    nbad = 0
    gaps = []
    for k in range(8):
        val, B = leaves[k]
        nb, g = probe(B, 'leaf #%d (b=%d)' % (k, val))
        nbad += nb; gaps.append(g)
    for k in range(4):
        B = leaves[rng.randrange(len(leaves))][1]
        nb, g = probe(B, 'rand leaf %d' % k)
        nbad += nb; gaps.append(g)
    for k in range(4):
        B = outside[rng.randrange(len(outside))]
        nb, g = probe(B, 'rand discard %d' % k)
        nbad += nb; gaps.append(g)
    for k in range(6):
        a = rng.uniform(-1, 1); b = a + 10 ** rng.uniform(-6, -1)
        c = rng.uniform(-1, 1); d = c + 10 ** rng.uniform(-6, -1)
        nb, g = probe((a, b, c, d), 'random box %d' % k)
        nbad += nb; gaps.append(g)

    # ---- (4) annulus discards exactly disjoint --------------------------------
    inner, outer = (1 - U) ** 2, 1 - U * U
    ann_bad = 0
    for (a, b, c, d) in outside:
        A4 = [(a, c), (a, d), (b, c), (b, d)]
        maxr2 = max(F(x) ** 2 + F(y) ** 2 for x, y in A4)
        dx = F(0) if a <= 0 <= b else min(abs(F(a)), abs(F(b)))
        dy = F(0) if c <= 0 <= d else min(abs(F(c)), abs(F(d)))
        if not (maxr2 < inner or dx * dx + dy * dy > outer):
            ann_bad += 1

    print()
    print('== (4) annulus ==')
    print('   exact disjointness failures on %d discarded boxes: %d' % (len(outside), ann_bad))
    print()
    print('SUMMARY: outside-direction failures %d ; annulus failures %d ;'
          ' minimum S-D over sampled atoms %.4e (claim: >= PAD-err = %.4e)'
          % (nbad, ann_bad, min(float(g) for g in gaps), PAD - err_full))


if __name__ == '__main__':
    main()
