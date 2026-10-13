"""fast_audit_reusable.py  (member upper-audit/atomic-audit, 2026-09-26)

Reusable exact-rational acceptance checker for ANY (eps, N) run of the lead's
hubline_atoms_fast / hubline_atoms configuration, so the full-domain sweep can be
spot-checked without re-running the expensive directed kernel.

  usage: py -3 -B py/fast_audit_reusable.py [eps] [N]        (defaults 1/1000 2048)

It reproduces the kernel DFS with the fast bound (recording terminal boxes) and then,
for the top capture leaves and two random leaves, computes exact Fraction quantities:
  * float count >= exact count  and  float count == exact count (report)
  * every atom with verdict "not possible" has exact squared distance > U^2
  * min over atoms of (S_exact - D_float) >= PAD - err   (the firewall margin)
  * 10 * exact_count < total on every sampled leaf
  * terminal areas sum to 4 exactly (domain completeness)
All writes stay in this member directory (the lead's evidence is only read).

Run: py -3 -B py/fast_audit_reusable.py 1-1000 2048
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
rng = random.Random(20260928)

e_sub = 2.0 ** -51
e_sq = 8 * 2.0 ** -51 + 2.0 ** -102 + 2.0 ** -49
err = 2 * (e_sub + e_sq) + 2 * 2.0 ** -48      # incl. the -PAD rounding


def main():
    eps = F((sys.argv[1] if len(sys.argv) > 1 else '1/1000').replace('-', '/'))
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 2048
    s, x, y = F(1, 5), F(0), F(1, 80)
    HB = [(s - eps, s + eps), (x, x + eps), (max(F(0), y - eps), y + eps)]
    src = json.loads((open(os.path.join(EVID, 'hubline-point-0.json'), encoding='utf-8')).read())
    W = src['proposal']['weights']
    print('config: s in [%s,%s], x in [%s,%s], y in [%s,%s], N=%d' % (*HB[0], *HB[1], *HB[2], N))
    atoms = FA.FastAtoms(HB, W, N)
    total = atoms.total
    maxX = max(np.max(np.abs(atoms.X[0])), np.max(np.abs(atoms.X[1])))
    maxY = max(np.max(np.abs(atoms.Y[0])), np.max(np.abs(atoms.Y[1])))
    print('atoms=%d  max|endpoint| = %.6f / %.6f  (assert<=2: %s)  total=%d (<2^60 %s)'
          % (len(atoms.W), maxX, maxY, max(maxX, maxY) <= 2, total, total < 2 ** 60))

    # exact atom ranges
    sl, sh = HB[0]; xl, xh = HB[1]; yl, yh = HB[2]
    exact = []
    for r in atoms.records:
        j, c, ss, wt = int(r[0]), F(r[1]), F(r[2]), int(r[3])
        if j == 0:
            ax, ay = (c, c), (ss, ss)
        elif j == 1:
            ax, ay = (xl - sh + U * c, xh - sl + U * c), (yl + U * ss, yh + U * ss)
        else:
            ax, ay = (xl + sl + U * c, xh + sh + U * c), (yl + U * ss, yh + U * ss)
        exact.append((ax, ay, wt))

    # DFS with the fast bound
    stack = [(-1.0, 1.0, -1.0, 1.0)]
    leaves, outside, unresolved = [], [], 0
    area = F(0)
    while stack:
        B = stack.pop()
        val = atoms.bound(B)
        if val < 0:
            outside.append(B)
            a, b, c, d = B
            area += (F(b) - F(a)) * (F(d) - F(c))
            continue
        if 10 * val < total:
            leaves.append((val, B))
            a, b, c, d = B
            area += (F(b) - F(a)) * (F(d) - F(c))
            continue
        a, b, c, d = B
        if max(b - a, d - c) < 2 ** -22:
            unresolved += 1
            area += (F(b) - F(a)) * (F(d) - F(c))
            continue
        if b - a >= d - c:
            m = (a + b) / 2; stack.extend([(a, m, c, d), (m, b, c, d)])
        else:
            m = (c + d) / 2; stack.extend([(a, b, c, m), (a, b, m, d)])
    print('DFS: leaves=%d outside=%d unresolved=%d   terminal area = %s (must be 4)'
          % (len(leaves), len(outside), unresolved, area))
    if unresolved or area != 4:
        print('FAIL: domain/termination problem')
        return
    leaves.sort(reverse=True)

    fail = 0
    sample = [('top0', leaves[0]), ('top1', leaves[1]), ('top2', leaves[2])]
    sample += [('rand%d' % k, leaves[rng.randrange(len(leaves))]) for k in range(2)]
    for tag, (val, B) in sample:
        a, b, c, d = B
        bx0, bx1, by0, by1 = F(a), F(b), F(c), F(d)
        dx = np.maximum(np.maximum(atoms.X[0] - b, a - atoms.X[1]), 0.)
        dy = np.maximum(np.maximum(atoms.Y[0] - d, c - atoms.Y[1]), 0.)
        D = dx * dx + dy * dy - PAD
        poss = D <= atoms.r2[1]
        cnt = 0; out_bad = 0; mingap = None
        for i, (ax, ay, wt) in enumerate(exact):
            dxm = max(F(0), bx0 - ax[1], ax[0] - bx1)
            dym = max(F(0), by0 - ay[1], ay[0] - by1)
            S = dxm * dxm + dym * dym
            if S <= U * U:
                cnt += wt
            if not poss[i]:
                if not (S > U * U):
                    out_bad += 1
                g = S - F.from_float(float(D[i]))
                mingap = g if mingap is None else min(mingap, g)
        ok = (int(atoms.W[poss].sum()) >= cnt and out_bad == 0 and 10 * cnt < total
              and mingap is not None and mingap >= F(PAD) - F(err))
        fail += 0 if ok else 1
        print('   %-6s bound=%-12d exact=%-12d 10*exact<total=%s outside-bad=%d min(S-D)=%.4e  %s'
              % (tag, val, cnt, 10 * cnt < total, out_bad, float(mingap), 'PASS' if ok else 'FAIL'))
    print('RESULT:', 'PASS (exact controls on sampled leaves)' if fail == 0 else 'FAIL (%d)' % fail)


if __name__ == '__main__':
    main()
