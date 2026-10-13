"""atomic_exact_audit.py  (member upper-audit/atomic-audit, 2026-09-26)

INDEPENDENT exact-rational audit of lead/hubline_atoms.py against the recorded run
evidence/hubline-atoms-1-1000-2048.json (H: s in [199/1000,201/1000], x in [0,1/1000],
y in [23/2000,27/2000]; N=2048; status certified; 4858 atoms / 11875 boxes / 5818 leaves).

The audit is deliberately split into the four obligations named by the Lead:

  (A) numeric interval primitives: bounds/add/sub/square/norm2 are outward
      (nextafter) -- verified against EXACT Fraction values on random and on
      realistic inputs;
  (B) integer capture sums: total / per-box sums computed in exact Python integers,
      checked against int64 limits (the code's own < 2**60 guard);
  (C) dyadic Cartesian box / annulus domain: the DFS terminal boxes are an exact
      partition of [-1,1]^2 (area sum == 4 exactly) and every box discarded by the
      annulus filter is EXACTLY disjoint from {1-U <= |c| <= sqrt(1-U^2)};
  (D) exact rational atom exposure screen + moving-circle witness: every kept atom
      satisfies the exposure inequality U*c <= s_lo (j=1) / U*c >= -s_lo (j=2)
      exactly, its exact position range over the hub box is contained in the float
      interval used by the kernel, and whenever the float verdict says "not
      possible" the exact squared distance is > U^2 (strict).

  (E) targeted exact re-check of the load-bearing leaves (top capture bounds) plus
      randomised controls.

Only imports the lead's module (no file writes outside this member directory; the
lead's evidence file is only read).

Run: py -3 -B py/atomic_exact_audit.py [nrand]
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

import hubline_atoms as A                      # read-only import of the audited kernel

U = A.U                                        # exact Fraction U
NRAND = int(sys.argv[1]) if len(sys.argv) > 1 else 3000


def fr_interval_contains(ivf, q):
    """ivf = (lo,hi) python floats; q exact Fraction."""
    return F.from_float(ivf[0]) <= F(q) <= F.from_float(ivf[1])


# ------------------------------------------------------------------ (A) primitives
def audit_primitives(nrand, rng):
    print('== (A) interval primitives: outward containment vs exact Fractions ==')
    bad = []
    cases = [F(0), F(1), -F(1), U, U * U, (1 - U) ** 2, 1 - U * U, F(1, 3), F(-7, 11),
             F(10) ** 300, F(10) ** -300, F(2) ** -1074, F(1, 2 ** 52) + F(1, 2 ** 105)]
    for _ in range(nrand):
        num = rng.randint(-10 ** 6, 10 ** 6)
        den = rng.choice([1, 10 ** 6, 2 ** 20, 3, 7, 10 ** 12])
        cases.append(F(num, den))
    for q in cases:
        lo, hi = A.bounds(q)
        if not (F.from_float(lo) <= F(q) <= F.from_float(hi)):
            bad.append(('bounds', str(q), lo, hi))
    print('   bounds(q) containment cases        : %d   violations %d' % (len(cases), len(bad)))

    nadd = 0
    for _ in range(nrand):
        a = F(rng.randint(-10 ** 6, 10 ** 6), rng.choice([1, 10 ** 6, 2 ** 20, 3]))
        b = F(rng.randint(-10 ** 6, 10 ** 6), rng.choice([1, 10 ** 6, 2 ** 20, 7]))
        Al, Ah = A.bounds(a)
        Bl, Bh = A.bounds(b)
        lo, hi = A.add((Al, Ah), (Bl, Bh))
        nadd += 1
        if not (F.from_float(lo) <= a + b <= F.from_float(hi)):
            bad.append(('add', str(a), str(b), lo, hi))
        lo, hi = A.sub((Al, Ah), (Bl, Bh))
        if not (F.from_float(lo) <= a - b <= F.from_float(hi)):
            bad.append(('sub', str(a), str(b), lo, hi))
    print('   add/sub exact-sum cases            : %d   violations %d' % (2 * nadd, len(bad)))

    nsq = 0
    for _ in range(nrand):
        a = F(rng.randint(-10 ** 6, 10 ** 6), rng.choice([1, 10 ** 6, 2 ** 20, 3]))
        b = a + F(rng.randint(0, 10 ** 6), rng.choice([1, 10 ** 6, 2 ** 20, 5]))
        # NOTE: the interval handed to square() is the pair of binary64 numbers
        # (that is what the kernel does); the exact min/max must therefore be taken
        # over THOSE endpoints, not over the pre-rounding rationals.
        af, bf = float(a), float(b)
        if af > bf:
            af, bf = bf, af
        aE, bE = F.from_float(af), F.from_float(bf)
        Aiv = (af, bf)
        lo, hi = A.square(Aiv)
        mn = F(0) if aE <= 0 <= bE else min(aE * aE, bE * bE)
        mx = max(aE * aE, bE * bE)
        nsq += 1
        if not (F.from_float(lo) <= mn and mx <= F.from_float(hi)):
            bad.append(('square', str(aE), str(bE), lo, hi))
        # norm2 on a rectangle
        c = F(rng.randint(-10 ** 6, 10 ** 6), rng.choice([1, 10 ** 6, 2 ** 20, 3]))
        d = c + F(rng.randint(0, 10 ** 6), rng.choice([1, 10 ** 6, 2 ** 20, 5]))
        cf, df = float(c), float(d)
        if cf > df:
            cf, df = df, cf
        cE, dE = F.from_float(cf), F.from_float(df)
        lo2, hi2 = A.norm2(Aiv, (cf, df))
        mn2 = mn + (F(0) if cE <= 0 <= dE else min(cE * cE, dE * dE))
        mx2 = mx + max(cE * cE, dE * dE)
        if not (F.from_float(lo2) <= mn2 and mx2 <= F.from_float(hi2)):
            bad.append(('norm2', str(aE), str(bE), str(cE), str(dE), lo2, hi2))
    print('   square/norm2 exact-min/max cases   : %d   violations %d' % (2 * nsq, len(bad)))
    for b in bad[:8]:
        print('     VIOLATION', b)
    return bad


# ------------------------------------------------------------------ (B)+(C)+(D)
def main():
    rng = random.Random(20260926)
    bad = audit_primitives(NRAND, rng)

    ev = json.load(open(os.path.join(EVID, 'hubline-atoms-1-1000-2048.json'), encoding='utf-8'))
    HB = [(F(ev['H'][0][0]), F(ev['H'][0][1])), (F(ev['H'][1][0]), F(ev['H'][1][1])),
          (F(ev['H'][2][0]), F(ev['H'][2][1]))]
    W = [[F(x) for x in row] for row in ev['weights']]
    N = int(ev['N'])
    recs = ev['atom_records']
    sl, sh = HB[0]
    xl, xh = HB[1]
    yl, yh = HB[2]
    print()
    print('== configuration ==')
    print('   H = s in [%s,%s], x in [%s,%s], y in [%s,%s], N=%d' % (sl, sh, xl, xh, yl, yh, N))
    print('   recorded: status=%s boxes=%d leaves=%d outside=%d atoms=%d total=%d maxcap=%d gap=%d'
          % (ev['status'], ev['boxes'], ev['leaves'], ev['outside'], ev['atoms'],
             ev['total_integer_demand'], ev['max_integer_capture'], ev['gap_integer']))

    # (D1) exact atoms: stereographic unit circle + integer weight + exposure screen
    print()
    print('== (D1) exact atom data: unit circle, weight integerisation, exposure screen ==')
    nbad = 0
    full = A.units(N)                          # the kernel's own proposal generator
    for j, (c, s) in enumerate(full):
        assert c * c + s * s == 1, ('not on S1', j, c, s)
    byrec = {(int(r[0]), F(r[1]), F(r[2])): int(r[3]) for r in recs}
    n, per = (len(W[0]) - 1) // 2, 2 * (len(W[0]) - 1) // 2 + 1
    weights_ok = 0
    for j, w in enumerate(W):
        for (c, s) in full:
            if j == 1 and U * c > sl:
                continue
            if j == 2 and U * c < -sl:
                continue
            v = F(w[0]); co, si = F(1), F(0)
            for k in range(1, n + 1):
                co, si = co * c - si * s, si * c + co * s
                v += F(w[k]) * co + F(w[n + k]) * si
            if v < 0:
                nbad += 1
            wt = round(v * 10 ** 9)
            if wt != byrec.get((j, c, s), 0):
                nbad += 1
            if wt:
                weights_ok += 1
    print('   atoms on S1 (c^2+s^2==1 exactly)   : %d/%d blocks ok' % (len(full), 1))
    print('   kept atoms reproduced exactly      : %d (recorded %d)  mismatches %d'
          % (weights_ok, len(recs), nbad))
    screen_bad = 0
    for r in recs:
        j, c, s = int(r[0]), F(r[1]), F(r[2])
        if j == 1 and not (U * c <= sl):
            screen_bad += 1
        if j == 2 and not (U * c >= -sl):
            screen_bad += 1
        if int(r[3]) <= 0:
            screen_bad += 1
    print('   exposure screen failures (kept atom not exposed for all s in box): %d' % screen_bad)
    total_exact = sum(int(r[3]) for r in recs)
    print('   total integer demand (exact python int): %d   recorded %d'
          % (total_exact, ev['total_integer_demand']))
    print('   total < 2**60 ? %s ; 10*total < 2**63 ? %s ; int64 np sum == exact ? %s'
          % (total_exact < 2 ** 60, 10 * total_exact < 2 ** 63,
             int(np.array([int(r[3]) for r in recs], dtype=np.int64).sum()) == total_exact))

    # exact atom position ranges over the hub box
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

    # (D2) the kernel's float atom intervals must contain the exact ranges
    X, Y, Ww, _ = A.build_atoms(HB, ev['weights'], N)
    contain_bad = 0
    for i, (ax, ay, wt) in enumerate(exact):
        if int(Ww[i]) != wt:
            contain_bad += 1
        if not (F.from_float(X[0][i]) <= ax[0] and ax[1] <= F.from_float(X[1][i])
                and F.from_float(Y[0][i]) <= ay[0] and ay[1] <= F.from_float(Y[1][i])):
            contain_bad += 1
    print('   float atom intervals contain the exact hub-box ranges: failures %d / %d'
          % (contain_bad, len(exact)))

    # (C)+(E) replicate the DFS with the kernel's own bound, record terminal boxes
    print()
    print('== (C/E) DFS replication with the kernel bound (records terminal boxes) ==')
    atoms = A.Atoms(HB, ev['weights'], N)
    stack = [(-1.0, 1.0, -1.0, 1.0)]
    leaves, outside, unresolved = [], [], []
    nbox = 0
    while stack:
        B = stack.pop()
        nbox += 1
        val = atoms.bound(B)
        if val < 0:
            outside.append(B); continue
        if 10 * val < atoms.total:
            leaves.append((val, B)); continue
        a, b, c, d = B
        if max(b - a, d - c) < 2 ** -22:
            unresolved.append((val, B)); continue
        if b - a >= d - c:
            m = (a + b) / 2; stack.extend([(a, m, c, d), (m, b, c, d)])
        else:
            m = (c + d) / 2; stack.extend([(a, b, c, m), (a, b, m, d)])
    print('   DFS boxes=%d leaves=%d outside=%d unresolved=%d (recorded %d/%d/%d)'
          % (nbox, len(leaves), len(outside), len(unresolved), ev['boxes'], ev['leaves'],
             ev['outside']))
    area = F(0)
    for (val, B) in leaves + unresolved:
        area += F(b - a) * F(d - c) if False else 0
    for B in [B for (_, B) in leaves] + [B for (_, B) in unresolved] + outside:
        a, b, c, d = B
        area += (F(b) - F(a)) * (F(d) - F(c))
    print('   SUM OF TERMINAL AREAS (exact Fraction) = %s   (root area = 4)' % area)

    # exact annulus test on every discarded box
    inner, outer = (1 - U) ** 2, 1 - U * U
    ann_bad = 0
    for (a, b, c, d) in outside:
        A4 = [(a, c), (a, d), (b, c), (b, d)]
        maxr2 = max(F(x) ** 2 + F(y) ** 2 for x, y in A4)
        dx = F(0) if a <= 0 <= b else min(abs(F(a)), abs(F(b)))
        dy = F(0) if c <= 0 <= d else min(abs(F(c)), abs(F(d)))
        minr2 = dx * dx + dy * dy
        if not (maxr2 < inner or minr2 > outer):
            ann_bad += 1
    print('   annulus discards exactly disjoint   : failures %d / %d' % (ann_bad, len(outside)))

    # (E) exact capture counts for the top leaves + per-atom outside direction
    leaves.sort(reverse=True)
    top = leaves[:20]
    print()
    print('== (E) exact re-check of the load-bearing leaves (top 20 by float bound) ==')
    total = total_exact
    worst_viol = 0
    for (val, B) in top[:5]:
        a, b, c, d = B
        bx0, bx1, by0, by1 = F(a), F(b), F(c), F(d)
        mask = None
        cnt = 0
        for (ax, ay, wt) in exact:
            dxm = max(F(0), bx0 - ax[1], ax[0] - bx1)
            dym = max(F(0), by0 - ay[1], ay[0] - by1)
            if dxm * dxm + dym * dym <= U * U:
                cnt += wt
        if 10 * cnt >= total:
            worst_viol += 1
        print('   leaf bound=%d exact=%d  10*exact<total ? %s   box=[%s,%s]x[%s,%s]'
              % (val, cnt, 10 * cnt < total, a, b, c, d))
    print('   top-5 leaves violating 10*exact<total: %d' % worst_viol)

    # per-atom "outside" calibration on the worst leaf and a random sample of boxes
    def per_atom_calibration(B, label):
        a, b, c, d = B
        cx = (a, b); cy = (c, d)
        Xf = (atoms.X[0], atoms.X[1]); Yf = (atoms.Y[0], atoms.Y[1])
        dx = A.sub(cx, Xf); dy = A.sub(cy, Yf)
        d2 = A.norm2(dx, dy)
        r2hi = atoms.r2[1]
        poss = d2[0] <= r2hi
        viol = 0; nout = 0
        bx0, bx1, by0, by1 = F(a), F(b), F(c), F(d)
        for i, (ax, ay, wt) in enumerate(exact):
            if poss[i]:
                continue
            nout += 1
            dxm = max(F(0), bx0 - ax[1], ax[0] - bx1)
            dym = max(F(0), by0 - ay[1], ay[0] - by1)
            if not (dxm * dxm + dym * dym > U * U):
                viol += 1
        print('   %-18s atoms float-says-outside=%d  exact-distance>U^2 failures=%d'
              % (label, nout, viol))
        return viol

    v = per_atom_calibration(top[0][1], 'worst leaf')
    for k in range(5):
        B = leaves[rng.randrange(len(leaves))][1]
        v += per_atom_calibration(B, 'random leaf %d' % k)
    for k in range(5):
        B = outside[rng.randrange(len(outside))]
        v += per_atom_calibration(B, 'random discard %d' % k)
    # random arbitrary boxes
    for k in range(5):
        a = rng.uniform(-1, 1); b = a + rng.uniform(1e-4, 0.5)
        c = rng.uniform(-1, 1); d = c + rng.uniform(1e-4, 0.5)
        v += per_atom_calibration((a, b, c, d), 'random box %d' % k)
    print('   TOTAL outside-direction failures (float outside but exact <= U^2): %d' % v)
    print()
    print('SUMMARY: primitive violations %d ; atom/weight mismatches %d ; screen failures %d ;'
          % (len(bad), nbad, screen_bad))
    print('         float-interval containment failures %d ; annulus failures %d ;'
          % (contain_bad, ann_bad))
    print('         outside-direction failures %d ; top-leaf 10*exact<total violations %d'
          % (v, worst_viol))


if __name__ == '__main__':
    main()
