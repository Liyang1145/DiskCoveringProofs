"""domain_leaf_audit.py  (member upper-audit/atomic-audit, 2026-09-26)

Two independent checks on the frozen hub-domain wrapper stage
evidence/hubline-domain-stage2200.json (1021 atomic + 76 infeasible leaves + 7 pending):

PART 1 - leaf partition in a DIFFERENT representation (no recursion reliance):
  * rational volume bookkeeping:  sum of terminal 3-D rational volumes == root volume;
  * flat pairwise interior-disjointness of all 1097 terminal boxes (O(n^2), exact);
  * every terminal box inside the root domain;
  * an independent recursive descent (max-width split, ties -> lowest index) that must
    reach exactly the recorded terminal set, each box once.

PART 2 - all-atom Fraction controls on the most delicate hub boxes:
  * rank the 1021 atomic leaves by relative gap = gap_integer / total_integer_demand;
  * for the 3 smallest, rebuild the leaf's atom set from the canonical unit-vector file
    (evidence/atomic-unit-vectors-2048.json, checked against the platform tan generator),
    replay the inner ring DFS with the kernel's own bound, take the TOP ring leaf
    (largest capture bound) and verify with exact Fractions over ALL atoms:
        float count >= exact count ; every "not possible" atom has exact S > U^2 ;
        min over atoms of (S_exact - D_float) >= PAD - err ; 10*exact < total.
Only reads the lead's evidence; writes stay in this member directory.

Run: py -3 -B py/domain_leaf_audit.py
"""
import json
import os
import sys
from fractions import Fraction as F

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..', '..', '..'))
LEAD = os.path.join(ROOT, 'research-2026', 'n12-global', 'lead')
EVID = os.path.join(ROOT, 'research-2026', 'n12-global', 'evidence')
sys.path.insert(0, LEAD)

import hubline_atoms as A
import hubline_atoms_fast as AF

U = A.U
PAD = AF.PAD
e_sub = 2.0 ** -51
e_sq = 8 * 2.0 ** -51 + 2.0 ** -102 + 2.0 ** -49
ERR = 2 * (e_sub + e_sq) + 2 * 2.0 ** -48


def dec(B):
    return tuple((F(r[0]), F(r[1])) for r in B)


def vol(B):
    v = F(1)
    for (l, h) in B:
        v *= (h - l)
    return v


def inside(B, R):
    return all(R[i][0] <= B[i][0] and B[i][1] <= R[i][1] for i in range(3))


def main():
    st = json.load(open(os.path.join(EVID, 'hubline-domain-stage2200.json'), encoding='utf-8'))
    leaves = st['leaves']
    atoms = [v for v in leaves if v['type'] == 'atomic']
    infeas = [v for v in leaves if v['type'] == 'infeasible']
    terminals = [dec(v['H']) for v in leaves] + [dec(b) for b in st['pending']]
    root = dec(st['domain'])
    print('stage: status=%s processed=%s certified=%d infeasible=%d pending=%d'
          % (st['status'], st['counts']['processed'], len(atoms), len(infeas), len(st['pending'])))
    print('root domain: s in [%s, %s], x in [%s, %s], y in [%s, %s]'
          % (*root[0], *root[1], *root[2]))

    # ---------------- PART 1 ----------------
    print()
    print('== PART 1: partition, flat rational-volume representation ==')
    vr = vol(root)
    vt = sum(vol(B) for B in terminals)
    print('   root 3-D volume        = %s' % vr)
    print('   sum terminal volumes   = %s' % vt)
    print('   equal exactly          = %s' % (vr == vt))
    bad_in = [k for k, B in enumerate(terminals) if not inside(B, root)]
    print('   terminals inside root  = %d failures / %d' % (len(bad_in), len(terminals)))
    # flat pairwise interior-disjointness
    n = len(terminals)
    ov = []
    for i in range(n):
        Bi = terminals[i]
        for j in range(i + 1, n):
            Bj = terminals[j]
            if all(max(Bi[k][0], Bj[k][0]) < min(Bi[k][1], Bj[k][1]) for k in range(3)):
                ov.append((i, j))
                if len(ov) > 5:
                    break
        if len(ov) > 5:
            break
    print('   pairwise interior overlaps (flat, exact) = %d' % len(ov))
    # independent recursive descent with the wrapper's rule
    tset = {}
    for k, B in enumerate(terminals):
        if B in tset:
            print('   DUPLICATE terminal box at indices %d and %d' % (tset[B], k))
        tset[B] = k
    reached = {}
    stack = [root]
    splits = 0
    while stack:
        B = stack.pop()
        if B in tset:
            reached[B] = reached.get(B, 0) + 1
            continue
        w = [h - l for (l, h) in B]
        j = max(range(3), key=lambda k: w[k])
        l, h = B[j]
        if h - l <= F(1, 10 ** 8):
            print('   PARTITION GAP: terminal not reached, width %s' % (h - l))
            break
        m = (l + h) / 2
        for (a, b) in ((l, m), (m, h)):
            child = list(B)
            child[j] = (a, b)
            stack.append(tuple(child))
        splits += 1
    print('   recursive descent: terminals reached %d / %d, splits %d, each once = %s'
          % (len(reached), len(tset), splits, set(reached.values()) == {1} and set(reached) == set(tset)))

    # ---------------- PART 2 ----------------
    print()
    print('== PART 2: all-atom Fraction control on the 3 most delicate hub boxes ==')
    canonical = json.loads(open(os.path.join(EVID, 'atomic-unit-vectors-2048.json'), encoding='utf-8').read())
    V = [(F(c), F(s)) for c, s in canonical]
    print('   canonical units: n=%d, all on S1 exactly = %s' % (len(V), all(c * c + s * s == 1 for c, s in V)))
    plat = A.units(2048)
    print('   canonical == platform tan-generator (elementwise) = %s' % (V == plat))
    old_units = A.units
    A.units = lambda n: V if n == 2048 else old_units(n)

    ranked = sorted(((v['result']['gap_integer'] / v['result']['total_integer_demand'], k, v)
                     for k, v in enumerate(atoms)), key=lambda t: t[0])
    for (rel, k, v) in ranked[:3]:
        B = dec(v['H'])
        sl, sh = B[0]; xl, xh = B[1]; yl, yh = B[2]
        print()
        print('   --- leaf #%d  relgap=%.6e  H: s[%s,%s] x[%s,%s] y[%s,%s]'
              % (k, rel, sl, sh, xl, xh, yl, yh))
        print('       recorded: %s' % {kk: v['result'][kk] for kk in
              ('boxes', 'leaves', 'outside', 'max_integer_capture', 'total_integer_demand', 'gap_integer', 'atoms')})
        C = AF.FastAtoms(B, v['proposal']['weights'], 2048)
        total = C.total
        # inner ring DFS with the kernel's own bound, recording leaves
        stack = [(-1.0, 1.0, -1.0, 1.0)]
        rl, out, unres = [], 0, 0
        nbox = 0
        while stack:
            Q = stack.pop(); nbox += 1
            val = C.bound(Q)
            if val < 0:
                out += 1; continue
            if 10 * val < total:
                rl.append((val, Q)); continue
            a, b, c, d = Q
            if max(b - a, d - c) < 2 ** -22:
                unres += 1; continue
            if b - a >= d - c:
                m = (a + b) / 2; stack.extend([(a, m, c, d), (m, b, c, d)])
            else:
                m = (c + d) / 2; stack.extend([(a, b, c, m), (a, b, m, d)])
        rl.sort(reverse=True)
        got = dict(atom_count=len(C.W), boxes=nbox, leaves=len(rl), outside=out, unresolved=unres,
                   max_int=int(rl[0][0]), total=int(total))
        print('       replay  : atoms=%d boxes=%d leaves=%d outside=%d unresolved=%d max=%d total=%d'
              % (got['atom_count'], got['boxes'], got['leaves'], got['outside'], got['unresolved'],
                 got['max_int'], got['total']))
        agree = (got['boxes'] == v['result']['boxes'] and got['leaves'] == v['result']['leaves']
                 and got['outside'] == v['result']['outside'] and got['max_int'] == v['result']['max_integer_capture']
                 and got['total'] == v['result']['total_integer_demand'] and got['atom_count'] == v['result']['atoms'])
        print('       agrees with recorded result = %s' % agree)

        # exact atom ranges for THIS hub box
        exact = []
        for r in C.records:
            j, c, s, wt = int(r[0]), F(r[1]), F(r[2]), int(r[3])
            if j == 0:
                ax, ay = (c, c), (s, s)
            elif j == 1:
                ax, ay = (xl - sh + U * c, xh - sl + U * c), (yl + U * s, yh + U * s)
            else:
                ax, ay = (xl + sl + U * c, xh + sh + U * c), (yl + U * s, yh + U * s)
            exact.append((ax, ay, wt))
        # top ring leaf exact control
        val, Q = rl[0]
        a, b, c, d = Q
        bx0, bx1, by0, by1 = F(a), F(b), F(c), F(d)
        dx = np.maximum(np.maximum(C.X[0] - b, a - C.X[1]), 0.)
        dy = np.maximum(np.maximum(C.Y[0] - d, c - C.Y[1]), 0.)
        D = dx * dx + dy * dy - PAD
        poss = D <= C.r2[1]
        cnt = 0; out_bad = 0; mingap = None; noutside = 0
        for i, (ax, ay, wt) in enumerate(exact):
            dxm = max(F(0), bx0 - ax[1], ax[0] - bx1)
            dym = max(F(0), by0 - ay[1], ay[0] - by1)
            S = dxm * dxm + dym * dym
            if S <= U * U:
                cnt += wt
            if not poss[i]:
                noutside += 1
                if not (S > U * U):
                    out_bad += 1
                g = S - F.from_float(float(D[i]))
                mingap = g if mingap is None else min(mingap, g)
        print('       TOP RING LEAF box=[%s,%s]x[%s,%s]  float=%d exact=%d  float>=exact=%s'
              % (a, b, c, d, int(C.W[poss].sum()), cnt, int(C.W[poss].sum()) >= cnt))
        print('       10*exact<total = %s   atoms float-says-outside=%d  exact-outside failures=%d'
              % (10 * cnt < total, noutside, out_bad))
        print('       min(S - D) = %.4e   >= PAD-ERR = %.4e ? %s'
              % (float(mingap), PAD - ERR, mingap >= F(PAD) - F(ERR)))


if __name__ == '__main__':
    main()
