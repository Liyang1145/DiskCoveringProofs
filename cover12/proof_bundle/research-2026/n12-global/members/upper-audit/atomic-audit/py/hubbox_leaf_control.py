"""hubbox_leaf_control.py  (member upper-audit/atomic-audit, 2026-09-26)

Reusable control for ANY frozen hub-domain stage file: pick one atomic leaf (by index
or by smallest relative gap), rebuild its atom set from the canonical unit vectors,
replay the inner ring DFS with the kernel's own bound, take the TOP ring leaf and run
the all-atom exact-Fraction control on it.

  usage: py -3 -B py/hubbox_leaf_control.py [stage.json] [index|min]
         default stage = evidence/hubline-domain-stage2200.json ; default selector = min

Checks per hub box:
  * replay agrees with the recorded result (boxes/leaves/outside/max/total/atoms)
  * on the top ring leaf: float count >= exact count, 10*exact < total,
    every "not possible" atom has exact S > U^2, min(S-D) >= PAD - ERR.
Reads only; writes nothing.
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
ERR = 2 * (2.0 ** -51 + 8 * 2.0 ** -51 + 2.0 ** -102 + 2.0 ** -49) + 2 * 2.0 ** -48


def dec(B):
    return tuple((F(r[0]), F(r[1])) for r in B)


def control(v, V, tag):
    B = dec(v['H'])
    sl, sh = B[0]; xl, xh = B[1]; yl, yh = B[2]
    C = AF.FastAtoms(B, v['proposal']['weights'], 2048)
    total = C.total
    stack = [(-1.0, 1.0, -1.0, 1.0)]
    rl, out, unres, nbox = [], 0, 0, 0
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
    rec = v['result']
    agree = (nbox == rec['boxes'] and len(rl) == rec['leaves'] and out == rec['outside']
             and int(rl[0][0]) == rec['max_integer_capture'] and total == rec['total_integer_demand']
             and len(C.W) == rec['atoms'] and unres == 0)
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
    val, Q = rl[0]
    a, b, c, d = Q
    bx0, bx1, by0, by1 = F(a), F(b), F(c), F(d)
    dx = np.maximum(np.maximum(C.X[0] - b, a - C.X[1]), 0.)
    dy = np.maximum(np.maximum(C.Y[0] - d, c - C.Y[1]), 0.)
    D = dx * dx + dy * dy - PAD
    poss = D <= C.r2[1]
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
    ok = (agree and int(C.W[poss].sum()) >= cnt and 10 * cnt < total and out_bad == 0
          and mingap is not None and mingap >= F(PAD) - F(ERR))
    print('%-14s relgap=%.3e  replay_agrees=%s  top-leaf float=%d exact=%d  '
          '10*exact<total=%s  exact_gap=%d  outside_bad=%d  min(S-D)=%.4e  %s'
          % (tag, rec['gap_integer'] / rec['total_integer_demand'], agree,
             int(C.W[poss].sum()), cnt, 10 * cnt < total, total - 10 * cnt, out_bad,
             float(mingap), 'PASS' if ok else 'FAIL'))
    return ok


def main():
    stage = sys.argv[1] if len(sys.argv) > 1 else os.path.join(EVID, 'hubline-domain-stage2200.json')
    sel = sys.argv[2] if len(sys.argv) > 2 else 'min'
    st = json.load(open(stage, encoding='utf-8'))
    at = [v for v in st['leaves'] if v['type'] == 'atomic']
    canon = json.loads(open(os.path.join(EVID, 'atomic-unit-vectors-2048.json'), encoding='utf-8').read())
    V = [(F(c), F(s)) for c, s in canon]
    old = A.units
    A.units = lambda n: V if n == 2048 else old(n)
    print('stage=%s  atomic leaves=%d  selector=%s' % (os.path.basename(stage), len(at), sel))
    if sel == 'min':
        idx = min(range(len(at)), key=lambda k: at[k]['result']['gap_integer'] / at[k]['result']['total_integer_demand'])
    else:
        idx = int(sel)
    ok = control(at[idx], V, 'leaf#%d' % idx)
    print('RESULT:', 'PASS' if ok else 'FAIL')


if __name__ == '__main__':
    main()
