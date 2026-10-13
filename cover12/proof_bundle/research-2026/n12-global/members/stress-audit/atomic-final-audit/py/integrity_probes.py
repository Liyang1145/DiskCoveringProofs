"""atomic-final-audit: integrity probes (negative controls + recorded-number cross-check).

  P1  budget path returns 'budget', never 'certified'
  P2  all-zero weights (total=0) returns 'unresolved', never 'certified'
  P3  STRICTNESS of the leaf test 10*val < total : construct total=1 with a box whose
      capture is exactly 1 -> must NOT be accepted (equality insufficient)
  P4  reproduce the *recorded* scale-26 capture for leaf 4398's unresolved box with my
      own integer arithmetic (independent recomputation of a stored number)
"""
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
N12 = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
sys.path.insert(0, os.path.join(N12, 'members', 'upper-audit', 'integer-atomic', 'py'))
import integer_kernel as IK

U = IK.U
SNAP = os.path.join(N12, 'evidence', 'hubline-domain-stage11825.json')
EVID = os.path.join(N12, 'evidence', 'atomic-unit-vectors-2048.json')


def atom_ints(H, weights, Sexpt):
    S = 1 << Sexpt
    V = [(F(c), F(s)) for c, s in json.loads(open(EVID, encoding='utf-8').read())]
    W = [[F(x) for x in row] for row in weights]
    n = (len(W[0]) - 1) // 2
    sl, sh = H[0]; xl, xh = H[1]; yl, yh = H[2]
    A = []
    for j, w in enumerate(W):
        for (c, sv) in V:
            if j == 1 and U * c > sl:
                continue
            if j == 2 and U * c < -sl:
                continue
            v = F(w[0]); co, si = F(1), F(0)
            for k in range(1, n + 1):
                co, si = co * c - si * sv, si * c + co * sv
                v += F(w[k]) * co + F(w[n + k]) * si
            wt = round(v * 10 ** 9)
            if not wt:
                continue
            if j == 0:
                rx = (c, c); ry = (sv, sv)
            elif j == 1:
                rx = (xl - sh + U * c, xh - sl + U * c); ry = (yl + U * sv, yh + U * sv)
            else:
                rx = (xl + sl + U * c, xh + sh + U * c); ry = (yl + U * sv, yh + U * sv)
            ax0 = (rx[0] * S).__floor__(); ax1 = -((-(rx[1] * S)).__floor__())
            ay0 = (ry[0] * S).__floor__(); ay1 = -((-(ry[1] * S)).__floor__())
            A.append((ax0, ax1, ay0, ay1, wt))
    return A, S


def capture(A, B, S, Sexpt):
    U2c = -((-(U * U * (1 << Sexpt) ** 2)).__floor__())
    tot = 0
    for (ax0, ax1, ay0, ay1, wt) in A:
        dx = max(0, ax0 - B[1], B[0] - ax1); dy = max(0, ay0 - B[3], B[2] - ay1)
        if dx * dx + dy * dy <= U2c:
            tot += wt
    return tot


def main():
    st = json.loads(open(SNAP, encoding='utf-8').read())
    atomic = [L for L in st['leaves'] if L.get('type') == 'atomic']
    leaf = atomic[4398]
    H = [(F(a), F(b)) for a, b in leaf['H']]
    W = leaf['proposal']['weights']
    out = {}

    print('P1 budget path:')
    A = IK.IntAtoms(H, W, 28)
    r = A.certify(budget=10)
    print('   budget=10 ->', json.dumps(r))
    out['P1'] = r

    print('P2 zero demand:')
    W0 = [['0'] * len(W[0]) for _ in range(3)]
    try:
        A0 = IK.IntAtoms(H, W0, 28)
        r0 = A0.certify(budget=200000)
        print('   all-zero weights -> status=%s (must not be certified)' % r0['status'])
        out['P2'] = r0
    except Exception as exc:
        print('   all-zero weights -> constructor raised %s: %s  (loud failure, no certificate)'
              % (type(exc).__name__, str(exc)[:80]))
        out['P2'] = {'exception': type(exc).__name__, 'note': 'empty atom list; raises instead of certifying'}

    print('P3 strictness 10*val < total (equality must fail):')
    W1 = [['0'] * len(W[0]) for _ in range(3)]
    W1[0][0] = '1'                     # one boundary atom of weight 1 (density 1 at w0)
    A1 = IK.IntAtoms(H, W1, 26)
    r1 = A1.certify(budget=200000)
    print('   total=%d ; certify -> status=%s boxes=%s (must be unresolved/budget, not certified)'
          % (A1.total, r1['status'], r1.get('boxes')))
    print('   bound on full square = %d ; 10*val >= total : %s'
          % (A1.bound((-A1.S, A1.S, -A1.S, A1.S)), 10 * A1.bound((-A1.S, A1.S, -A1.S, A1.S)) >= A1.total))
    out['P3'] = {'status': r1['status'], 'total': A1.total,
                 'full_square_capture': A1.bound((-A1.S, A1.S, -A1.S, A1.S))}

    print('P4 reproduce recorded scale-26 capture for the recorded unresolved box:')
    B26 = (4512816, 4512832, -43155728, -43155712)
    A26, S26 = atom_ints(H, W, 26)
    cap = capture(A26, B26, S26, 26)
    res26 = leaf['result']
    print('   my capture at 2^26 = %d ; kernel bound() = %d' % (cap, IK.IntAtoms(H, W, 26).bound(B26)))
    print('   (recorded scale-26 attempt: %s)' % json.dumps(
        json.loads(open(os.path.join(N12, 'members/finite-reduction/integer-domain/out/escalated-scale28-evidence.json'),
                        encoding='utf-8').read())['records'][0]['scale_26_result']))
    out['P4'] = {'my_capture_2^26': cap, 'kernel_bound': IK.IntAtoms(H, W, 26).bound(B26)}

    def default(o):
        return str(o)
    dest = os.path.join(HERE, '..', 'evidence', 'integrity-probes.json')
    with open(dest, 'w', encoding='utf-8') as f:
        json.dump(out, f, indent=1, default=default)
    print('wrote', os.path.relpath(dest, N12))


if __name__ == '__main__':
    main()
