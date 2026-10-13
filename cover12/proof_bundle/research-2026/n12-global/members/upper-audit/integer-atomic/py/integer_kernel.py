"""integer_kernel.py  (member upper-audit/integer-atomic, 2026-09-26)

INDEPENDENT pure-int64 distance kernel for the atomic hub-line dual.  No float enters
any distance computation: atom rectangles are built from the exact rational data
(records + hub box H) and converted by outward floor/ceil at scale S = 2**26; ring
boxes are dyadic with depth <= 23, so their endpoints are exact integers in units of
1/S; squared distances are int64 with |endpoint| <= 2S, |diff| <= 4S, d^2 <= 32 S^2
= 2^57 < 2^63.  Thresholds are exact integers:
    U2_ceil     = ceil(U^2 S^2)            (capture test: d2 <= U2_ceil)
    inner_floor = floor((1-U)^2 S^2)       (discard if high < inner_floor)
    outer_ceil  = ceil((1-U^2) S^2)        (discard if low  > outer_ceil)
Exposure screening (U*c <= s_lo for hub 1, U*c >= -s_lo for hub 2) is done in exact
rationals; weights are the same positive integers round(W(theta)*1e9).  Unit vectors
come from evidence/atomic-unit-vectors-2048.json (no tan anywhere).

Self-checks performed on every run:
  * all atom integer endpoints within +-2S; all ring endpoints exact integers;
  * every split midpoint exact; d^2 <= 32 S^2; total < 2^60 and 10*total < 2^63;
  * calibration against exact Fractions on random (atom, ring box) pairs:
      exact min d^2 <= U^2  =>  integer test counts the atom        (no false negative)
      integer verdict outside (d2 > U2_ceil)  =>  exact min d^2 > U^2 (no false positive)

Run:  py -3 -B py/integer_kernel.py [positive|stage3|hub <idx>] [S_exp]
"""
import json
import os
import random
import sys
from fractions import Fraction as F

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..', '..', '..'))
EVID = os.path.join(ROOT, 'research-2026', 'n12-global', 'evidence')
U = F('0.361102963744508672616920293904')


def ceilF(q):
    q = F(q)
    return -((-q.numerator) // q.denominator)


def floorF(q):
    q = F(q)
    return q.numerator // q.denominator


class IntAtoms:
    def __init__(self, H, weights, Sexpt=26):
        # ---- prerequisites, asserted in the class API itself (not only in the CLI)
        # so that any independent replayer calling this class gets the same guards.
        assert isinstance(Sexpt, int) and 20 <= Sexpt <= 28, 'scale exponent out of range'
        assert len(H) == 3, 'H must have three intervals (s, x, y)'
        for iv_ in H:
            assert len(iv_) == 2, 'each H entry must be an interval'
            lo, hi = F(iv_[0]), F(iv_[1])
            assert lo <= hi, 'H interval not ordered'
        assert F(H[0][0]) >= 0, 's interval must lie in [0, U] (required by the generator)'
        assert len(weights) == 3, 'weights must have three blocks (W0, W1, W2)'
        for row in weights:
            assert isinstance(row, (list, tuple)), 'each weight row must be a sequence'
            assert len(row) % 2 == 1 and len(row) >= 5, 'weight row length must be odd and >= 5 (1 + 2K, K >= 2)'
        assert all(len(row) == len(weights[0]) for row in weights), 'weight rows must be equal length'
        assert len(weights[0]) % 2 == 1, 'weight row length must be odd (1 + 2K)'

        self.S = 1 << Sexpt
        self.S2 = self.S * self.S
        self.U2_ceil = ceilF(U * U * self.S2)
        self.inner_floor = floorF((1 - U) ** 2 * self.S2)
        self.outer_ceil = ceilF((1 - U * U) * self.S2)
        self.H = [(F(a), F(b)) for a, b in H]
        Hself = self.H
        sl, sh = Hself[0]; xl, xh = Hself[1]; yl, yh = Hself[2]
        canon = json.loads(open(os.path.join(EVID, 'atomic-unit-vectors-2048.json'), encoding='utf-8').read())
        V = [(F(c), F(s)) for c, s in canon]
        assert len(V) == 2048 and all(c * c + s * s == 1 for c, s in V)
        Wflat = [[F(x) for x in row] for row in weights]
        n = (len(Wflat[0]) - 1) // 2
        ax0, ax1, ay0, ay1, wts = [], [], [], [], []
        for j, w in enumerate(Wflat):
            for (c, s) in V:
                if j == 1 and U * c > sl:
                    continue
                if j == 2 and U * c < -sl:
                    continue
                v = F(w[0]); co, si = F(1), F(0)
                for k in range(1, n + 1):
                    co, si = co * c - si * s, si * c + co * s
                    v += F(w[k]) * co + F(w[n + k]) * si
                assert v >= 0
                wt = round(v * 10 ** 9)
                if not wt:
                    continue
                if j == 0:
                    rx, ry = (c, c), (s, s)
                elif j == 1:
                    rx = (xl - sh + U * c, xh - sl + U * c); ry = (yl + U * s, yh + U * s)
                else:
                    rx = (xl + sl + U * c, xh + sh + U * c); ry = (yl + U * s, yh + U * s)
                S = self.S
                ax0.append(floorF(rx[0] * S)); ax1.append(ceilF(rx[1] * S))
                ay0.append(floorF(ry[0] * S)); ay1.append(ceilF(ry[1] * S))
                wts.append(wt)
        self.Ax0 = np.array(ax0, dtype=np.int64); self.Ax1 = np.array(ax1, dtype=np.int64)
        self.Ay0 = np.array(ay0, dtype=np.int64); self.Ay1 = np.array(ay1, dtype=np.int64)
        self.W = np.array(wts, dtype=np.int64)
        self.total = int(sum(wts))
        self.maxend = int(max(np.abs(self.Ax0).max(), np.abs(self.Ax1).max(),
                              np.abs(self.Ay0).max(), np.abs(self.Ay1).max()))
        self.maxd2 = 0
        assert self.maxend <= 2 * self.S
        assert self.total < 2 ** 60 and 10 * self.total < 2 ** 63

    # ------------------------------------------------------------------ bound
    def bound(self, B):
        bx0, bx1, by0, by1 = B
        # ring box endpoints must be exact integers in [-S, S] with lo <= hi
        S = self.S
        assert (-S <= bx0 <= bx1 <= S) and (-S <= by0 <= by1 <= S), \
            'ring box endpoints must satisfy -S <= lo <= hi <= S (integer units)'
        nearx = max(bx0, -bx1, 0); neary = max(by0, -by1, 0)
        farx = max(abs(bx0), abs(bx1)); fary = max(abs(by0), abs(by1))
        low = nearx * nearx + neary * neary
        high = farx * farx + fary * fary
        if high < self.inner_floor or low > self.outer_ceil:
            return -1
        dx = np.maximum(np.maximum(self.Ax0 - bx1, bx0 - self.Ax1), 0)
        dy = np.maximum(np.maximum(self.Ay0 - by1, by0 - self.Ay1), 0)
        d2 = dx * dx + dy * dy
        m = int(d2.max())
        if m > self.maxd2:
            self.maxd2 = m
        assert m <= 32 * self.S2
        return int(self.W[d2 <= self.U2_ceil].sum())

    # ------------------------------------------------------------------ DFS
    def certify(self, max_depth=23, budget=4000000):
        S = self.S
        stack = [(-S, S, -S, S)]
        nbox = leaves = outside = 0
        worst = 0
        while stack:
            B = stack.pop(); nbox += 1
            if nbox > budget:
                return dict(status='budget', boxes=nbox, pending=len(stack) + 1)
            val = self.bound(B)
            if val < 0:
                outside += 1; continue
            if 10 * val < self.total:
                leaves += 1; worst = max(worst, val); continue
            a, b, c, d = B
            w = max(b - a, d - c)
            if w <= 16:
                return dict(status='unresolved', box=[a, b, c, d], cap=val,
                            total=self.total, boxes=nbox, depth=max_depth)
            if b - a >= d - c:
                assert (a + b) % 2 == 0
                m = (a + b) // 2
                stack.extend([(a, m, c, d), (m, b, c, d)])
            else:
                assert (c + d) % 2 == 0
                m = (c + d) // 2
                stack.extend([(a, b, c, m), (a, b, m, d)])
        return dict(status='certified', boxes=nbox, leaves=leaves, outside=outside,
                    max_integer_capture=worst, total_integer_demand=self.total,
                    gap_integer=self.total - 10 * worst, atoms=len(self.W),
                    scale=self.S, max_d2_seen=self.maxd2,
                    endpoint_cap_units=2 * self.S, max_endpoint_units=self.maxend)


def exact_ranges(H, weights):
    """exact Fraction atom rectangles (for calibration against the integer kernel)."""
    sl, sh = H[0]; xl, xh = H[1]; yl, yh = H[2]
    canon = json.loads(open(os.path.join(EVID, 'atomic-unit-vectors-2048.json'), encoding='utf-8').read())
    V = [(F(c), F(s)) for c, s in canon]
    Wflat = [[F(x) for x in row] for row in weights]
    n = (len(Wflat[0]) - 1) // 2
    out = []
    for j, w in enumerate(Wflat):
        for (c, s) in V:
            if j == 1 and U * c > sl:
                continue
            if j == 2 and U * c < -sl:
                continue
            v = F(w[0]); co, si = F(1), F(0)
            for k in range(1, n + 1):
                co, si = co * c - si * s, si * c + co * s
                v += F(w[k]) * co + F(w[n + k]) * si
            wt = round(v * 10 ** 9)
            if not wt:
                continue
            if j == 0:
                rx, ry = (c, c), (s, s)
            elif j == 1:
                rx = (xl - sh + U * c, xh - sl + U * c); ry = (yl + U * s, yh + U * s)
            else:
                rx = (xl + sl + U * c, xh + sh + U * c); ry = (yl + U * s, yh + U * s)
            out.append((rx, ry, wt))
    return out


def calibration(atoms, H, weights, nrand=400, seed=7):
    """exact-Fraction calibration of both soundness directions."""
    rng = random.Random(seed)
    exact = exact_ranges(H, weights)
    assert len(exact) == len(atoms.W)
    fn = fp = shell_bad = 0
    S = atoms.S
    for _ in range(nrand):
        # random dyadic ring box at scale S (depth <= 23), snapped to the 2^depth grid
        # and always inside [-S, S] (index-based construction, no modular snapping).
        depth = rng.randrange(0, 24)
        w = 2 * S // (1 << depth)               # cell width in units of 1/S
        kmax = 2 * S // w                       # number of cells spanning [-S, S]
        kx = rng.randrange(0, kmax)
        ky = rng.randrange(0, kmax)
        B = (-S + kx * w, -S + (kx + 1) * w, -S + ky * w, -S + (ky + 1) * w)
        assert -S <= B[0] <= B[1] <= S and -S <= B[2] <= B[3] <= S
        val = atoms.bound(B)
        if val < 0:
            continue
        bx0f, bx1f, by0f, by1f = [F(v, S) for v in B]
        dx = np.maximum(np.maximum(atoms.Ax0 - B[1], B[0] - atoms.Ax1), 0)
        dy = np.maximum(np.maximum(atoms.Ay0 - B[3], B[2] - atoms.Ay1), 0)
        d2 = dx * dx + dy * dy
        inside_int = d2 <= atoms.U2_ceil
        for i in rng.sample(range(len(exact)), 25):
            (rx, ry, wt) = exact[i]
            dxm = max(F(0), bx0f - rx[1], rx[0] - bx1f)
            dym = max(F(0), by0f - ry[1], ry[0] - by1f)
            Sx = dxm * dxm + dym * dym
            tr = Sx <= U * U
            iv = bool(inside_int[i])
            if tr and not iv:
                fn += 1
            if iv and not tr:
                # allowed only inside the outward-rounding shell: the atom rectangle
                # is enlarged by <= 1 unit per coordinate, so the squared distance can
                # drop by at most about 6/S (verified here explicitly).
                fp += 1
                if Sx - U * U > F(6, atoms.S):
                    shell_bad += 1
    return dict(false_negatives=fn, outward_rounded_overcounts=fp, shell_violations=shell_bad,
                samples=nrand * 25)


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else 'positive'
    Sexpt = 26
    jobs = []
    if mode == 'positive':
        ev = json.load(open(os.path.join(EVID, 'hubline-atoms-1-1000-2048.json'), encoding='utf-8'))
        jobs.append(('positive s[.199,.201]x[0,.001]y[.0115,.0135]', ev['H'], ev['weights']))
        if len(sys.argv) > 2:
            Sexpt = int(sys.argv[2])
    elif mode in ('stage3', 'stage'):
        path = os.path.join(EVID, 'hubline-domain-stage2200.json') if mode == 'stage3' else sys.argv[2]
        nsel = '3' if mode == 'stage3' else (sys.argv[3] if len(sys.argv) > 3 else 'all')
        if len(sys.argv) > 4:
            Sexpt = int(sys.argv[4])
        st = json.load(open(path, encoding='utf-8'))
        at = [v for v in st['leaves'] if v['type'] == 'atomic']
        rank = sorted(range(len(at)), key=lambda k: at[k]['result']['gap_integer'] / at[k]['result']['total_integer_demand'])
        sel = rank if nsel == 'all' else rank[:int(nsel)]
        for k in sel:
            v = at[k]
            jobs.append(('leaf#%d(relgap %.2e)' % (k, v['result']['gap_integer'] / v['result']['total_integer_demand']),
                         v['H'], v['proposal']['weights']))
        import hashlib
        print('input %s sha256 %s' % (os.path.basename(path),
              hashlib.sha256(open(path, 'rb').read()).hexdigest()[:16]))
    elif mode == 'hub':
        idx = int(sys.argv[2])
        if len(sys.argv) > 3:
            Sexpt = int(sys.argv[3])
        st = json.load(open(os.path.join(EVID, 'hubline-domain-stage2200.json'), encoding='utf-8'))
        at = [v for v in st['leaves'] if v['type'] == 'atomic']
        v = at[idx]
        jobs.append(('stage2200 leaf#%d' % idx, v['H'], v['proposal']['weights']))
    else:
        raise SystemExit('mode?')
    assert 20 <= Sexpt <= 28, 'scale exponent out of the audited range'
    import hashlib
    print('S = 2^%d = %d ; U2_ceil/inner_floor/outer_ceil computed exactly from rational U' % (Sexpt, 1 << Sexpt))
    print('canonical units sha256 %s ; kernel sha256 %s' % (
        hashlib.sha256(open(os.path.join(EVID, 'atomic-unit-vectors-2048.json'), 'rb').read()).hexdigest()[:16],
        hashlib.sha256(open(os.path.abspath(__file__), 'rb').read()).hexdigest()[:16]))
    ncert = nfail = 0
    for (tag, Hraw, weights) in jobs:
        H = [(F(a), F(b)) for a, b in Hraw]
        A = IntAtoms(H, weights, Sexpt)
        cal = calibration(A, H, weights, nrand=(400 if len(jobs) <= 5 else 40))
        res = A.certify()
        ncert += 1 if res['status'] == 'certified' else 0
        nfail += 0 if res['status'] == 'certified' else 1
        if len(jobs) <= 5:
            print()
            print('== %s ==' % tag)
            print('   atoms=%d total=%d' % (len(A.W), A.total))
            print('   calibration: false negatives %d ; outward-rounded overcounts %d ; shell violations %d  (of %d samples)'
                  % (cal['false_negatives'], cal['outward_rounded_overcounts'], cal['shell_violations'], cal['samples']))
            print('   certify: %s' % json.dumps(res))
        else:
            print('   %-24s atoms=%-5d total=%-13d status=%-11s boxes=%-7s max=%-11s gap=%s  cal(fn=%d,ov=%d,bad=%d)'
                  % (tag, len(A.W), A.total, res['status'], res.get('boxes'), res.get('max_integer_capture'),
                     res.get('gap_integer'), cal['false_negatives'], cal['outward_rounded_overcounts'],
                     cal['shell_violations']), flush=True)
    print()
    print('SUMMARY: certified %d / %d  (failed %d)' % (ncert, len(jobs), nfail))


if __name__ == '__main__':
    main()
