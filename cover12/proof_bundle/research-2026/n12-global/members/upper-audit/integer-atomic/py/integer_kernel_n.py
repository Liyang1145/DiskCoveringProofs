"""integer_kernel_n.py  (member upper-audit/integer-atomic, 2026-09-26)

N-generalizable companion of the FROZEN py/integer_kernel.py (that file is imported,
never modified).  Purpose: give the manifest verifier an atom-count-dispatching entry
point (N = 2048 as before, N = 8192 for the two-hub fallback) with the same pure-int64
distance arithmetic.

Independence statement (explicit, per Lead):
  * INDEPENDENT of the float kernels: H and weights are re-read here from the caller's
    JSON/rational source; atom coordinates are rebuilt from the exact rational
    stereographic vectors; floor/ceil at scale S; all distance/annulus/threshold
    arithmetic is integer (same proven design as the frozen module's class docstring).
  * NON-INDEPENDENT (deliberately reused from the frozen module, by Lead's instruction):
    the methods IntAtoms.bound  and  IntAtoms.certify.  This file subclasses the frozen
    class and only replaces __init__ (atom construction + guards).  Any audit of those
    two methods transfers verbatim; this file claims nothing new about them.
  * All constructor guards and the overflow/range checks of the frozen class are
    re-asserted here on the generalized path.

Evidence policy: evidence/ is not writable from this member scope, so the N=8192 exact
stereographic unit vectors are written to this member directory
(../evidence/canonical-unit-vectors-8192.json) and every vector is verified exactly.

Run:  py -3 -B py/integer_kernel_n.py vectors 8192
      py -3 -B py/integer_kernel_n.py check-n8192
"""
import json
import math
import os
import sys
from fractions import Fraction as F

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import integer_kernel as ik          # frozen module: reuse bound/certify, copy arithmetic

U = ik.U
ceilF = ik.ceilF
floorF = ik.floorF

MY_EVID = os.path.join(HERE, '..', 'evidence')
N12 = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))          # .../research-2026/n12-global
EVID = os.path.join(N12, 'evidence')
TWO_HUB = os.path.join(N12, 'members', 'two-hub', 'proposal-repair')
DEFAULT_VECTOR_DIR = MY_EVID
N8192_PATH = os.path.join(MY_EVID, 'canonical-unit-vectors-8192.json')


# ----------------------------------------------------------------- exact vectors
def stereographic_units(N, decimals=8):
    """N exact rational points of S^1: t = round(tan(pi j/N) * 10^dec) / 10^dec,
    (c, s) = ((1-t^2)/(1+t^2), 2t/(1+t^2)) -- the same proposal family the float
    kernels used.  NOTE: tan is only a *proposal*; correctness of each point on S^1
    is verified exactly, no property of tan is relied upon."""
    scale = 10 ** decimals
    out = []
    for j in range(N):
        if 2 * j == N:
            out.append((F(-1), F(0)))
            continue
        t = F(round(math.tan(math.pi * j / N) * scale), scale)
        out.append(((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t)))
    return out


def save_vectors(N, path=None, decimals=8):
    path = path or (N8192_PATH if N == 8192 else os.path.join(MY_EVID, 'canonical-unit-vectors-%d.json' % N))
    V = stereographic_units(N, decimals)
    assert len(V) == N
    assert all(c * c + s * s == 1 for c, s in V), 'generated point off S^1'
    payload = {'N': N, 'decimals': decimals,
               'note': 'exact rational stereographic points; each verified c^2+s^2==1',
               'vectors': [[str(c), str(s)] for c, s in V]}
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(payload, f, indent=1)
    return path, V


def load_vectors(src):
    """src = N (int) -> default member file; path str -> json/list."""
    if isinstance(src, int):
        p = N8192_PATH if src == 8192 else os.path.join(MY_EVID, 'canonical-unit-vectors-%d.json' % src)
        if not os.path.exists(p):
            p, _ = save_vectors(src)
        src = p
    if isinstance(src, str):
        d = json.loads(open(src, encoding='utf-8').read())
        raw = d['vectors'] if isinstance(d, dict) and 'vectors' in d else d
        V = [(F(a), F(b)) for a, b in raw]
    else:
        V = [(F(a), F(b)) for a, b in src]
    assert all(c * c + s * s == 1 for c, s in V), 'vector not exactly on S^1'
    assert len(V) >= 5, 'need at least a handful of vectors'
    return V


# ----------------------------------------------------------------- N-generalized atoms
class IntAtomsN(ik.IntAtoms):
    """Same pure-int64 kernel for an arbitrary atom count N.

    bound() and certify() are INHERITED from the frozen IntAtoms (non-independent by
    design); only the construction (which atoms, which N) differs."""

    def __init__(self, H, weights, vectors, Sexpt=26, screen=True):
        # ---- prerequisites, same guards as the frozen class (constructor-level)
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
            assert len(row) % 2 == 1 and len(row) >= 5, 'weight row length must be odd and >= 5 (1 + 2K)'
        assert all(len(row) == len(weights[0]) for row in weights), 'weight rows must be equal length'

        if isinstance(vectors, (int, str)):
            V = load_vectors(vectors)
        else:
            V = [(F(a), F(b)) for a, b in vectors]
        assert all(c * c + s * s == 1 for c, s in V), 'vector not exactly on S^1'

        self.S = 1 << Sexpt
        self.S2 = self.S * self.S
        self.U2_ceil = ceilF(U * U * self.S2)
        self.inner_floor = floorF((1 - U) ** 2 * self.S2)
        self.outer_ceil = ceilF((1 - U * U) * self.S2)
        self.H = [(F(a), F(b)) for a, b in H]
        sl, sh = self.H[0]; xl, xh = self.H[1]; yl, yh = self.H[2]
        Wflat = [[F(x) for x in row] for row in weights]
        n = (len(Wflat[0]) - 1) // 2
        S = self.S
        ax0, ax1, ay0, ay1, wts = [], [], [], [], []
        for j, w in enumerate(Wflat):
            for (c, s) in V:
                if screen:
                    if j == 1 and U * c > sl:
                        continue
                    if j == 2 and U * c < -sl:
                        continue
                v = F(w[0]); co, si = F(1), F(0)
                for k in range(1, n + 1):
                    co, si = co * c - si * s, si * c + co * s
                    v += F(w[k]) * co + F(w[n + k]) * si
                assert v >= 0, 'negative density value'
                wt = round(v * 10 ** 9)
                if not wt:
                    continue
                if j == 0:
                    rx, ry = (c, c), (s, s)
                elif j == 1:
                    rx = (xl - sh + U * c, xh - sl + U * c); ry = (yl + U * s, yh + U * s)
                else:
                    rx = (xl + sl + U * c, xh + sh + U * c); ry = (yl + U * s, yh + U * s)
                ax0.append(floorF(rx[0] * S)); ax1.append(ceilF(rx[1] * S))
                ay0.append(floorF(ry[0] * S)); ay1.append(ceilF(ry[1] * S))
                wts.append(wt)
        self.N = len(V)
        self.Ax0 = np.array(ax0, dtype=np.int64); self.Ax1 = np.array(ax1, dtype=np.int64)
        self.Ay0 = np.array(ay0, dtype=np.int64); self.Ay1 = np.array(ay1, dtype=np.int64)
        self.W = np.array(wts, dtype=np.int64)
        self.total = int(sum(wts))
        self.maxend = int(max(np.abs(self.Ax0).max(), np.abs(self.Ax1).max(),
                              np.abs(self.Ay0).max(), np.abs(self.Ay1).max()))
        self.maxd2 = 0
        # ---- same overflow / range checks as the frozen class
        assert self.maxend <= 2 * self.S, 'atom endpoint beyond 2S'
        assert self.total < 2 ** 60 and 10 * self.total < 2 ** 63, 'integer overflow guard'


# ----------------------------------------------------------------- CLI
def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else 'vectors'
    if mode == 'vectors':
        N = int(sys.argv[2]) if len(sys.argv) > 2 else 8192
        p, V = save_vectors(N)
        print('saved %d exact stereographic vectors to %s' % (len(V), os.path.relpath(p, HERE)))
        print('  verified c^2+s^2==1 for all %d ; sample c=%s s=%s' % (len(V), V[3][0], V[3][1]))
    elif mode == 'check-n8192':
        src = os.path.join(TWO_HUB, 'N_scan.json')
        d = json.loads(open(src, encoding='utf-8').read())
        H, W = d['H'], d['weights_o6']
        row = [r for r in d['N_scan'] if r['N'] == 8192][0]
        print('source: %s (two-hub saved H / weights_o6 / N=8192 FastAtoms certificate)' % os.path.relpath(src, HERE))
        print('  saved row: %s' % json.dumps(row))
        A = IntAtomsN(H, W, 8192, Sexpt=26)
        print('  integer kernel: N=%d atoms=%d total=%d max_endpoint=%d (cap 2S=%d)'
              % (A.N, len(A.W), A.total, A.maxend, 2 * A.S))
        res = A.certify()
        print('  certify (pure int): %s' % json.dumps(res))
        fbox = row.get('box')
        if fbox:
            B = tuple(int(round(v * A.S)) for v in (fbox[0], fbox[1], fbox[2], fbox[3]))
            print('  saved FastAtoms unresolved box, scaled to integer units: %s' % (B,))
            print('  int bound on that box = %d   (saved float cap = %d ; int >= float ? %s)'
                  % (A.bound(B), row.get('cap', -1), A.bound(B) >= row.get('cap', -1)))
        print('  status: %s' % ('certified (int64 kernel, N=8192)' if res['status'] == 'certified' else res['status']))
    elif mode == 'selftest':
        H = [('199/1000', '201/1000'), ('0', '1/1000'), ('23/2000', '27/2000')]
        W = json.loads(open(os.path.join(EVID, 'hubline-atoms-1-1000-2048.json'), encoding='utf-8').read())['weights']
        V2048 = load_vectors(2048)
        fired, missed = [], []
        def must_fire(fn, label):
            try:
                fn()
            except AssertionError as e:
                fired.append(label); print('  fires ok   : %-32s -> %s' % (label, str(e)[:52])); return
            except Exception as e:
                fired.append(label); print('  rejects ok : %-32s -> %s: %s' % (label, type(e).__name__, str(e)[:36])); return
            missed.append(label); print('  NOT FIRING : %-32s' % label)
        print('== IntAtomsN guards (must fire) ==')
        must_fire(lambda: IntAtomsN(H, W, V2048, 19), 'Sexpt=19')
        must_fire(lambda: IntAtomsN(H[:2], W, V2048), 'len(H)=2')
        must_fire(lambda: IntAtomsN([('201/1000', '199/1000')] + H[1:], W, V2048), 'H unordered')
        must_fire(lambda: IntAtomsN([('-1/1000', '1/1000')] + H[1:], W, V2048), 's_lo<0')
        must_fire(lambda: IntAtomsN(H, [W[0], W[1]], V2048), 'len(weights)=2')
        must_fire(lambda: IntAtomsN(H, [W[0][:8], W[1], W[2]], V2048), 'even row length')
        must_fire(lambda: IntAtomsN(H, W, [(F(1), F(1))] * 8), 'vector off S^1')
        must_fire(lambda: IntAtomsN(H, W, 8192, 29), 'Sexpt=29')
        A_big = IntAtomsN(H, W, V2048)
        must_fire(lambda: A_big.bound((0, A_big.S + 1, 0, 1)), 'inherited bound guard: hi>S')
        must_fire(lambda: A_big.bound((0, -1, 0, 1)), 'inherited bound guard: lo>hi')

        # -- dispatch consistency: my N=2048 vectors vs the frozen evidence canonical file
        print()
        print('== N=2048 dispatch consistency ==')
        evcanon = json.loads(open(os.path.join(EVID, 'atomic-unit-vectors-2048.json'), encoding='utf-8').read())
        Vev = [(F(a), F(b)) for a, b in evcanon]
        print('  generated N=2048 == evidence canonical (elementwise): %s' % (Vev == V2048))
        A = IntAtomsN(H, W, V2048)
        res = A.certify()
        print('  positive box via IntAtomsN(N=2048): status=%s boxes=%s max=%s gap=%s'
              % (res['status'], res['boxes'], res['max_integer_capture'], res['gap_integer']))
        print('  matches frozen-module numbers (11875 / 32575800681 / 1271822): %s'
              % (res['status'] == 'certified' and res['boxes'] == 11875
                 and res['max_integer_capture'] == 32575800681 and res['gap_integer'] == 1271822))
        print()
        print('SUMMARY: guards fired %d, missed %d; dispatch consistency %s'
              % (len(fired), len(missed), 'PASS' if not missed and res['boxes'] == 11875 else 'FAIL'))
    else:
        raise SystemExit('mode?')


if __name__ == '__main__':
    main()
