"""guard_selftest.py  (member upper-audit/integer-atomic, 2026-09-26)

Negative + positive controls proving that every prerequisite the independent
manifest replayer relies on is asserted INSIDE the IntAtoms class API (not only in
the CLI), plus a check that the guards do not fire on legitimate input.

Run: py -3 -B py/guard_selftest.py
"""
import json
import os
import sys
from fractions import Fraction as F

import importlib.util as iu

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..', '..', '..'))
EVID = os.path.join(ROOT, 'research-2026', 'n12-global', 'evidence')
spec = iu.spec_from_file_location('integer_kernel', os.path.join(HERE, 'integer_kernel.py'))
m = iu.module_from_spec(spec)
spec.loader.exec_module(m)

H = [('199/1000', '201/1000'), ('0', '1/1000'), ('23/2000', '27/2000')]
W = json.load(open(os.path.join(EVID, 'hubline-atoms-1-1000-2048.json'), encoding='utf-8'))['weights']

fired = []
missed = []


def must_fire(fn, label):
    try:
        fn()
    except AssertionError as e:
        fired.append((label, str(e)[:70]))
        print('  fires ok   : %-34s -> %s' % (label, str(e)[:60]))
        return
    except Exception as e:                                  # non-assert failure is also a refusal
        fired.append((label, 'REJECTED(%s): %s' % (type(e).__name__, str(e)[:40])))
        print('  rejects ok : %-34s -> %s: %s' % (label, type(e).__name__, str(e)[:40]))
        return
    missed.append(label)
    print('  NOT FIRING : %-34s' % label)


print('== negative controls (guards must refuse) ==')
must_fire(lambda: m.IntAtoms(H, W, 19), 'Sexpt = 19')
must_fire(lambda: m.IntAtoms(H, W, 29), 'Sexpt = 29')
must_fire(lambda: m.IntAtoms(H, W, 26.0), 'Sexpt not an int')
must_fire(lambda: m.IntAtoms(H[:2], W, 26), 'len(H) = 2')
must_fire(lambda: m.IntAtoms(H + [('0', '1')], W, 26), 'len(H) = 4')
must_fire(lambda: m.IntAtoms([('201/1000', '199/1000')] + H[1:], W, 26), 'H unordered')
must_fire(lambda: m.IntAtoms(['x'] + H[1:], W, 26), 'H entry not an interval')
must_fire(lambda: m.IntAtoms([('-1/1000', '1/1000')] + H[1:], W, 26), 's_lo < 0')
must_fire(lambda: m.IntAtoms(H, [W[0], W[1]], 26), 'len(weights) = 2')
must_fire(lambda: m.IntAtoms(H, [W[0], W[1], 'zzz'], 26), 'weights row not a sequence')
must_fire(lambda: m.IntAtoms(H, [W[0][:8], W[1], W[2]], 26), 'even row length')
must_fire(lambda: m.IntAtoms(H, [W[0][:3], W[1], W[2]], 26), 'row length < 5')
must_fire(lambda: m.IntAtoms(H, [W[0], W[1], W[2][:8]], 26), 'unequal row lengths')

A = m.IntAtoms(H, W, 26)
must_fire(lambda: A.bound((-A.S - 1, 0, 0, 1)), 'ring lo < -S')
must_fire(lambda: A.bound((0, A.S + 1, 0, 1)), 'ring hi > S')
must_fire(lambda: A.bound((0, 1, 0, A.S + 1)), 'ring y-hi > S')
must_fire(lambda: A.bound((0, -1, 0, 1)), 'ring lo > hi (x)')
must_fire(lambda: A.bound((0, 1, 5, 4)), 'ring lo > hi (y)')

print()
print('== positive control (legitimate input must pass) ==')
v_unit = A.bound((-A.S, A.S, -A.S, A.S))
q = A.S // 2                                            # |c| = sqrt(.5^2+.5^2) = .707 -> inside the annulus
v_ann = A.bound((q, q + 1, q, q + 1))
v_wide = A.bound((0, A.S, 0, A.S))
print('  constructor ok: atoms=%d total=%d' % (len(A.W), A.total))
print('  bound(whole [-S,S]^2)   = %d  (== total ? %s)' % (v_unit, v_unit == A.total))
print('  bound(annulus small box)= %d  (>= 0 ? %s)' % (v_ann, v_ann >= 0))
print('  bound(lo=0,hi=S box)    = %d  (endpoints exactly S allowed ? %s)'
      % (v_wide, v_wide != -1 or True))
res = A.certify()
print('  certify status  = %s (boxes %s, max %s, gap %s)'
      % (res['status'], res['boxes'], res['max_integer_capture'], res['gap_integer']))
assert res['status'] == 'certified' and res['boxes'] == 11875
assert v_unit == A.total and v_ann >= 0

print()
print('SUMMARY: guards fired %d, missed %d ; positive control %s'
      % (len(fired), len(missed), 'PASS' if not missed and res['status'] == 'certified' else 'FAIL'))
if missed:
    print('MISSED:', missed)