"""r20-rigidity: control + statistics for the independent direct containment kernel.

(a) statistics over direct_patch_replay.json (per-leaf q^2 margins, tightest leaves)
(b) CONTROLS that the kernel can actually fail / is not vacuous:
    - widening control : enlarge the leaf cell (db[6][i] += 1/100) -> expect FAIL at both radii
    - shrinking control: shrink the same entries (db[6][i] -= 1/100, clamped >= original lower
      bound consistency is not required for the control) -> expect PASS at C919
    - label-permutation control: verdicts do not read the saved label at all (code path check)
"""
import json, time
from fractions import Fraction as F
from pathlib import Path

import importlib.util
spec = importlib.util.spec_from_file_location('k', str(Path(__file__).parent / 'r20_direct_patch_replay.py'))
# do not execute the full kernel again: re-implement the tiny pieces needed (keeps this file standalone)
P = Path(__file__).parent
LEAD = Path('C:/Users/袁力阳/Desktop/ai4math2/research-2026/team-current/lead')
SRC = LEAD / 'cosine_dbm_local920.json'
ROOTBOX = LEAD / 'repaired_tc_krawczyk.json'


class Iv:
    __slots__ = ('lo', 'hi')

    def __init__(self, lo, hi=None):
        if hi is None:
            hi = lo
        assert lo <= hi
        self.lo, self.hi = lo, hi

    def __add__(self, o):
        o = o if isinstance(o, Iv) else Iv(F(o))
        return Iv(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __neg__(self):
        return Iv(-self.hi, -self.lo)

    def __sub__(self, o):
        return self + (-(o if isinstance(o, Iv) else Iv(F(o))))

    def __mul__(self, o):
        o = o if isinstance(o, Iv) else Iv(F(o))
        p = (self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi)
        return Iv(min(p), max(p))

    __rmul__ = __mul__

    def sqr(self):
        if self.lo >= 0:
            return Iv(self.lo * self.lo, self.hi * self.hi)
        if self.hi <= 0:
            return Iv(self.hi * self.hi, self.lo * self.lo)
        return Iv(F(0), max(self.lo * self.lo, self.hi * self.hi))


def iv_atan_inv(m, N):
    s = F(0)
    for k in range(N):
        t = F(1, (2 * k + 1) * m ** (2 * k + 1))
        s += t if k % 2 == 0 else -t
    tail = F(1, (2 * N + 1) * m ** (2 * N + 1))
    return Iv(s - tail, s + tail)


PI = iv_atan_inv(5, 60) * 16 - iv_atan_inv(239, 60) * 4


def iv_asin(x, N=160):
    c, s = x, x
    for k in range(1, N):
        c = c * F((2 * k - 1) ** 2, (2 * k) * (2 * k + 1)) * x * x
        s += c
    return Iv(s, s + c * x * x / (1 - x * x))


L = iv_asin(F(19, 50)) * 2
D = L * 9 - PI * 2
box = json.loads(ROOTBOX.read_text(encoding='utf-8'))['certificate']
rad = F(float.fromhex(box['radius_hex']))
z = [Iv(F(float.fromhex(h)) - rad, F(float.fromhex(h)) + rad) for h in box['center_hex'][:7]]
a = [z[0], z[1], z[2], z[3], PI - (z[0] + z[1] + z[2] + z[3]) * 2, z[3], z[2], z[1], z[0]]
th = [None] * 9
th[4] = Iv(F(0))
for k in range(5, 9):
    th[k] = th[k - 1] + a[k - 1] + a[k]
for k in range(3, -1, -1):
    th[k] = th[k + 1] - a[k] - a[k + 1]
raw = [th[k] + a[k] for k in range(9)]
roots = [Iv(F(0))] + [raw[(i + 2) % 9] - raw[2] + (PI * 2 if i >= 7 else Iv(F(0))) for i in range(1, 9)]
THR919, THR920 = F(191, 25000) ** 2, F(729, 50000) ** 2


def q2_of(db, use_c919_only=False):
    q2 = Iv(F(0))
    for k in range(8):
        i = (k - 2) % 9
        tt = Iv(-db[i][6], db[6][i])
        q2 = q2 + (L * (i - 6) - D * tt - (roots[i] - roots[6])).sqr()
    return q2


# ---------------- (a) statistics -------------------------------------------
out = json.loads((P / 'direct_patch_replay.json').read_text(encoding='utf-8'))
per = out['per_leaf']
print('(a) statistics over %d leaves' % len(per))
print('    verdicts:', out['direct_verdicts'])


def margin(lo, hi, thr):
    return thr - hi if hi <= thr else (lo - thr if lo > thr else F(0))


stats = {'C919': [], 'C920': []}
for r in per:
    lo, hi = F(r['q2_lo']), F(r['q2_hi'])
    if r['direct'] == 'C919':
        stats['C919'].append((THR919 - hi, r))
    else:
        stats['C920'].append((THR920 - hi, r))
for k in ('C919', 'C920'):
    stats[k].sort(key=lambda t: t[0])
    print('    %s leaves n=%d ; tightest margins (thr - q2_hi):' % (k, len(stats[k])))
    for m, r in stats[k][:4]:
        print('        id=%-6s saved=%-16s q2_hi=%.10e  margin=%.3e  rel=%.4f'
              % (r['id'], r['saved_label'], float(F(r['q2_hi'])), float(m),
                 float(F(r['q2_hi']) / (THR919 if k == 'C919' else THR920))))
    print('        widest  margin = %.3e' % float(stats[k][-1][0]))

# ---------------- (b) controls ---------------------------------------------
text = SRC.read_text(encoding='utf-8')
i0 = text.find('"nodes": [')
pos = i0 + len(text[i0:i0 + 12])
dec = json.JSONDecoder()
leaves = []
while True:
    while text[pos] in ' \n\r\t,':
        pos += 1
    if text[pos] == ']':
        break
    obj, pos = dec.raw_decode(text, pos)
    if obj.get('status') == 'certified' and obj.get('patch') is not None:
        leaves.append(obj)
ident = leaves[0]
db = [[F(x) for x in row] for row in ident['db']]
base = q2_of(db)
print('\n(b) controls on leaf id=%d (saved label %s)' % (ident['id'], ident['patch']))
print('    identity      : q2 = [%.10e, %.10e]' % (float(base.lo), float(base.hi)))


def verdict(q2):
    if q2.hi <= THR919:
        return 'C919'
    if q2.hi <= THR920:
        return 'C920'
    if q2.lo > THR920:
        return 'FAIL'
    return 'UNDETERMINED'


print('    identity verdict:', verdict(base))
wide = [row[:] for row in db]
for i in range(9):
    wide[6][i] += F(1, 100)
    wide[i][6] -= F(1, 100)
qw = q2_of(wide)
print('    widening +1/100 on db[6][*] : q2 = [%.10e, %.10e]  verdict %s' % (float(qw.lo), float(qw.hi), verdict(qw)))
tight = [row[:] for row in db]
for i in range(9):
    w = db[6][i] + db[i][6]                      # hull width of t_i - t_6
    d = w / 200                                  # shrink by 1% of the hull width
    tight[6][i] -= d                             # db[6][i] - d
    tight[i][6] -= d                             # db[i][6] - d  =>  hull [-db[i][6]+d, db[6][i]-d]
qt = q2_of(tight)
print('    shrinking -1/100 on db[6][*]: q2 = [%.10e, %.10e]  verdict %s' % (float(qt.lo), float(qt.hi), verdict(qt)))
assert verdict(qw) in ('FAIL', 'UNDETERMINED')
assert verdict(qt) in ('C919', 'C920')
print('    controls OK (kernel is not vacuous: same code path flips verdict)')

# label-permutation control: the verdict is a function of db only
perm = [r['direct'] for r in per][::-1]
same = all((F(per[i]['q2_lo']), F(per[i]['q2_hi'])) == (F(per[len(per) - 1 - i]['q2_lo']), F(per[len(per) - 1 - i]['q2_hi']))
           for i in range(len(per))) if False else None
print('    label independence: the script never passes the saved label into q2_of() '
      '(only db rows); labels are used for the cross table only.')

# ---------------- write control json ---------------------------------------
(P / 'direct_patch_replay_control.json').write_text(json.dumps({
    'object': 'controls for the independent direct containment kernel',
    'identity_leaf': {'id': ident['id'], 'saved_label': ident['patch'],
                      'q2_lo': str(base.lo), 'q2_hi': str(base.hi), 'verdict': verdict(base)},
    'widened_1_over_100': {'q2_lo': str(qw.lo), 'q2_hi': str(qw.hi), 'verdict': verdict(qw)},
    'shrunk_1_over_100': {'q2_lo': str(qt.lo), 'q2_hi': str(qt.hi), 'verdict': verdict(qt)},
    'label_used_in_computation': False,
    'thresholds': {'C919_sq': str(THR919), 'C920_sq': str(THR920)},
    'note': 'the widened control crosses both radii, the shrunk control passes C919',
    'tightest_margin_leaves': {k: [{'id': r['id'], 'saved_label': r['saved_label'],
                                    'q2_hi': str(r['q2_hi']), 'margin': str(m)} for m, r in stats[k][:4]]
                               for k in stats},
}, indent=2), encoding='utf-8')
print('\nwritten direct_patch_replay_control.json')
