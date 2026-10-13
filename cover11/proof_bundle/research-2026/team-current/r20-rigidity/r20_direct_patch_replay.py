"""r20-rigidity: INDEPENDENT DIRECT CONTAINMENT KERNEL for the 120 patch-certified
leaves of the fixed global DBM tree.

Lead obligation (2026-09-26):
  * the last 120 local leaves are currently replayed through lead/replay_closed_dbm.py,
    which calls known_patch(db) and can therefore ride on the historical branches
    (C913 / C914-corner / C916 / C915 / C918 / reflected variants);
  * build a READ-ONLY, INDEPENDENT, DIRECT containment kernel that reads ONLY
      - lead/cosine_dbm_local920.json      (leaf cells; db = exact DBM cell data)
      - lead/repaired_tc_krawczyk.json     (the exact dyadic C891 root box)
    and, per leaf, verifies the RAW8 DIRECT bound  q^2 <= (191/25000)^2  or
    q^2 <= (729/50000)^2, WITHOUT calling known_patch and WITHOUT trusting the
    saved patch names;
  * also re-check the radii C919 = 191/25000, C920 = 729/50000 and the
    growth = 1/100000 certificates (constants from the two registered certificate
    JSON files, exact rational arithmetic);
  * the C891 root contraction is NOT re-audited (box taken as given);
  * write only into r20-rigidity/ (direct_patch_replay.json + this script); no subagents.

Independence / rigor
  * no lead module is imported; the chart is re-derived from its definition
        theta_i = i*L - D*t_i ,  L = 2*asin(19/50),  D = 9L - 2*pi,
    so the raw8 coordinate k (k=0..7) is the deviation of theta_i - theta_6
    (i = (k-2) mod 9) from its value at the exact C891 root:
        h_k = (i-6)*L - D*(t_i - t_6) - (theta*_i - theta*_6).
  * ALL arithmetic is exact rational. The only transcendental inputs are enclosed
    as rational intervals: pi by Machin's formula (alternating tails bounded by the
    first omitted term), asin(19/50) by its positive binomial series with the ratio
    bound c_{k+1}/c_k <= x^2. mpmath is not used.
  * the root angles are intervals built from the dyadic C891 box (hex centre, exact
    binary64 radius).
  * verdict = PASS only if the whole q^2 interval is <= the exact rational square;
    FAIL only if strictly above; otherwise UNDETERMINED (straddle). The 8 coordinate
    hulls are used independently, i.e. q^2 is over-estimated (conservative).
"""
import json, time, hashlib
from fractions import Fraction as F
from pathlib import Path

P = Path(__file__).parent
LEAD = Path('C:/Users/袁力阳/Desktop/ai4math2/research-2026/team-current/lead')
SRC = LEAD / 'cosine_dbm_local920.json'
ROOTBOX = LEAD / 'repaired_tc_krawczyk.json'
CERT919 = LEAD / 'anisotropic_stress_ball_certificate.json'
CERT920 = LEAD / 'relative_stress_ball_certificate.json'

# ---------------------------------------------------------------- intervals ---
class Iv:
    __slots__ = ('lo', 'hi')

    def __init__(self, lo, hi=None):
        if hi is None:
            hi = lo
        assert lo <= hi
        self.lo = lo
        self.hi = hi

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

    def __repr__(self):
        return '[%.12e, %.12e]' % (float(self.lo), float(self.hi))


def iv_atan_inv(m, N):
    assert m > 1
    s = F(0)
    for k in range(N):
        t = F(1, (2 * k + 1) * m ** (2 * k + 1))
        s += t if k % 2 == 0 else -t
    tail = F(1, (2 * N + 1) * m ** (2 * N + 1))
    return Iv(s - tail, s + tail)


PI = iv_atan_inv(5, 60) * 16 - iv_atan_inv(239, 60) * 4


def iv_asin(x, N=160):
    assert 0 < x < 1
    c = x
    s = c
    for k in range(1, N):
        c = c * F((2 * k - 1) ** 2, (2 * k) * (2 * k + 1)) * x * x
        s += c
    return Iv(s, s + c * x * x / (1 - x * x))


ASIN = iv_asin(F(19, 50))
L = ASIN * 2
D = L * 9 - PI * 2
print('pi  width %.3e   L width %.3e   D width %.3e' % (float(PI.hi - PI.lo), float(L.hi - L.lo), float(D.hi - D.lo)))
print('L  midpoint = %.22f' % float(L.lo + (L.hi - L.lo) / 2))
print('D  midpoint = %.22f' % float(D.lo + (D.hi - D.lo) / 2))

# --------------------------------------------------- C891 root box -> thetas --
box = json.loads(ROOTBOX.read_text(encoding='utf-8'))['certificate']
rad = F(float.fromhex(box['radius_hex']))
assert len(box['center_hex']) >= 7
z = []
for hxx in box['center_hex'][:7]:
    c = F(float.fromhex(hxx))
    z.append(Iv(c - rad, c + rad))
a = [z[0], z[1], z[2], z[3], PI - (z[0] + z[1] + z[2] + z[3]) * 2, z[3], z[2], z[1], z[0]]
th = [None] * 9
th[4] = Iv(F(0))
for k in range(5, 9):
    th[k] = th[k - 1] + a[k - 1] + a[k]
for k in range(3, -1, -1):
    th[k] = th[k + 1] - a[k] - a[k + 1]
raw = [th[k] + a[k] for k in range(9)]
roots = [Iv(F(0))]
for i in range(1, 9):
    roots.append(raw[(i + 2) % 9] - raw[2] + (PI * 2 if i >= 7 else Iv(F(0))))
print('root angle halfwidths (max over i): %.3e rad' % float(max((roots[i].hi - roots[i].lo) / 2 for i in range(9))))

# ----------------------------------------------------- stream the 120 leaves --
t0 = time.time()
text = SRC.read_text(encoding='utf-8')
key = '"nodes": ['
i0 = text.find(key)
assert i0 > 0
pos = i0 + len(key)
dec = json.JSONDecoder()
leaves, n_nodes, status_count = [], 0, {}
while True:
    while text[pos] in ' \n\r\t,':
        pos += 1
    if text[pos] == ']':
        break
    obj, pos = dec.raw_decode(text, pos)
    n_nodes += 1
    st = obj.get('status')
    status_count[st] = status_count.get(st, 0) + 1
    if st == 'certified' and obj.get('patch') is not None:
        leaves.append(obj)
print('parsed %d nodes in %.1f s ; statuses %s ; patch leaves = %d'
      % (n_nodes, time.time() - t0, status_count, len(leaves)))

# ---------------------------------------------- direct raw8 containment check --
THR919 = F(191, 25000) ** 2
THR920 = F(729, 50000) ** 2
assert F(191, 25000) == F(764, 100000) and F(729, 50000) == F(1458, 100000)

rows = []
for lf in leaves:
    db = [[F(x) for x in row] for row in lf['db']]
    assert len(db) == 10 and all(len(r) == 10 for r in db)
    assert db[0][9] == 1 and db[9][0] == -1 and all(db[i][i] == 0 for i in range(10))
    q2 = Iv(F(0))
    hs = []
    for k in range(8):
        i = (k - 2) % 9
        tt = Iv(-db[i][6], db[6][i])                    # t_i - t_6  (DBM hull)
        h = L * (i - 6) - D * tt - (roots[i] - roots[6])
        hs.append(h)
        q2 = q2 + h.sqr()
    rows.append({'id': lf['id'], 'saved_label': lf['patch'], 'depth': lf.get('depth'),
                 'q2_lo': q2.lo, 'q2_hi': q2.hi})

summary = {'PASS_C919': 0, 'PASS_C920': 0, 'FAIL_both': 0, 'UNDETERMINED': 0}
label_cross, fails, undet = {}, [], []
for r in rows:
    lo, hi = r['q2_lo'], r['q2_hi']
    if hi <= THR919:
        r['direct'] = 'C919'
    elif hi <= THR920:
        r['direct'] = 'C920'
    elif lo > THR920:
        r['direct'] = 'FAIL'
        fails.append(r)
    else:
        r['direct'] = 'UNDETERMINED'
        undet.append(r)
    summary[{'C919': 'PASS_C919', 'C920': 'PASS_C920', 'FAIL': 'FAIL_both',
             'UNDETERMINED': 'UNDETERMINED'}[r['direct']]] += 1
    label_cross.setdefault(r['saved_label'], []).append(r['direct'])

print('\ndirect verdicts:', summary)
print('saved-label cross table:')
for k in sorted(label_cross):
    v = label_cross[k]
    print('   %-22s n=%3d  %s' % (k, len(v), {d: v.count(d) for d in sorted(set(v))}))
if fails:
    print('\nFAIL (q^2 strictly above both radii):')
    for r in fails:
        print('   id=%-6s saved=%-20s q2=[%.8e, %.8e]' % (r['id'], r['saved_label'], float(r['q2_lo']), float(r['q2_hi'])))
if undet:
    print('\nUNDETERMINED (interval straddles a threshold):')
    for r in undet:
        print('   id=%-6s saved=%-20s q2=[%.8e, %.8e]' % (r['id'], r['saved_label'], float(r['q2_lo']), float(r['q2_hi'])))

# ------------------------------------------------- constants / growth checks --
def growth_check(tau, tau0, mu, B, A, C, G, d, q, growth):
    pos = tau * B * G * q
    quartic = d / 3 + tau ** 2 * (B * d + A) ** 2 / (4 * (tau - tau0))
    coeff = mu / 2 - C * q - quartic * q * q
    return {'positivity_lhs': str(pos), 'positivity_ok': bool(pos < 1),
            'positivity_margin': str(1 - pos),
            'quartic': str(quartic), 'coefficient': str(coeff),
            'coefficient_float': float(coeff), 'above_growth': bool(coeff > growth),
            'margin_over_growth': str(coeff - growth)}


c919 = json.loads(CERT919.read_text(encoding='utf-8'))
c920 = json.loads(CERT920.read_text(encoding='utf-8'))
chk = {
    'C919_radius': {'claimed': '191/25000', 'exact': str(F(191, 25000)),
                    'equals_certificate_rho': F(c919['constants']['rho']) == F(191, 25000),
                    'certificate_rho': c919['constants']['rho'], 'squared': str(THR919)},
    'C920_radius': {'claimed': '729/50000', 'exact': str(F(729, 50000)),
                    'equals_certificate_rho': F(c920['constants']['rho']) == F(729, 50000),
                    'certificate_rho': c920['constants']['rho'], 'squared': str(THR920)},
    'growth_value': {'C919': c919['constants']['growth'], 'C920': c920['constants']['growth'],
                     'both_equal_1_over_100000': F(c919['constants']['growth']) == F(1, 100000)
                                                 and F(c920['constants']['growth']) == F(1, 100000)},
    'C919_growth_check': growth_check(F(1, 10), F(1, 20), F(1, 500), F(182), F(1074, 1000),
                                      F(358, 10000), F(1892, 1000), F(80, 1000),
                                      F(191, 25000), F(1, 100000)),
    'C920_growth_check': growth_check(F(1468), F(734), F(18, 10000), F(495, 1000), F(858, 100000),
                                      F(358, 10000), F(15363, 1000000), F(80, 1000),
                                      F(729, 50000), F(1, 100000)),
    'certificate_recorded_coefficient_lower': {'C919': c919['diagnostics']['coefficient_lower'],
                                               'C920': c920['diagnostics']['coefficient_lower']},
    'recorded_vs_exact_coefficient': {
        'C919_recorded_leq_exact': F(c919['diagnostics']['coefficient_lower'])
                                   <= F(growth_check(F(1, 10), F(1, 20), F(1, 500), F(182), F(1074, 1000),
                                                     F(358, 10000), F(1892, 1000), F(80, 1000),
                                                     F(191, 25000), F(1, 100000))['coefficient']),
        'C920_recorded_leq_exact': F(c920['diagnostics']['coefficient_lower'])
                                   <= F(growth_check(F(1468), F(734), F(18, 10000), F(495, 1000),
                                                     F(858, 100000), F(358, 10000), F(15363, 1000000),
                                                     F(80, 1000), F(729, 50000), F(1, 100000))['coefficient']),
    },
}
print('\nconstants / growth recheck (exact rationals):')
print(json.dumps(chk, indent=2, default=str))

out = {
    'caliber': ('read-only independent DIRECT containment kernel; exact rational interval arithmetic; '
                'inputs = cosine_dbm_local920.json + repaired_tc_krawczyk.json (C891 dyadic box); '
                'known_patch NOT called, saved patch names NOT trusted (only cross-tabulated); '
                'C891 root contraction NOT re-audited'),
    'inputs': {'source': str(SRC), 'rootbox': str(ROOTBOX),
               'certificates': [str(CERT919), str(CERT920)],
               'sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (SRC, ROOTBOX, CERT919, CERT920)}},
    'enclosure_widths': {'pi': float(PI.hi - PI.lo), 'L': float(L.hi - L.lo), 'D': float(D.hi - D.lo)},
    'n_nodes_parsed': n_nodes, 'node_status_counts': status_count, 'n_patch_leaves': len(leaves),
    'thresholds': {'C919_radius': '191/25000', 'C919_radius_sq': str(THR919),
                   'C920_radius': '729/50000', 'C920_radius_sq': str(THR920)},
    'direct_verdicts': summary,
    'saved_label_cross_table': {k: {d: v.count(d) for d in sorted(set(v))} for k, v in label_cross.items()},
    'fails': [{'id': r['id'], 'saved_label': r['saved_label'], 'q2_lo': str(r['q2_lo']), 'q2_hi': str(r['q2_hi'])}
              for r in fails],
    'undetermined': [{'id': r['id'], 'saved_label': r['saved_label'], 'q2_lo': str(r['q2_lo']), 'q2_hi': str(r['q2_hi'])}
                     for r in undet],
    'per_leaf': [{'id': r['id'], 'saved_label': r['saved_label'], 'depth': r['depth'], 'direct': r['direct'],
                  'q2_lo': str(r['q2_lo']), 'q2_hi': str(r['q2_hi'])} for r in rows],
    'constants_and_growth': chk,
    'seconds': time.time() - t0,
}
(P / 'direct_patch_replay.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
print('\nwritten direct_patch_replay.json  (%.1f s total)' % (time.time() - t0))
