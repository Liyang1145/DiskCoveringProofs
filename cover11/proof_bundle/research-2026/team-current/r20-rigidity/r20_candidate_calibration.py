"""r20-rigidity step 1: independent calibration of the saved n11 candidate.

Objects (read-only):
  n11/upper/certified_object.json      -- 22 integers / 1e17 (saved certified upper object)
Caliber: D = closed unit disk, 11 equal disks radius R, centre units = D radius, radians.
No symmetry / no active-set assumption is used; everything is recomputed from centres.

Outputs: r20_calibration.json, and a printed summary.
Sections:
  A. centre calibration (moduli/angles), mirror-symmetry test (min mismatch over all axes)
  B. FULL critical set of the covering radius: all triple circumcentres inside D,
     all perpendicular-bisector intersections with bd D (both branches), with the
     "pair/ triple really nearest" flags; level ledger.
  C. the 20 metric local radii of the angle-only model:
        11 site-face circumradii (Delaunay faces) + 9 switch radii |P_i - c_i|
     -> which saturate the max (= the covering radius), which carry slack.
  D. 60-dps confirmation of the tight/slack values and of the next critical level.
"""
import json, math, itertools, os
from pathlib import Path
import numpy as np

P = Path(__file__).parent
ROOT = P.parents[2]
OUT = {}

raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
C = np.array([[int(v) / 1e17 for v in a] for a in raw['centers_scaled_1e17']], dtype=float)
LO = float(raw['certified_interval']['lo'])
HI = float(raw['certified_interval']['hi'])
HUBS = [0, 2]
RINGS = [i for i in range(11) if i not in HUBS]
n = 11

# ---------- A. calibration -------------------------------------------------
mod = np.linalg.norm(C, axis=1)
ang = np.arctan2(C[:, 1], C[:, 0])
order = sorted(RINGS, key=lambda i: ang[i])
cyc = [order[(k + 1) % 9] - order[k] for k in range(9)]
OUT['A'] = {
    'hub_moduli': {str(i): float(mod[i]) for i in HUBS},
    'ring_moduli': {str(i): float(mod[i]) for i in order},
    'ring_angles_deg': {str(i): float(math.degrees(ang[i])) for i in order},
    'induced_cyclic_order': order,
    'hub_separation': float(np.linalg.norm(C[0] - C[2])),
    'hub_hub_minus_2R': float(np.linalg.norm(C[0] - C[2]) - 2 * LO),
    'ring_min_modulus': float(min(mod[i] for i in RINGS)),
    'ring_max_modulus': float(max(mod[i] for i in RINGS)),
    'hub_plus_LO': {str(i): float(mod[i] + LO) for i in HUBS},
}


def mirror_mismatch(C, axis_angle):
    """max_i min_j |C_j - Refl(C_i)| ; a site fixed by the reflection is allowed
    to match itself, so no index is excluded."""
    Rm = np.array([[math.cos(2 * axis_angle), math.sin(2 * axis_angle)],
                   [math.sin(2 * axis_angle), -math.cos(2 * axis_angle)]])
    Cr = C @ Rm
    worst = 0.0
    for i in range(len(C)):
        worst = max(worst, float(np.linalg.norm(C - Cr[i], axis=1).min()))
    return worst


axes = []
for i in range(n):
    axes.append(('through site %d' % i, ang[i]))
for i in range(n):
    for j in range(i + 1, n):
        a2 = math.atan2(C[i, 1] + C[j, 1], C[i, 0] + C[j, 0])
        axes.append(('bisector of %d,%d' % (i, j), a2))
        a3 = math.atan2(C[i, 1] - C[j, 1], C[i, 0] - C[j, 0])
        axes.append(('line %d-%d' % (i, j), a3))
best = min(((mirror_mismatch(C, a), name, a) for name, a in axes), key=lambda t: t[0])
# refine the best axis locally
_, name0, a0 = best
for it in range(4000):
    a0c = a0 + 1e-3 * math.cos(2 * math.pi * it / 4000)
    m = mirror_mismatch(C, a0c)
    if m < best[0]:
        best = (m, name0 + ' (refined)', a0c)
OUT['A']['best_mirror_axis'] = {
    'initial_label': best[1],
    'mismatch_max': best[0],
    'axis_angle_deg': float(math.degrees(best[2])) if best[2] is not None else None,
    'comment': 'mismatch ~1e-17 => exact mirror symmetry; ~1e-3 => none',
}
# explicit hub test: are the two hubs on one line through the origin?
cr = C[0, 0] * C[2, 1] - C[0, 1] * C[2, 0]
OUT['A']['hub_cross_product'] = float(cr)
OUT['A']['hub_cross_relative'] = float(abs(cr) / (mod[0] * mod[2]))

# ---------- B. full critical set -------------------------------------------
def critical_points(C):
    pts = []
    for (i, j, k) in itertools.combinations(range(n), 3):
        A = np.array([C[j] - C[i], C[k] - C[i]])
        b = 0.5 * np.array([C[j] @ C[j] - C[i] @ C[i], C[k] @ C[k] - C[i] @ C[i]])
        det = A[0, 0] * A[1, 1] - A[0, 1] * A[1, 0]
        if abs(det) < 1e-14:
            continue
        u = np.linalg.solve(A, b)
        if u @ u > 1.0:
            continue
        d = np.linalg.norm(C - u, axis=1)
        nearest = sorted(range(n), key=lambda t: d[t])
        pts.append({'kind': 'V3', 'sites': (i, j, k), 'point': u.tolist(),
                    'value': float(d.min()),
                    'is_critical': set(nearest[:3]) == {i, j, k},
                    'circumradius': float(np.linalg.norm(u - C[i])),
                    'nearest': nearest[:4], 'dist4': [float(d[t]) for t in nearest[:4]]})
    for (i, j) in itertools.combinations(range(n), 2):
        dv = C[i] - C[j]
        dd = dv @ dv
        if dd < 1e-14:
            continue
        A0 = (0.5 * (C[i] @ C[i] - C[j] @ C[j]) / dd) * dv
        nv = np.array([-dv[1], dv[0]]) / math.sqrt(dd)
        s2 = 1.0 - A0 @ A0
        if s2 <= 0:
            continue
        s = math.sqrt(s2)
        for sgn in (+1, -1):
            p = A0 + sgn * s * nv
            d = np.linalg.norm(C - p, axis=1)
            nearest = sorted(range(n), key=lambda t: d[t])
            pts.append({'kind': 'V2b', 'sites': (i, j), 'point': p.tolist(),
                        'value': float(d.min()),
                        'is_critical': set(nearest[:2]) == {i, j},
                        'nearest': nearest[:4], 'dist4': [float(d[t]) for t in nearest[:4]]})
    return pts


pts = critical_points(C)
crit = [p for p in pts if p['is_critical']]
gam = max(p['value'] for p in crit)
levels = sorted({round(p['value'], 14) for p in crit}, reverse=True)
tight = [p for p in crit if p['value'] > gam - 1e-9]
OUT['B'] = {
    'n_critical_points': len(crit),
    'n_points_total': len(pts),
    'covering_radius_num': gam,
    'certified_interval_lo': LO, 'certified_interval_hi': HI,
    'radius_minus_lo': gam - LO,
    'n_tight_within_1e-9': len(tight),
    'tight_points': sorted(
        [{'kind': p['kind'], 'sites': list(p['sites']),
          'value_minus_lo': p['value'] - LO, 'point': p['point']} for p in tight],
        key=lambda q: q['value_minus_lo']),
    'top_levels': levels[:12],
    'gap_top_to_next': levels[0] - levels[1] if len(levels) > 1 else None,
}
# full ledger of near-top points (print for the report)
led = sorted([(p['value'], p['kind'], p['sites']) for p in crit], reverse=True)
OUT['B']['ledger_top40'] = [[float(v), k, list(s)] for v, k, s in led[:40]]

# ---------- C. the 20 metric local radii ------------------------------------
from scipy.spatial import Delaunay
tri = Delaunay(C)
faces = [tuple(int(t) for t in s) for s in tri.simplices]
face_rad, face_ctr = [], []
for f in faces:
    p = C[list(f)]
    # circumcentre
    A = np.array([p[1] - p[0], p[2] - p[0]])
    b = 0.5 * np.array([p[1] @ p[1] - p[0] @ p[0], p[2] @ p[2] - p[0] @ p[0]])
    u = np.linalg.solve(A, b)
    face_rad.append(float(np.linalg.norm(u - p[0])))
    face_ctr.append(u.tolist())
# switch points: nearest-site bisector of consecutive rings in induced order
sw = []
for k in range(9):
    i, j = order[k], order[(k + 1) % 9]
    dv = C[i] - C[j]
    dd = dv @ dv
    A0 = (0.5 * (C[i] @ C[i] - C[j] @ C[j]) / dd) * dv
    nv = np.array([-dv[1], dv[0]]) / math.sqrt(dd)
    s = math.sqrt(1.0 - A0 @ A0)
    cand = []
    for sgn in (+1, -1):
        q = A0 + sgn * s * nv
        d = np.linalg.norm(C - q, axis=1)
        if set(np.argsort(d)[:2]) == {i, j}:          # (i,j) really the two nearest
            cand.append((float(d.min()), q))
    assert cand, (i, j)
    p = max(cand, key=lambda t: t[0])[1]               # the local max on bd D
    # cross-check against the independently computed critical list
    match = [cp for cp in crit if cp['kind'] == 'V2b' and set(cp['sites']) == {i, j}]
    if match:
        assert np.linalg.norm(np.array(match[0]['point']) - p) < 1e-12, (i, j)
    sw.append((i, j, p.tolist(), float(np.linalg.norm(p - C[i]))))
radii = ([{'idx': k, 'type': 'site_face', 'sites': list(faces[k]), 'radius': face_rad[k],
           'circumcentre': face_ctr[k]} for k in range(len(faces))]
         + [{'idx': 11 + k, 'type': 'switch', 'sites': [sw[k][0], sw[k][1]],
             'radius': sw[k][3], 'point': sw[k][2]} for k in range(9)])
M = max(r['radius'] for r in radii)
for r in radii:
    r['rel_to_max'] = r['radius'] / M
    r['saturated'] = bool(r['radius'] > M - 1e-12)
sat = [r for r in radii if r['saturated']]
slack = [r for r in radii if not r['saturated']]
OUT['C'] = {
    'n_local_radii': len(radii), 'max_local_radius': M,
    'n_saturated': len(sat), 'n_slack': len(slack),
    'saturated_sites': [r['sites'] for r in sat],
    'slack': [{'type': r['type'], 'sites': r['sites'], 'radius': r['radius'],
               'rel': r['rel_to_max'], 'abs_slack_vs_max': M - r['radius']} for r in slack],
    'radii': radii,
}

# ---------- D. 60-dps confirmation ------------------------------------------
import mpmath as mp
mp.mp.dps = 60
Cm = [[mp.mpf(int(v)) / mp.mpf(10) ** 17 for v in a] for a in raw['centers_scaled_1e17']]
Cmp = mp.matrix(Cm)


def dist_m(p, q):
    return mp.sqrt(sum((p[t] - q[t]) ** 2 for t in range(2)))


hi_vals = []
for p in tight:
    u = mp.matrix(p['point'])
    d = min(dist_m(u, mp.matrix(Cm[t])) for t in range(11))
    hi_vals.append((p['kind'], tuple(p['sites']), mp.nstr(d - mp.mpf(raw['certified_interval']['lo']), 8)))
OUT['D'] = {
    'tight_values_minus_lo_60dps': [[k, list(s), v] for k, s, v in hi_vals],
}
# exact-ish value of the two slack radii (60 dps)
sl = []
for r in slack:
    if r['type'] == 'switch':
        p = mp.matrix(r['point'])
        i = r['sites'][0]
        v = dist_m(p, mp.matrix(Cm[i]))
    else:
        f = r['sites']
        p = [Cmp[f[k], :] for k in range(3)]
        # circumradius from side lengths
        a = dist_m(p[1], p[2]); b = dist_m(p[0], p[2]); c = dist_m(p[0], p[1])
        ar = (a + b + c) / 2
        area2 = mp.sqrt(ar * (ar - a) * (ar - b) * (ar - c))
        v = a * b * c / (4 * area2)
    sl.append({'type': r['type'], 'sites': r['sites'],
               'radius_60dps': mp.nstr(v, 30),
               'slack_vs_lo': mp.nstr(mp.mpf(LO) - v, 8),
               'rel_slack': mp.nstr((mp.mpf(LO) - v) / mp.mpf(LO), 8)})
OUT['D']['slack_radii_60dps'] = sl

(P / 'r20_calibration.json').write_text(json.dumps(OUT, indent=2), encoding='utf-8')

print('=== A. calibration ===')
print('hub moduli', OUT['A']['hub_moduli'], 'ring moduli', OUT['A']['ring_moduli'])
print('induced cyclic order', order)
print('best mirror axis:', OUT['A']['best_mirror_axis'])
print('hub cross product (rel):', OUT['A']['hub_cross_product'], OUT['A']['hub_cross_relative'])
print('=== B. critical set ===')
print('n critical points', len(crit), ' gamma =', repr(gam))
print('gamma - certified lo =', gam - LO, ' (hi-lo =', HI - LO, ')')
print('n tight (<1e-9):', len(tight))
print('top levels:', levels[:6])
print('gap top->next:', OUT['B']['gap_top_to_next'])
print('ledger top 24:')
for v, k, s in led[:24]:
    print('   %.17f %-4s %s' % (v, k, s))
print('=== C. 20 local radii ===')
print('max local radius', M, ' saturated:', len(sat), ' slack:', len(slack))
for r in slack:
    print('  SLACK', r['type'], r['sites'], 'radius=%.15f' % r['radius'],
          'rel=%.12f' % r['rel_to_max'], 'abs_slack=%.6e' % (M - r['radius']))
print('=== D. 60 dps ===')
for k, s, v in hi_vals:
    print('   %-4s %s  d-lo = %s' % (k, s, v))
for r in sl:
    print('   SLACK', r)
