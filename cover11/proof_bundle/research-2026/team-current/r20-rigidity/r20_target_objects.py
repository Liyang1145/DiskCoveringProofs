"""r20-rigidity continuation (step 8): decide the relation between the saved 1e-17 object
and the two "ideal" 1e-60 / 17-digit symmetric objects, at high precision.

Read-only inputs:
  n11/upper/certified_object.json               x*  (22 ints / 1e17, certified UB C529)
  research-2026/session2/n11alg/cert_sym60.json X60 (22 ints / 1e60, registered RD_interval)
  n11/kkt2/frozen.json                          Xf  (17-digit KKT frozen object, R=0.37998385311983857)

Sections (all at 80 dps, exact rational inputs, no float parsing of the literals):
  A  label correspondence between x* and X60 / Xf  (assignment on the projection)
  B  full critical set of each object: covering radius and ledger (V3 inside D with the
     3 sites really nearest; V2b = bisector x bdD with the 2 sites really nearest)
  C  active-set Jacobian J18 at each object: singular values, rank, left-null sign pattern
  D  Gordan/Danskin decision: min over the simplex of ||J^T lambda||
  E  the symmetric image of x* and the distance to X60 along the near-null direction

No claim registered; numeric/structural diagnosis only. Writes r20_target_objects.json.
"""
import json, math, itertools, sys
from pathlib import Path
import numpy as np
import mpmath as mp

P = Path(__file__).parent
ROOT = P.parents[2]
mp.mp.dps = 80
N = 11

# ---------------------------------------------------------------- loaders
def load_scaled(path, key, scale):
    d = json.loads((ROOT / path).read_text(encoding='utf-8-sig'))
    rows = d[key]
    return [mp.matrix([mp.mpf(int(v)) / scale for v in a]) for a in rows], d


def load_float(path, key):
    d = json.loads((ROOT / path).read_text(encoding='utf-8-sig'))
    return [mp.matrix([mp.mpf(repr(x)) for x in a]) for a in d[key]], d


XS, dxs = load_scaled('n11/upper/certified_object.json', 'centers_scaled_1e17', mp.mpf(10) ** 17)
X60, d60 = load_scaled('research-2026/session2/n11alg/cert_sym60.json', 'centers_scaled_1e60', mp.mpf(10) ** 60)
XF, dfz = load_float('n11/kkt2/frozen.json', 'centers')
LO = mp.mpf(dxs['certified_interval']['lo'])
HI = mp.mpf(dxs['certified_interval']['hi'])
RD60 = mp.mpf(d60['RD_interval'][0].split(',')[0].lstrip('['))

OBJ = {'x* (1e-17 saved)': XS, 'X60 (1e-60 sym)': X60, 'Xf (17d KKT)': XF}


# ---------------------------------------------------------------- geometry
def circ(C, tri):
    a, b, c = tri
    A = mp.matrix([[C[b][0] - C[a][0], C[b][1] - C[a][1]],
                   [C[c][0] - C[a][0], C[c][1] - C[a][1]]])
    rhs = mp.matrix([(sum(C[b][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2,
                     (sum(C[c][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2])
    det = A[0, 0] * A[1, 1] - A[0, 1] * A[1, 0]
    if abs(det) < mp.mpf('1e-25'):
        return None
    return mp.lu_solve(A, rhs)


def bis_bd(C, i, j, sgn):
    dv = C[i] - C[j]
    dd = sum(dv[t] ** 2 for t in range(2))
    A0 = mp.matrix([(sum(C[i][t] ** 2 for t in range(2)) - sum(C[j][t] ** 2 for t in range(2))) / 2
                    / dd * dv[t] for t in range(2)])
    nv = mp.matrix([-dv[1] / mp.sqrt(dd), dv[0] / mp.sqrt(dd)])
    s2 = 1 - sum(A0[t] ** 2 for t in range(2))
    if s2 <= 0:
        return None
    return mp.matrix([A0[t] + sgn * mp.sqrt(s2) * nv[t] for t in range(2)])


def d2p(p, q):
    return mp.sqrt(sum((p[t] - q[t]) ** 2 for t in range(2)))


def critical_set(C):
    """full candidate critical set with the 'really nearest' flags (80 dps)"""
    out = []
    for tri in itertools.combinations(range(N), 3):
        u = circ(C, tri)
        if u is None:
            continue
        nu = sum(u[t] ** 2 for t in range(2))
        if nu > 1:
            continue
        ds = sorted((d2p(u, C[q]), q) for q in range(N))
        out.append({'kind': 'V3', 'sites': list(tri), 'point': [u[0], u[1]],
                    'value': ds[0][0], 'critical': set(q for _, q in ds[:3]) == set(tri),
                    'margin': ds[3][0] - ds[0][0], 'inside': 1 - nu})
    for i, j in itertools.combinations(range(N), 2):
        for sgn in (1, -1):
            p = bis_bd(C, i, j, sgn)
            if p is None:
                continue
            ds = sorted((d2p(p, C[q]), q) for q in range(N))
            out.append({'kind': 'V2b', 'sites': [i, j], 'sgn': sgn, 'point': [p[0], p[1]],
                        'value': ds[0][0], 'critical': set(q for _, q in ds[:2]) == {i, j},
                        'margin': ds[2][0] - ds[0][0]})
    return out


def gamma_of(C, crit):
    return max(p['value'] for p in crit if p['critical'])


# ---------------------------------------------------------------- A. correspondence
def match(Ca, Cb):
    D = np.array([[float(d2p(Ca[i], Cb[j])) for j in range(N)] for i in range(N)])
    from scipy.optimize import linear_sum_assignment
    r, c = linear_sum_assignment(D)
    return [(int(i), int(j)) for i, j in zip(r, c)], float(D[r, c].max())


print('=== A. correspondence (identity-label displacement matrix) ===')
report = {}
for name, CX in OBJ.items():
    if CX is XS:
        continue
    perm, worst = match(XS, CX)
    ident = max(float(d2p(XS[i], CX[i])) for i in range(N))
    print('  x* -> %-16s : optimal assignment worst = %.6e ; identity worst = %.6e'
          % (name, worst, ident))
    print('     perm (i -> j):', perm)
    report[name] = {'worst_opt': worst, 'worst_identity': ident, 'perm': perm}

# also: mirror test for X60 (is it exactly mirror symmetric?)
def mirror_mismatch(C, axis):
    Rm = mp.matrix([[mp.cos(2 * axis), mp.sin(2 * axis)], [mp.sin(2 * axis), -mp.cos(2 * axis)]])
    worst = mp.mpf(0)
    for i in range(N):
        p = mp.matrix([C[i][0] * Rm[0, 0] + C[i][1] * Rm[1, 0],
                       C[i][0] * Rm[0, 1] + C[i][1] * Rm[1, 1]])
        worst = max(worst, min(d2p(p, C[j]) for j in range(N)))
    return worst


print('\n=== A2. mirror structure of X60 (refined axis search) ===')
axs = [(mp.atan2(C[1], C[0]), 'site %d' % i) for i, C in [(i, X60[i]) for i in range(N)]]
best = (mp.inf, None, None)
for a0, lab in axs:
    for d in np.linspace(-0.6, 0.6, 121):
        aa = a0 + mp.mpf(float(d))
        m = mirror_mismatch(X60, aa)
        if m < best[0]:
            best = (m, lab, aa)
print('  best axis from %s : mismatch = %s' % (best[1], mp.nstr(best[0], 6)))
print('  x* mirror mismatch (from calibration): 3.526093e-09 (axis -90.062deg)')
report['X60_mirror'] = {'axis_deg': mp.nstr(best[2] * 180 / mp.pi, 12), 'mismatch': mp.nstr(best[0], 8)}

# ---------------------------------------------------------------- B. critical sets
print('\n=== B. critical sets and covering radii (80 dps) ===')
for name, CX in OBJ.items():
    crit = critical_set(CX)
    gam = gamma_of(CX, crit)
    critc = [p for p in crit if p['critical']]
    tight = [p for p in critc if p['value'] > gam - mp.mpf('1e-9')]
    lev = sorted({mp.nstr(p['value'], 20) for p in critc}, reverse=True)
    print('  %-18s gamma = %s' % (name, mp.nstr(gam, 40)))
    print('      #critical = %d, #tight(<1e-9) = %d' % (len(critc), len(tight)))
    tops = sorted(critc, key=lambda p: -p['value'])[:6]
    for p in tops:
        print('      %-4s %-12s value-gamma = %s' % (p['kind'], str(p['sites']), mp.nstr(p['value'] - gam, 5)))
    report.setdefault('gamma', {})[name] = mp.nstr(gam, 40)
    report.setdefault('tight', {})[name] = sorted([[p['kind'], p['sites']] for p in tight])
    report.setdefault('next_level_gap', {})[name] = mp.nstr(sorted([p['value'] for p in critc], reverse=True)[len(tight)] - gam, 6)

print('\n  differences:')
g_xs = mp.mpf(report['gamma']['x* (1e-17 saved)'])
g_60 = mp.mpf(report['gamma']['X60 (1e-60 sym)'])
g_f = mp.mpf(report['gamma']['Xf (17d KKT)'])
print('   gamma(x*) - gamma(X60) = %s' % mp.nstr(g_xs - g_60, 12))
print('   gamma(x*) - LO         = %s' % mp.nstr(g_xs - LO, 12))
print('   gamma(X60) - RD60(lo)  = %s' % mp.nstr(g_60 - RD60, 12))
print('   gamma(Xf) - gamma(X60) = %s' % mp.nstr(g_f - g_60, 12))
report['diffs'] = {'gamma_xs_minus_X60': mp.nstr(g_xs - g_60, 12),
                   'gamma_xs_minus_LO': mp.nstr(g_xs - LO, 12),
                   'gamma_X60_minus_RD60lo': mp.nstr(g_60 - RD60, 12),
                   'gamma_Xf_minus_X60': mp.nstr(g_f - g_60, 12),
                   'LO_minus_RD60lo': mp.nstr(LO - RD60, 12)}

json.dump(report, open(P / 'r20_target_objects.json', 'w'), indent=2)
print('\nwritten r20_target_objects.json')
