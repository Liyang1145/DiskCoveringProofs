"""r20-rigidity: independent audit of the repaired-TC-root geometric assembly.

Read-only input: ../lead/repaired_tc_krawczyk.json (Krawczyk box, 12 unknowns; only the first 7
shape coordinates (a0,a1,a2,a3,y0,y1,R) are used here).

Purpose (audit, not a new proof of the root):
  [A] box definition: the interval box must contain the certified box [c-rad, c+rad] EXACTLY.
      The previous script used float endpoints (CH[i]-/-+RAD), which rounds inward.  Both
      variants are built here and the defect is measured in exact binary64 rationals.
  [B] every positivity claim is decided on the exact interval endpoint (mpf comparison), and a
      conservative rational threshold (floor of the lower endpoint) is reported as well.
  [C] general position of the 11 sites on the whole box:
        - no 3 collinear  (165 cross-product determinants != 0)
        - no 4 cocircular (330 translated circle determinants != 0)
      This is a DIFFERENT instrument from the empty-circle margin; the empty-circle margin alone
      only rules out *empty* cocircular quadruples and therefore CANNOT be used to claim that no
      4 sites are cocircular.
  [D] per-face Delaunay data recomputed from the three sites, cross-checked against the
      structure-predicted circumcentres (U_k, (m,+/-h)), with an independent incircle-determinant
      control of every empty-circle sign.
  [E] completeness of the face list: combinatorial incidence + Euler + hull/strict-orientation
      + angle sums at all 11 sites (interior 2*pi, hull = nonagon interior angle) + area sum vs
      hull area.
No claim is registered here; this is an audit artifact of the r20-rigidity directory.
"""
import json
import mpmath as mp
from pathlib import Path

P = Path(__file__).parent
LEAD = P.parent / 'lead'
mp.mp.dps = 60
mp.iv.dps = 60
ZERO = mp.iv.mpf(0)
PI = mp.iv.pi

cert = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text(encoding='utf-8'))['certificate']
RAD = float.fromhex(cert['radius_hex'])
CH = [float.fromhex(v) for v in cert['center_hex']]
NC = len(CH)
print('certificate: radius = %s = %.17g ; n_center = %d ; contraction = %s'
      % (cert['radius_hex'], RAD, NC, cert['contraction_inf']))

REP = {'radius_hex': cert['radius_hex'], 'center_hex': cert['center_hex'],
       'contraction_inf': cert['contraction_inf']}


def exact(x):
    """exact rational value of a binary64"""
    return mp.mpf(x)


def iv_point(x):
    return mp.iv.mpf(x)


# ---------------------------------------------------------------- [A] boxes
print('\n[A] box definition')
E_LO = [exact(CH[i]) - exact(RAD) for i in range(NC)]
E_HI = [exact(CH[i]) + exact(RAD) for i in range(NC)]
BUG = [mp.iv.mpf([CH[i] - RAD, CH[i] + RAD]) for i in range(NC)]
FIX = [iv_point(CH[i]) + mp.iv.mpf([-RAD, RAD]) for i in range(NC)]
bad_lo = max(float(E_LO[i] - mp.mpf(BUG[i].a)) for i in range(NC))   # >0 => true box excluded
bad_hi = max(float(mp.mpf(BUG[i].b) - E_HI[i]) for i in range(NC))   # >0 => true box excluded
fix_lo = max(float(E_LO[i] - mp.mpf(FIX[i].a)) for i in range(NC))
fix_hi = max(float(mp.mpf(FIX[i].b) - E_HI[i]) for i in range(NC))
wid = max(float(mp.mpf(FIX[i].b) - mp.mpf(FIX[i].a)) for i in range(NC))
print('    float-endpoint defect (max over coordinates):')
print('      exact lo outside buggy box by  <= %.3e   (exact hi) <= %.3e' % (bad_lo, bad_hi))
print('    corrected box iv(c)+iv([-rad,rad]):  exact box outside by %.3e / %.3e ; width <= %.3e'
      % (fix_lo, fix_hi, wid))
REP['box'] = {'float_endpoint_defect_lo': bad_lo, 'float_endpoint_defect_hi': bad_hi,
              'fixed_box_outside_lo': fix_lo, 'fixed_box_outside_hi': fix_hi,
              'fixed_box_max_width': wid,
              'contains_certified_box': bool(fix_lo <= 0 and fix_hi <= 0)}
assert REP['box']['contains_certified_box'], 'corrected box must contain the certified box'


# ------------------------------------------------------- positivity reporting
def pos(name, val, nround=6):
    """positivity decided on the exact interval lower endpoint; conservative threshold reported"""
    lo = mp.mpf(val.a)
    hi = mp.mpf(val.b)
    ok = bool(lo > 0)
    thr = mp.floor(lo * 10 ** nround) / 10 ** nround if ok else None
    REP.setdefault('positivity', {})[name] = {
        'lower_endpoint': mp.nstr(lo, 30), 'upper_endpoint': mp.nstr(hi, 30),
        'pass_lower_gt_0': ok,
        'conservative_threshold': (mp.nstr(thr, 12) if ok else None)}
    return ok


# ------------------------------------------------------------- structure
def structure(X):
    a0, a1, a2, a3, y0, y1, R = X
    a4 = PI - 2 * (a0 + a1 + a2 + a3)
    ak = [a0, a1, a2, a3, a4, a3, a2, a1, a0]
    th = [ZERO] * 9
    for k in range(5, 9):
        th[k] = th[k - 1] + ak[k - 1] + ak[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (ak[k] + ak[k + 1])
    rho = [mp.iv.cos(ak[k]) - mp.iv.sqrt(R * R - mp.iv.sin(ak[k]) ** 2) for k in range(9)]
    C = [(rho[k] * mp.iv.cos(th[k]), rho[k] * mp.iv.sin(th[k])) for k in range(9)]
    B = [(mp.iv.cos(th[k] + ak[k]), mp.iv.sin(th[k] + ak[k])) for k in range(9)]
    U = [(C[k][0] + C[(k + 1) % 9][0] - B[k][0],
          C[k][1] + C[(k + 1) % 9][1] - B[k][1]) for k in range(9)]
    return {'a': ak, 'theta': th, 'rho': rho, 'C': C, 'B': B, 'U': U,
            'y0': y0, 'y1': y1, 'R': R}


S = structure(FIX[:7])
ak, th, rho, C, B, U = S['a'], S['theta'], S['rho'], S['C'], S['B'], S['U']
y0, y1, R = S['y0'], S['y1'], S['R']
d = (y1 - y0) / 2
m = (y0 + y1) / 2
h = mp.iv.sqrt(R * R - d * d)
SITE = C + [(y0, ZERO), (y1, ZERO)]
NAMES = ['C%d' % k for k in range(9)] + ['H0', 'H1']


def sqd(p, q):
    return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2


def sqn(p):
    return p[0] ** 2 + p[1] ** 2


def crossv(o, p, q):
    return (p[0] - o[0]) * (q[1] - o[1]) - (p[1] - o[1]) * (q[0] - o[0])


# ------------------------------------------------- branch legality (corrected box)
print('\n[B] branch legality / structure, corrected box, decisions on exact endpoints')
B1 = {}
B1['min_arc_halfwidth'] = min(ak, key=lambda v: mp.mpf(v.a))
B1['min_R2_minus_sin2'] = min((R * R - mp.iv.sin(x) ** 2 for x in ak), key=lambda v: mp.mpf(v.a))
B1['R2_minus_d2'] = R * R - d * d
B1['min_theta_increment'] = min((ak[k] + ak[(k + 1) % 9] for k in range(9)),
                                key=lambda v: mp.mpf(v.a))
ok = []
ok.append(pos('min_arc_halfwidth_a_k', B1['min_arc_halfwidth']))
ok.append(pos('min_R2_minus_sin2_a_k', B1['min_R2_minus_sin2']))
ok.append(pos('R2_minus_d2', B1['R2_minus_d2']))
ok.append(pos('min_theta_increment', B1['min_theta_increment']))
ok.append(pos('rho_lo', min(rho, key=lambda v: mp.mpf(v.a))))
ok.append(pos('1_minus_rho_hi', 1 - max(rho, key=lambda v: mp.mpf(v.b))))
ok.append(pos('hub_norm_margin', min(1 - R - mp.iv.sqrt(sqn(HUB)) for HUB in SITE[9:])))
ok.append(pos('pin_inside_D', min(1 - sqn(U[k]) for k in range(9))))
REP['branch_all_pass'] = bool(all(ok))
print('    all branch-legality decisions pass on exact endpoints: %s' % REP['branch_all_pass'])

# exact reflection statement (parameter level): palindromic a and theta_{8-k} = -theta_k
ref_th = max(abs(mp.mpf((th[8 - k] + th[k]).a)) + abs(mp.mpf((th[8 - k] + th[k]).b))
             for k in range(9))
REP['reflection_theta_residual'] = float(ref_th)
print('    |theta_{8-k} + theta_k| over box <= %.3e  (exact identity at parameter level)' % ref_th)

# ------------------------------------------------- [C] general position
print('\n[C] general position of the 11 sites over the whole corrected box')


def det3(rows):
    (a11, a12, a13), (a21, a22, a23), (a31, a32, a33) = rows
    return (a11 * (a22 * a33 - a23 * a32) - a12 * (a21 * a33 - a23 * a31)
            + a13 * (a21 * a32 - a22 * a31))


coll_min, coll_arg = None, None
for i in range(11):
    for j in range(i + 1, 11):
        for k in range(j + 1, 11):
            cr = crossv(SITE[i], SITE[j], SITE[k])
            v = min(mp.mpf(cr.a), mp.mpf(cr.b), key=abs)
            if coll_min is None or abs(v) < abs(coll_min):
                coll_min, coll_arg = v, (NAMES[i], NAMES[j], NAMES[k])
pos('min_3point_collinearity_det', mp.iv.mpf([abs(coll_min), abs(coll_min)]))
REP['collinear'] = {'n_triples': 165, 'min_abs_det': mp.nstr(coll_min, 20), 'argmin': coll_arg,
                    'all_nonsingular': bool(abs(coll_min) > 0)}
print('    165 triples: min |cross| = %.6e at %s' % (float(abs(coll_min)), coll_arg))

cir_min, cir_arg, cir_bad = None, None, []
for i in range(11):
    for j in range(i + 1, 11):
        for k in range(j + 1, 11):
            for l in range(k + 1, 11):
                p, q, r, s = SITE[i], SITE[j], SITE[k], SITE[l]
                rows = [[q[0] - p[0], q[1] - p[1], sqn(q) - sqn(p)],
                        [r[0] - p[0], r[1] - p[1], sqn(r) - sqn(p)],
                        [s[0] - p[0], s[1] - p[1], sqn(s) - sqn(p)]]
                D = det3(rows)
                lo, hi = mp.mpf(D.a), mp.mpf(D.b)
                if lo <= 0 <= hi:
                    cir_bad.append((NAMES[i], NAMES[j], NAMES[k], NAMES[l],
                                    mp.nstr(lo, 8), mp.nstr(hi, 8)))
                v = min(lo, hi, key=abs)
                if cir_min is None or abs(v) < abs(cir_min):
                    cir_min, cir_arg = v, (NAMES[i], NAMES[j], NAMES[k], NAMES[l])
REP['cocircular'] = {'n_quadruples': 330, 'min_abs_det': mp.nstr(cir_min, 20), 'argmin': cir_arg,
                     'n_inconclusive': len(cir_bad), 'inconclusive': cir_bad[:20],
                     'no_4_cocircular_on_box': bool(len(cir_bad) == 0 and abs(cir_min) > 0)}
print('    330 quadruples: min |circle det| = %.6e at %s ; inconclusive (0 in interval): %d'
      % (float(abs(cir_min)), cir_arg, len(cir_bad)))
if cir_bad:
    for row in cir_bad[:10]:
        print('       INCONCLUSIVE %s' % (row,))

# -------------------------------------------------------------- [D] faces
print('\n[D] face list: circumcentre from the three sites, empty-circle margins, cross-checks')
FACES = [(1, 2, 10), (2, 3, 9), (3, 4, 9), (4, 5, 9), (5, 6, 9), (6, 7, 10), (8, 0, 10),
         (2, 9, 10), (6, 9, 10), (0, 1, 10), (7, 8, 10)]
HULL = [(k, (k + 1) % 9) for k in range(9)]
ACTIVE_FAN = {(1, 1), (2, 0), (3, 0), (4, 0), (5, 0), (6, 1), (8, 1)}


def circum(p, q, r):
    ax, ay = p[0] - r[0], p[1] - r[1]
    bx, by = q[0] - r[0], q[1] - r[1]
    det = ax * by - ay * bx
    dx = (sqn(p) - sqn(r)) / 2
    dy = (sqn(q) - sqn(r)) / 2
    return (dx * by - ay * dy) / det, (ax * dy - dx * bx) / det, det


rows = []
for f in FACES:
    p, q, r = SITE[f[0]], SITE[f[1]], SITE[f[2]]
    ccx, ccy, det = circum(p, q, r)
    rr2 = sqd((ccx, ccy), p)
    cc = (ccx, ccy)
    empty_lo = min(mp.mpf((sqd(cc, SITE[j]) - rr2).a) for j in range(11) if j not in f)
    inside_lo = mp.mpf((1 - sqn(cc)).a)
    area_lo = mp.mpf(abs(det).a) / 2
    # structure-predicted centre
    rings = sorted(i for i in f if i < 9)
    hub = [i for i in f if i >= 9][0]
    if len(rings) == 2:
        kk = next(i for i in range(9) if set(rings) == {i, (i + 1) % 9})
        pred = U[kk]
        tag = ('fan', kk, hub)
        is_active = (kk, hub - 9) in ACTIVE_FAN
    else:
        kk = rings[0]
        sgn = 1 if mp.mpf(C[kk][1].b) > 0 else -1
        pred = (m, sgn * h)
        tag = ('central', kk, 'both hubs')
        is_active = True
    pred_err = mp.iv.sqrt(sqd(cc, pred))
    # independent incircle control
    orient = (q[0] - p[0]) * (r[1] - p[1]) - (q[1] - p[1]) * (r[0] - p[0])
    osign = 1 if mp.mpf(orient.a) > 0 else -1
    inc_min = None
    for j in range(11):
        if j in f:
            continue
        t = SITE[j]
        inc = det3([[p[0] - t[0], p[1] - t[1], sqn((p[0] - t[0], p[1] - t[1]))],
                    [q[0] - t[0], q[1] - t[1], sqn((q[0] - t[0], q[1] - t[1]))],
                    [r[0] - t[0], r[1] - t[1], sqn((r[0] - t[0], r[1] - t[1]))]])
        v = osign * mp.mpf(inc.b if osign > 0 else inc.a)   # want < 0 => outside
        inc_min = v if inc_min is None or v > inc_min else inc_min
    rows.append({'face': f, 'names': [NAMES[i] for i in f], 'tag': tag, 'active': is_active,
                 'empty_lo': empty_lo, 'inside_lo': inside_lo, 'area_lo': area_lo,
                 'pred_err_hi': mp.mpf(pred_err.b), 'incircle_max': inc_min,
                 'circumradius2_minus_R2': (rr2 - R * R)})
    print('    %-20s %-24s empty>=%+.6e  |cc|<1 by %+.3e  area>=%.3e  |cc-pred|<=%.3e  incircle<=%+.3e'
          % (str(rows[-1]['names']), str(tag), float(empty_lo), float(inside_lo),
             float(area_lo), float(mp.mpf(pred_err.b)), float(inc_min)))

min_empty = min(rw['empty_lo'] for rw in rows)
min_inside = min(rw['inside_lo'] for rw in rows)
min_area = min(rw['area_lo'] for rw in rows)
max_prederr = max(rw['pred_err_hi'] for rw in rows)
max_inc = max(rw['incircle_max'] for rw in rows)
pos('min_empty_circle_margin', mp.iv.mpf([min_empty, min_empty]))
pos('min_inside_D_margin', mp.iv.mpf([min_inside, min_inside]))
pos('min_triangle_area', mp.iv.mpf([min_area, min_area]))
pos('min_incircle_outside_margin', mp.iv.mpf([-max_inc, -max_inc]))
REP['faces'] = [{'names': rw['names'], 'tag': str(rw['tag']), 'active': rw['active'],
                 'empty_margin_lo': mp.nstr(rw['empty_lo'], 20),
                 'inside_D_lo': mp.nstr(rw['inside_lo'], 20),
                 'area_lo': mp.nstr(rw['area_lo'], 20),
                 'cc_minus_predicted_hi': mp.nstr(rw['pred_err_hi'], 20),
                 'incircle_signed_max': mp.nstr(rw['incircle_max'], 20),
                 'circumradius2_minus_R2': [mp.nstr(mp.mpf(rw['circumradius2_minus_R2'].a), 20),
                                            mp.nstr(mp.mpf(rw['circumradius2_minus_R2'].b), 20)]}
                for rw in rows]
REP['min_empty_circle_margin'] = mp.nstr(min_empty, 20)
REP['min_inside_D_margin'] = mp.nstr(min_inside, 20)
REP['min_triangle_area'] = mp.nstr(min_area, 20)
REP['max_cc_minus_predicted'] = mp.nstr(max_prederr, 20)
REP['incircle_control_consistent'] = bool(max_inc < 0)
print('    min empty margin   = %s' % REP['min_empty_circle_margin'])
print('    min inside-D       = %s' % REP['min_inside_D_margin'])
print('    max |cc - predicted| = %s' % REP['max_cc_minus_predicted'])
print('    incircle-determinant control: max signed value = %s (must be < 0)' % mp.nstr(max_inc, 20))

slack = [rw for rw in rows if not rw['active']]
REP['slack'] = [{'names': rw['names'],
                 'circumradius2_minus_R2_hi': mp.nstr(mp.mpf(rw['circumradius2_minus_R2'].b), 20)}
                for rw in slack]
print('    slack faces: %s' % [(rw['names'], mp.nstr(mp.mpf(rw['circumradius2_minus_R2'].b), 12))
                               for rw in slack])
pos('negative of slack max circumradius2-R2',
    mp.iv.mpf([-max(mp.mpf(rw['circumradius2_minus_R2'].b) for rw in slack)] * 2))

# ------------------------------------------------- [E] combinatorial completeness
print('\n[E] combinatorial completeness + angle sums + area sum')
cnt = {}
for f in FACES:
    for e in ((f[0], f[1]), (f[1], f[2]), (f[0], f[2])):
        cnt[tuple(sorted(e))] = cnt.get(tuple(sorted(e)), 0) + 1
hull_ok = all(cnt.get(tuple(sorted(e)), 0) == 1 for e in HULL)
int_edges = [e for e in cnt if e not in [tuple(sorted(e)) for e in HULL]]
int_ok = all(cnt[e] == 2 for e in int_edges)
used = sorted({s for f in FACES for s in f})
V, E, F = 11, len(cnt), len(FACES)
hull_margin = min(mp.mpf(crossv(C[k], C[(k + 1) % 9], SITE[j]).a)
                  for k in range(9) for j in range(11) if j not in (k, (k + 1) % 9))
pos('hull_orientation_margin', mp.iv.mpf([hull_margin, hull_margin]))
REP['combinatorial'] = {'V': V, 'E': E, 'F': F, 'euler': V - E + F, 'hull_edges_once': hull_ok,
                        'interior_edges_twice': int_ok, 'all_sites_used': len(used) == 11,
                        '3F': 3 * F, '2E_minus_h': 2 * E - 9,
                        'hull_orientation_margin': mp.nstr(hull_margin, 20)}
print('    V=%d E=%d F=%d  Euler=%d  hull once=%s  interior twice=%s  sites=%s  3F=%d=2E-h=%d'
      % (V, E, F, V - E + F, hull_ok, int_ok, len(used) == 11, 3 * F, 2 * E - 9))


def angle_at(v, a, b):
    u1 = (a[0] - v[0], a[1] - v[1])
    u2 = (b[0] - v[0], b[1] - v[1])
    cr = abs(u1[0] * u2[1] - u1[1] * u2[0])
    dt = u1[0] * u2[0] + u1[1] * u2[1]
    return mp.iv.atan2(cr, dt)


ang = {i: [] for i in range(11)}
for f in FACES:
    for tri in ((f[0], f[1], f[2]), (f[1], f[2], f[0]), (f[2], f[0], f[1])):
        ang[tri[0]].append(angle_at(SITE[tri[0]], SITE[tri[1]], SITE[tri[2]]))
sums = {i: sum(ang[i], ZERO) for i in range(11)}
for k in range(9):
    hull_ang = angle_at(C[k], C[(k - 1) % 9], C[(k + 1) % 9])
    diff = sums[k] - hull_ang
    REP['angle_sum_%s' % NAMES[k]] = {'sum_minus_hull_angle': [mp.nstr(mp.mpf(diff.a), 20),
                                                                mp.nstr(mp.mpf(diff.b), 20)]}
    print('    angle sum at %-3s minus hull interior angle in [%+.3e, %+.3e]'
          % (NAMES[k], float(mp.mpf(diff.a)), float(mp.mpf(diff.b))))
for k in (9, 10):
    diff = sums[k] - 2 * PI
    REP['angle_sum_%s' % NAMES[k]] = {'sum_minus_2pi': [mp.nstr(mp.mpf(diff.a), 20),
                                                        mp.nstr(mp.mpf(diff.b), 20)]}
    print('    angle sum at %-3s minus 2*pi            in [%+.3e, %+.3e]'
          % (NAMES[k], float(mp.mpf(diff.a)), float(mp.mpf(diff.b))))
ang_ok = (all(mp.mpf((sums[k] - angle_at(C[k], C[(k - 1) % 9], C[(k + 1) % 9])).a) <= 0 <=
              mp.mpf((sums[k] - angle_at(C[k], C[(k - 1) % 9], C[(k + 1) % 9])).b) for k in range(9))
          and all(mp.mpf((sums[k] - 2 * PI).a) <= 0 <= mp.mpf((sums[k] - 2 * PI).b)
                  for k in (9, 10)))
REP['angle_sums_consistent'] = bool(ang_ok)

shoelace = sum(C[k][0] * C[(k + 1) % 9][1] - C[(k + 1) % 9][0] * C[k][1] for k in range(9)) / 2
area_sum = sum(abs(circum(SITE[f[0]], SITE[f[1]], SITE[f[2]])[2]) / 2 for f in FACES)
gap = area_sum - shoelace
REP['area'] = {'sum_faces': mp.nstr(area_sum, 20), 'hull': mp.nstr(shoelace, 20),
               'sum_minus_hull': [mp.nstr(mp.mpf(gap.a), 20), mp.nstr(mp.mpf(gap.b), 20)]}
print('    area: sum(faces) - hull in [%+.3e, %+.3e] (must contain 0)'
      % (float(mp.mpf(gap.a)), float(mp.mpf(gap.b))))
REP['area_sums_consistent'] = bool(mp.mpf(gap.a) <= 0 <= mp.mpf(gap.b))

# boundary arcs
tie = R * R
tie_err = max(max(mp.mpf((sqd(B[k], C[k]) - tie).b), mp.mpf((sqd(B[k], C[(k + 1) % 9]) - tie).b))
              for k in range(9))
sa = sum(ak, ZERO) - PI
REP['tie_identity_err_hi'] = mp.nstr(tie_err, 20)
REP['sum_ak_minus_pi'] = [mp.nstr(mp.mpf(sa.a), 20), mp.nstr(mp.mpf(sa.b), 20)]
print('    |B_k - C_k|^2 - R^2 <= %.3e ; sum a_k - pi in [%+.3e, %+.3e]'
      % (float(tie_err), float(mp.mpf(sa.a)), float(mp.mpf(sa.b))))

# ---------------------------------------------------------------- verdict
REP['audit_verdict'] = {
    'box_ok': REP['box']['contains_certified_box'],
    'branch_ok': REP['branch_all_pass'],
    'no_3_collinear_on_box': REP['collinear']['all_nonsingular'],
    'no_4_cocircular_on_box': REP['cocircular']['no_4_cocircular_on_box'],
    'empty_circle_strict_all_faces': bool(min_empty > 0),
    'all_circumcentres_inside_D': bool(min_inside > 0),
    'combinatorial_triangulation': bool(hull_ok and int_ok and len(used) == 11
                                        and V - E + F == 1 and 3 * F == 2 * E - 9),
    'angle_sums_consistent': REP['angle_sums_consistent'],
    'area_sum_consistent': REP['area_sums_consistent'],
    'incircle_control_consistent': REP['incircle_control_consistent'],
    'what_is_not_claimed': [
        'root existence/uniqueness (read-only Krawczyk certificate of the lead, 12D system)',
        'global lower bound r_D(11) or anything outside the root box',
        'that the empty-circle margin implies no-4-cocircular: the two are separate instruments '
        'and only the 330 circle determinants above address the non-empty cocircular quadruples',
    ]}
json.dump(REP, open(P / 'r20_tc_box_audit.json', 'w'), indent=2)
print('\nverdict: %s' % json.dumps(REP['audit_verdict'], indent=2))
print('written r20_tc_box_audit.json')
