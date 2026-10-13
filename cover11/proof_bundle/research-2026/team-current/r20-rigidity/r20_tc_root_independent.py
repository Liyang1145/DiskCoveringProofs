"""r20-rigidity (independent geometric assembly for the repaired TC root).

Read-only input: 4 = research-2026/team-current/lead/repaired_tc_krawczyk.json (the Krawczyk
box: 12 unknowns = (a0,a1,a2,a3,y0,y1,R) plus 5 multipliers; centre = exact binary64 rationals,
radius = 0x1.12e0be826d695p-30).  The argument does NOT use scipy.spatial.Delaunay: the face
list is assembled from the res5 reflection structure and verified by exact combinatorics plus
interval margins.

Structure (derived from REPAIRED-TC-ROOT-INTERFACE.md and re-derived here):
  a4 = pi - 2(a0+a1+a2+a3);  a = (a0,a1,a2,a3,a4,a3,a2,a1,a0);  sum a = pi exactly.
  theta4 = 0, theta[k+1]-theta[k] = a[k]+a[k+1] (cyclic);  rho[k] = cos a[k] - sqrt(R^2-sin^2 a[k]).
  rings  C_k = rho[k](cos theta_k, sin theta_k),  hubs H0 = (y0,0), H1 = (y1,0).
  ties   B_k = (cos(theta_k+a_k), sin(theta_k+a_k))  (exactly R from C_k and C_{k+1}).
  pins   U_k = C_k + C_{k+1} - B_k  (the other intersection of the two radius-R circles).
  Reflection in the x-axis: C_k <-> C_{8-k}, U_k <-> U_{7-k}, theta_{8-k} = -theta_k.

Face list (11 = 2*11 - 9 - 2), assembled here from the structure, not from a hull algorithm:
  fan, active     : (1,2,H1) (2,3,H0) (3,4,H0) (4,5,H0) (5,6,H0) (6,7,H1) (8,0,H1)
                    (circumcentres U_1,U_2,U_3,U_4,U_5,U_6,U_8; res5 gives |U_k - H| = R)
  central, active : (2,H0,H1) and (6,H0,H1) (circumcentres (m,-h), (m,h), h = sqrt(R^2-d^2))
  slack           : (0,1,H1) and (7,8,H1) (fan triangles not assumed saturated)

Checks performed (interval arithmetic on the whole root box, so they hold for the exact root):
  * branch legality: a_k > 0, R > |sin a_k|, rho_k in (0,1), |d| < R, strict hub norms,
    theta ordering;  reflection relations C_k <-> C_{8-k}, U_k <-> U_{7-k};
  * combinatorial incidence: every site used, each hull edge in exactly 1 face, each interior
    edge in exactly 2, V=11, E=21, F=11, Euler V-E+F=1, sum of degrees = 2E;
  * Delaunay criterion: for every face, the circumcentre cc (computed from the three sites) is
    strictly inside D and every other site has squared distance - circumradius^2 > 0;
  * radius: circumradius^2 <= R^2 for every face (interval), exactly-R identities checked for
    the 9 active faces, strict margin for the 2 slack faces.
"""
import json
from pathlib import Path
import mpmath as mp

P = Path(__file__).parent
LEAD = P.parent / 'lead'
IVDPS = 60
mp.mp.dps = IVDPS
mp.iv.dps = IVDPS

cert = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text(encoding='utf-8'))['certificate']
RAD = float.fromhex(cert['radius_hex'])
CH = [float.fromhex(v) for v in cert['center_hex']]
print('root box radius = %.6e ;  contraction = %s' % (RAD, cert['contraction_inf']))


def box(i):
    """exact binary64 centre + symmetric displacement interval.

    AUDIT FIX 2026-09-25 (lead directive): the first version used float endpoints
    `mp.iv.mpf([CH[i]-RAD, CH[i]+RAD])`; the two float subtractions/ additions round to
    nearest and can move the endpoint INWARD, i.e. the interval then does not contain the
    certified box.  Measured defect <= 2.7e-17 per coordinate (margins are >= 1.1e-3), but the
    whole-box claim requires containment, so build it as iv(c) + iv([-rad,+rad])."""
    return mp.iv.mpf(CH[i]) + mp.iv.mpf([-RAD, RAD])


a0, a1, a2, a3, y0, y1, R = (box(i) for i in range(7))
a4 = mp.iv.pi - 2 * (a0 + a1 + a2 + a3)
ak = [a0, a1, a2, a3, a4, a3, a2, a1, a0]
th = [mp.iv.mpf(0)] * 9
for k in range(5, 9):
    th[k] = th[k - 1] + ak[k - 1] + ak[k]
for k in range(3, -1, -1):
    th[k] = th[k + 1] - (ak[k] + ak[k + 1])
rho = [mp.iv.cos(ak[k]) - mp.iv.sqrt(R * R - mp.iv.sin(ak[k]) ** 2) for k in range(9)]
C = [(rho[k] * mp.iv.cos(th[k]), rho[k] * mp.iv.sin(th[k])) for k in range(9)]
HUB = [(y0, mp.iv.mpf(0)), (y1, mp.iv.mpf(0))]
SITE = C + HUB
NAMES = ['C%d' % k for k in range(9)] + ['H0', 'H1']


def lo(x):
    return float(mp.mpf(x.a))


def hi(x):
    return float(mp.mpf(x.b))


def mid(x):
    return float((mp.mpf(x.a) + mp.mpf(x.b)) / 2)


def sqd(p, q):
    return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2


def sqn(p):
    return p[0] ** 2 + p[1] ** 2


def crossv(o, p, q):
    return (p[0] - o[0]) * (q[1] - o[1]) - (p[1] - o[1]) * (q[0] - o[0])


REP = {}

# ---------------- branch legality ------------------------------------------
print('\n[1] branch legality and symmetry (interval, whole root box)')
REP['min_arc_halfwidth'] = min(lo(x) for x in ak)
REP['min_R2_minus_sin2'] = min(lo(R * R - mp.iv.sin(x) ** 2) for x in ak)
REP['rho_range'] = [min(lo(x) for x in rho), max(hi(x) for x in rho)]
d = (y1 - y0) / 2
m = (y0 + y1) / 2
h = mp.iv.sqrt(R * R - d * d)
REP['R2_minus_d2'] = lo(R * R - d * d)
REP['hub_norm_margin'] = min(lo((1 - R) ** 2 - sqn(HUB[i])) for i in range(2))
REP['min_theta_increment'] = min(lo(ak[k] + ak[(k + 1) % 9]) for k in range(9))
print('    min arc half-width a_k           = %.6e   (>0 required)' % REP['min_arc_halfwidth'])
print('    min (R^2 - sin^2 a_k)            = %.6e   (>0 required, sqrt branch)' % REP['min_R2_minus_sin2'])
print('    rho_k range                      = [%.6f, %.6f]  (need 0<rho<1: disks in D)' % tuple(REP['rho_range']))
print('    R^2 - d^2                        = %.6e   (>0 required, central h)' % REP['R2_minus_d2'])
print('    hub strictness (1-R)^2 - |H|^2   = %.6e   (>0 required)' % REP['hub_norm_margin'])
print('    min theta increment a_k+a_{k+1}  = %.6e   (>0 required, cyclic order)' % REP['min_theta_increment'])
# reflection relations
refl_err = max(hi(abs(C[k][0] - C[8 - k][0])) for k in range(9))
refl_err = max(refl_err, max(hi(abs(C[k][1] + C[8 - k][1])) for k in range(9)))
REP['reflection_err_C'] = refl_err
print('    reflection  |C_k - mirror(C_{8-k})|_inf = %.3e (x even, y odd)' % refl_err)
B = [(mp.iv.cos(th[k] + ak[k]), mp.iv.sin(th[k] + ak[k])) for k in range(9)]
U = [(C[k][0] + C[(k + 1) % 9][0] - B[k][0], C[k][1] + C[(k + 1) % 9][1] - B[k][1]) for k in range(9)]
REP['U_reflection_err'] = max(hi(abs(U[k][0] - U[(7 - k) % 9][0])) for k in range(9))
REP['U_reflection_err'] = max(REP['U_reflection_err'],
                             max(hi(abs(U[k][1] + U[(7 - k) % 9][1])) for k in range(9)))
print('    reflection  U_k <-> U_{7-k}      = %.3e' % REP['U_reflection_err'])
# pin identities (exact by construction)
pin_err = max(hi(abs(sqd(U[k], C[k]) - R * R)) for k in range(9))
pin_err = max(pin_err, max(hi(abs(sqd(U[k], C[(k + 1) % 9]) - R * R)) for k in range(9)))
REP['pin_distance_identity_err'] = pin_err
print('    pin identity |U_k-C_k|^2 - R^2   <= %.3e (exact construction, |U_k-C_{k+1}| too)' % pin_err)
REP['U_inside_margin'] = min(lo(1 - sqn(U[k])) for k in range(9))
print('    pins strictly inside D           = %.6e  (>0 required)' % REP['U_inside_margin'])

# ---------------- combinatorial incidence ---------------------------------
print('\n[2] combinatorial incidence of the structure-assembled face list (no hull algorithm)')
FACES = [(1, 2, 10), (2, 3, 9), (3, 4, 9), (4, 5, 9), (5, 6, 9), (6, 7, 10), (8, 0, 10),
         (2, 9, 10), (6, 9, 10), (0, 1, 10), (7, 8, 10)]
HULL = [(k, (k + 1) % 9) for k in range(9)]
cnt = {}
for f in FACES:
    for e in ((f[0], f[1]), (f[1], f[2]), (f[0], f[2])):
        e = tuple(sorted(e))
        cnt[e] = cnt.get(e, 0) + 1
hull_ok = all(cnt.get(tuple(sorted(e)), 0) == 1 for e in HULL)
int_edges = [e for e in cnt if e not in [tuple(sorted(e)) for e in HULL]]
int_ok = all(cnt[e] == 2 for e in int_edges)
used = sorted({s for f in FACES for s in f})
V, E, F = 11, len(cnt), len(FACES)
REP.update({'V': V, 'E': E, 'F': F, 'euler_VmEmF': V - E + F, 'hull_edges_once': hull_ok,
            'interior_edges_twice': int_ok, 'all_sites_used': len(used) == 11,
            'sum_face_degrees': sum(3 for _ in FACES), 'sum_site_degrees': sum(cnt[e] for e in cnt)})
print('    V=%d  E=%d  F=%d   V-E+F = %d  (disk triangulation: 1)' % (V, E, F, V - E + F))
print('    hull edges (ring k,k+1) each in exactly 1 face: %s' % hull_ok)
print('    interior edges each in exactly 2 faces         : %s  (%d interior edges)' % (int_ok, len(int_edges)))
print('    all 11 sites used: %s ; sum of face degrees = 3F = %d = 2E - h = %d'
      % (len(used) == 11, 3 * F, 2 * E - 9))
assert hull_ok and int_ok and len(used) == 11 and V - E + F == 1 and 3 * F == 2 * E - 9

# hull orientation + hub interiority (cross products via interval, but endpoints: the ring
# nonagon must be strictly convex and contain both hubs strictly)
hull_margin = 1e9
hull_margin_exact = None
for k in range(9):
    for j in range(11):
        if j in (k, (k + 1) % 9):
            continue
        hull_margin = min(hull_margin, lo(crossv(C[k], C[(k + 1) % 9], SITE[j])))
        e = mp.mpf(crossv(C[k], C[(k + 1) % 9], SITE[j]).a)
        hull_margin_exact = e if hull_margin_exact is None or e < hull_margin_exact else hull_margin_exact
REP['hull_orientation_margin'] = hull_margin
REP['hull_orientation_margin_exact'] = mp.nstr(hull_margin_exact, 20)
print('    strict hull orientation margin (all other sites left of each hull edge) = %.6e' % hull_margin)
assert hull_margin_exact > 0, 'hull orientation must be strictly positive on the exact endpoints'

# ---------------- per-face circumcentre / radius / empty circle -------------
print('\n[3] Delaunay criterion per face (circumcentre from the three sites, interval)')


def circum(p, q, r):
    """circumcentre and squared circumradius of a nondegenerate triangle (interval arithmetic)"""
    ax, ay = p[0] - r[0], p[1] - r[1]
    bx, by = q[0] - r[0], q[1] - r[1]
    det = ax * by - ay * bx
    dx = (sqn(p) - sqn(r)) / 2
    dy = (sqn(q) - sqn(r)) / 2
    cxx = (dx * by - ay * dy) / det
    cyy = (ax * dy - dx * bx) / det
    # x solves (p-r).x = (|p|^2-|r|^2)/2 and (q-r).x = (|q|^2-|r|^2)/2, i.e. x IS the
    # circumcentre (do NOT add r again -- implementation bug fixed 2026-09-25)
    cc = (cxx, cyy)
    return cc, sqd(cc, p), det


rows = []
ACTIVE_FAN = {(1, 1), (2, 0), (3, 0), (4, 0), (5, 0), (6, 1), (8, 1)}
for f in FACES:
    cc, rr2, det = circum(SITE[f[0]], SITE[f[1]], SITE[f[2]])
    empty = min(lo(sqd(cc, SITE[j]) - rr2) for j in range(11) if j not in f)
    insideD = 1 - hi(sqn(cc))
    tri_area_margin = lo(abs(det)) / 2
    rows.append((f, cc, rr2, empty, insideD, tri_area_margin))
    kinds = [NAMES[i] for i in f]
    print('    %-16s  empty margin %+.4e   |cc|<1 by %.3e   area margin %.3e'
          % (str(kinds), empty, insideD, tri_area_margin))
REP['min_empty_margin'] = min(r[3] for r in rows)
REP['min_inside_D_margin'] = min(r[4] for r in rows)
REP['min_triangle_area_margin'] = min(r[5] for r in rows)
# exact-endpoint decisions (normative): the printed floats above are summary readings only
empty_exact = min(mp.mpf((sqd(r[1], SITE[j]) - r[2]).a) for r in rows
                  for j in range(11) if j not in r[0])
inside_exact = min(mp.mpf((1 - sqn(r[1])).a) for r in rows)
REP['min_empty_margin_exact'] = mp.nstr(empty_exact, 20)
REP['min_inside_D_margin_exact'] = mp.nstr(inside_exact, 20)
REP['min_empty_margin_conservative_threshold'] = mp.nstr(mp.floor(empty_exact * 100) / 100, 8)
REP['min_inside_D_margin_conservative_threshold'] = mp.nstr(mp.floor(inside_exact * 100) / 100, 8)
print('    min empty-circle margin = %.6e  (>0 => strict Delaunay criterion)' % REP['min_empty_margin'])
print('    min (1-|cc|)            = %.6e  (>0 => every Voronoi vertex inside D)' % REP['min_inside_D_margin'])
print('    exact endpoints: empty >= %s (conservative >= %s) ; 1-|cc| >= %s (conservative >= %s)'
      % (REP['min_empty_margin_exact'], REP['min_empty_margin_conservative_threshold'],
         REP['min_inside_D_margin_exact'], REP['min_inside_D_margin_conservative_threshold']))
print('    NOTE: strict empty circles rule out EMPTY cocircular quadruples only; they say nothing')
print('          about cocircular quadruples in general (see r20_tc_box_audit.py / the audit note).')
assert empty_exact > 0 and inside_exact > 0, 'exact-endpoint positivity failed'

# ---------------- radius identities: active = R, slack < R ----------------
print('\n[4] circumradius vs R (active identities from the root system, slack strict)')
act_rows, sl_rows = [], []
for f, cc, rr2, empty, insideD, _ in rows:
    rings = sorted(i for i in f if i < 9)
    if len(rings) == 2:
        k = next(i for i in range(9) if set(rings) == {i, (i + 1) % 9})
        hub = [i for i in f if i >= 9][0]
        tag = ('fan', k, hub)
        is_active = (k, hub - 9) in ACTIVE_FAN
        if is_active:
            # the circumcentre identity is the pin: check |U_k - H_hub| - R  (root equation)
            res = sqd(U[k], HUB[hub - 9]) - R * R
            # cross-check: the circumcentre recomputed from the three sites must coincide with U_k
            distance_cc_pin = mp.iv.sqrt(sqd(cc, U[k]))
            act_rows.append((tag, [lo(res), hi(res)], ('cc-pin', lo(distance_cc_pin), hi(distance_cc_pin))))
        else:
            sl_rows.append((tag, [lo(rr2 - R * R), hi(rr2 - R * R)], [lo(rr2), hi(R * R)]))
    else:
        tag = ('central', rings[0], 'both hubs')
        cc_id = (m, h if mid(C[rings[0]][1]) > 0 else -h)
        res = sqd(cc_id, C[rings[0]]) - R * R
        hubiv = [sqd(cc_id, HUB[i]) - R * R for i in range(2)]
        assert all(lo(x) <= 0 <= hi(x) for x in hubiv), [lo(x) for x in hubiv]
        act_rows.append((tag, [lo(res), hi(res)], ('hub-identity', [lo(x) for x in hubiv], [hi(x) for x in hubiv])))
n_contain = 0
for tag, res, extra in act_rows:
    contains = res[0] <= 0 <= res[1]
    n_contain += contains
    print('    ACTIVE  %-26s  residual(|pin-H|^2 - R^2) in [%+.3e, %+.3e]  contains 0: %s  %s'
          % (str(tag), res[0], res[1], contains, extra))
assert n_contain == 9
for tag, sl, rr in sl_rows:
    print('    SLACK   %-26s  circumradius^2 - R^2 in [%+.3e, %+.3e]  (strictly <0)' % (str(tag), sl[0], sl[1]))
REP['n_active'] = len(act_rows)
REP['n_slack'] = len(sl_rows)
REP['slack_max_circumradius2_minus_R2'] = max(x[1][1] for x in sl_rows)
print('    active faces: %d, slack faces: %d (slack upper bound %.3e < 0)'
      % (REP['n_active'], REP['n_slack'], REP['slack_max_circumradius2_minus_R2']))
assert REP['n_active'] == 9 and REP['n_slack'] == 2 and REP['slack_max_circumradius2_minus_R2'] < 0

# ---------------- boundary ties tile the circle ----------------------------
print('\n[5] boundary: ties exactly R from their ring pair, arcs tile the circle')
tie_err = max(hi(abs(sqd(B[k], C[k]) - R * R)) for k in range(9))
tie_err = max(tie_err, max(hi(abs(sqd(B[k], C[(k + 1) % 9]) - R * R)) for k in range(9)))
REP['tie_identity_err'] = tie_err
REP['sum_arc_halfwidths_minus_pi'] = [lo(sum(ak, mp.iv.mpf(0)) - mp.iv.pi), hi(sum(ak, mp.iv.mpf(0)) - mp.iv.pi)]
print('    tie identity |B_k - C_k|^2 - R^2 <= %.3e  (exact construction)' % tie_err)
print('    sum a_k - pi in [%+.3e, %+.3e]  (exact tiling of the boundary)' % tuple(REP['sum_arc_halfwidths_minus_pi']))

json.dump(REP, open(P / 'r20_tc_root_independent.json', 'w'), indent=2)
print('\nwritten r20_tc_root_independent.json')
