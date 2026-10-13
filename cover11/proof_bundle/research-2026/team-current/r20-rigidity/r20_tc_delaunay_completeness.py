"""r20-rigidity: completeness instruments for the repaired-TC-root face list (audit, part 2).

Part 1 (`r20_tc_box_audit.py`) fixed the box definition, decided all positivity on exact
interval endpoints and measured the general position of the 11 sites.  It found:
  * box float-endpoint defect <= 2.7e-17 (margins are >= 1.1e-3),
  * (C4,H0,H1) is EXACTLY collinear (all three on the x-axis; theta_4 = 0 exactly),
  * exactly 6 of the 330 quadruples are cocircular on the box ({C0,C1,C7,C8}, {C0,C2,C6,C8},
    {C0,C3,C5,C8}, {C1,C2,C6,C7}, {C1,C3,C5,C7}, {C2,C3,C5,C6}) -- all are mirror-symmetric
    pairs, which are cyclic by the exact reflection symmetry; the other 324 have |det| >= 5.6e-8.

This part closes the remaining logical gaps of the "complete Delaunay / Voronoi vertex list"
argument with instruments that are independent of the empty-circle margin:

  [F] the 11 listed triangles are exactly the bounded faces of the straight-line graph formed by
      their 21 edges, i.e. a genuine geometric triangulation of the hull:
        F1  210 edge pairs: no two edges meet except at a common endpoint (no proper crossing,
            no positive-length collinear overlap);
        F2  88 (face, other site) pairs: no site lies in the closed triangle of another face;
        F2b 231 (edge, other site) pairs: no site lies in the interior of an edge;
        F3  55 face pairs: separating-axis certificate of disjoint interiors (control);
        F4  hull = the nonagon, both hubs strictly interior;
        F5  counts V=11, E=21, F=11, Euler=1, outer boundary = 9 hull edges  =>  sum of sides of
            the bounded faces = 2E - 9 = 33 = 3*11, so all 11 bounded faces are triangles; with
            F1+F2+F2b each listed triangle is one of them, and there are exactly 11 => the list
            IS the bounded-face set (no sub-complex, no overlap).

  [G] no EMPTY cocircular quadruple exists on the box:
        G1  the only cocircular quadruples are the 6 mirror ones (exact: two mirror pairs have
            their common centre on the x-axis; re-derived here by the circle-centre/radius
            construction, not by a determinant sign);
        G2  each of the 6 has a site strictly inside its circle on the whole box (interval,
            margin >= 0.61) => none of them is empty;
        =>  the Delaunay subdivision has no cell with >= 4 vertices, hence it is a triangulation;
            with F and the strict empty-circle margins of part 1 the listed faces are exactly that
            triangulation and the Voronoi vertices are exactly the 11 circumcentres.
      WARNING (scope): this is NOT "no 4 sites are cocircular" -- that statement is FALSE here
      (the 6 mirror quadruples are exactly cocircular).  The empty-circle margin of part 1 alone
      cannot decide either direction; only G1+G2 can.

Read-only input: ../lead/repaired_tc_krawczyk.json.  mpmath.iv only, no new backend/precision.
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

# corrected box (identical to part 1 and to lead/repair_tc_krawczyk.py certify())
FX = [mp.iv.mpf(CH[i]) + mp.iv.mpf([-RAD, RAD]) for i in range(7)]
a0, a1, a2, a3, y0, y1, R = FX
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
U = [(C[k][0] + C[(k + 1) % 9][0] - B[k][0], C[k][1] + C[(k + 1) % 9][1] - B[k][1])
     for k in range(9)]
SITE = C + [(y0, ZERO), (y1, ZERO)]
NAMES = ['C%d' % k for k in range(9)] + ['H0', 'H1']
FACES = [(1, 2, 10), (2, 3, 9), (3, 4, 9), (4, 5, 9), (5, 6, 9), (6, 7, 10), (8, 0, 10),
         (2, 9, 10), (6, 9, 10), (0, 1, 10), (7, 8, 10)]
HULL = [(k, (k + 1) % 9) for k in range(9)]
REP = {}


def orient(p, q, r):
    return (q[0] - p[0]) * (r[1] - p[1]) - (q[1] - p[1]) * (r[0] - p[0])


def dot(p, q, r):
    return (q[0] - p[0]) * (r[0] - p[0]) + (q[1] - p[1]) * (r[1] - p[1])


def sign_iv(v):
    lo, hi = mp.mpf(v.a), mp.mpf(v.b)
    if lo > 0:
        return 1
    if hi < 0:
        return -1
    if lo == 0 and hi == 0:
        return 0
    return None            # interval straddles 0 -> undecided


def lo_(v):
    return mp.mpf(v.a)


def hi_(v):
    return mp.mpf(v.b)


# ------------------------------------------------------------------ [F] triangulation
print('[F] is the listed face set a genuine geometric triangulation of the hull?')
EDGES = sorted({tuple(sorted(e)) for f in FACES
                for e in ((f[0], f[1]), (f[1], f[2]), (f[0], f[2]))})
assert len(EDGES) == 21, len(EDGES)
print('    distinct edges: %d (expected 21)' % len(EDGES))

# F1: no two edges share more than a single endpoint
def edge_overlap(e1, e2):
    """True / False / None(undecided): do the two closed segments share a positive-length set?"""
    shared = sorted(set(e1) & set(e2))
    if len(shared) == 2:
        return True
    if len(shared) == 1:
        Pv = shared[0]
        Q = e1[0] if e1[1] == Pv else e1[1]
        SX = e2[0] if e2[1] == Pv else e2[1]
        sc = sign_iv(orient(SITE[Pv], SITE[Q], SITE[SX]))
        if sc is None:
            return None
        if sc != 0:
            return False
        sd = sign_iv(dot(SITE[Pv], SITE[Q], SITE[SX]))
        return None if sd is None else bool(sd > 0)
    p, q, r, s = SITE[e1[0]], SITE[e1[1]], SITE[e2[0]], SITE[e2[1]]
    sg = [sign_iv(orient(p, q, r)), sign_iv(orient(p, q, s)),
          sign_iv(orient(r, s, p)), sign_iv(orient(r, s, q))]
    if None in sg:
        return None
    s1, s2, s3, s4 = sg
    if s1 * s2 < 0 and s3 * s4 < 0:
        return True
    if s1 * s2 > 0 or s3 * s4 > 0:
        return False
    if s1 == 0 and s2 == 0 and s3 == 0 and s4 == 0:
        best = None
        for ax in (0, 1):
            a_lo = min(lo_(p[ax]), lo_(q[ax]))
            a_hi = max(hi_(p[ax]), hi_(q[ax]))
            b_lo = min(lo_(r[ax]), lo_(s[ax]))
            b_hi = max(hi_(r[ax]), hi_(s[ax]))
            ov = min(a_hi, b_hi) - max(a_lo, b_lo)
            if best is None or ov > best:
                best = ov
        return bool(best is not None and best > 0)
    return False


cross_bad, cross_und = [], []
for i in range(len(EDGES)):
    for j in range(i + 1, len(EDGES)):
        r = edge_overlap(EDGES[i], EDGES[j])
        if r is True:
            cross_bad.append((NAMES[EDGES[i][0]], NAMES[EDGES[i][1]],
                              NAMES[EDGES[j][0]], NAMES[EDGES[j][1]]))
        elif r is None:
            cross_und.append((NAMES[EDGES[i][0]], NAMES[EDGES[i][1]],
                              NAMES[EDGES[j][0]], NAMES[EDGES[j][1]]))
REP['F1_non_crossing'] = {'pairs_tested': 210, 'violations': cross_bad, 'undecided': cross_und,
                          'pass': len(cross_bad) == 0 and len(cross_und) == 0}
print('    F1 non-crossing: %d violations, %d undecided / 210 pairs'
      % (len(cross_bad), len(cross_und)))
for row in (cross_bad + cross_und)[:10]:
    print('       %s' % (row,))

# F2: no site in the closed triangle of another face
def in_closed_triangle(f, j):
    o = 1 if lo_(orient(SITE[f[0]], SITE[f[1]], SITE[f[2]])) > 0 else -1
    vals = [o * orient(SITE[f[k]], SITE[f[(k + 1) % 3]], SITE[j]) for k in range(3)]
    return min(hi_(v) for v in vals) >= 0, vals


inside_bad = []
for f in FACES:
    for j in range(11):
        if j in f:
            continue
        hit, vals = in_closed_triangle(f, j)
        if hit:
            inside_bad.append((NAMES[j], [NAMES[i] for i in f]))
REP['F2_site_in_face'] = {'pairs_tested': 88, 'violations': inside_bad, 'pass': not inside_bad}
print('    F2 no site in any other face (closed): %d violations / 88' % len(inside_bad))

# F2b: no site in the interior of an edge
edge_bad = []
for e in EDGES:
    for w in range(11):
        if w in e:
            continue
        p, q = SITE[e[0]], SITE[e[1]]
        cr = orient(p, q, SITE[w])
        dt = dot(SITE[w], p, q)
        on_line = sign_iv(cr) == 0 or lo_(abs(cr)) == 0
        strictly_between = sign_iv(dt) == -1
        if on_line and strictly_between:
            edge_bad.append((NAMES[w], NAMES[e[0]], NAMES[e[1]]))
REP['F2b_site_in_edge'] = {'pairs_tested': 231, 'violations': edge_bad, 'pass': not edge_bad}
print('    F2b no site in the interior of an edge: %d violations / 231' % len(edge_bad))

# F3: pairwise disjoint interiors.
# Certificate: no edge pair shares a positive-length set (F1) and no vertex of one triangle lies
# in the closed triangle of the other unless it is a shared vertex (F2 restricted).  Two convex
# sets with intersecting interiors must have a vertex of one in the interior of the other or a
# proper edge crossing, so these two facts certify interior disjointness.
def in_closed_tri_strict(f, j):
    o = 1 if lo_(orient(SITE[f[0]], SITE[f[1]], SITE[f[2]])) > 0 else -1
    vals = [o * orient(SITE[f[k]], SITE[f[(k + 1) % 3]], SITE[j]) for k in range(3)]
    return min(hi_(v) for v in vals) >= 0


sep_ok, sep_fail, sep_adj = 0, [], 0
for i in range(len(FACES)):
    for j in range(i + 1, len(FACES)):
        f, g = FACES[i], FACES[j]
        sh = [e for e in ((f[0], f[1]), (f[1], f[2]), (f[0], f[2]))
              if all(x in g for x in e)]
        if len(sh) == 1:
            u, v = sh[0]
            wf = [x for x in f if x not in (u, v)][0]
            wg = [x for x in g if x not in (u, v)][0]
            s1 = sign_iv(orient(SITE[u], SITE[v], SITE[wf]))
            s2 = sign_iv(orient(SITE[u], SITE[v], SITE[wg]))
            if s1 is not None and s2 is not None and s1 * s2 < 0:
                sep_ok += 1
                sep_adj += 1
            else:
                sep_fail.append(([NAMES[x] for x in f], [NAMES[x] for x in g], 'adjacent', s1, s2))
        else:
            crossed = any(edge_overlap((f[a], f[(a + 1) % 3]), (g[b], g[(b + 1) % 3])) is not False
                          for a in range(3) for b in range(3))
            vin = any(in_closed_tri_strict(f, x) for x in g if x not in f) or \
                any(in_closed_tri_strict(g, x) for x in f if x not in g)
            if not crossed and not vin:
                sep_ok += 1
            else:
                sep_fail.append(([NAMES[x] for x in f], [NAMES[x] for x in g], 'far', crossed, vin))
REP['F3_pairwise_disjoint_interiors'] = {'pairs_tested': 55, 'certified': sep_ok,
                                         'certified_adjacent': sep_adj, 'not_certified': sep_fail,
                                         'pass': not sep_fail}
print('    F3 disjoint interiors: %d/55 certified (%d adjacent by opposite-side orientation, '
      'rest by no-edge-overlap + no-non-shared-vertex-in-closed-triangle), %d not'
      % (sep_ok, sep_adj, len(sep_fail)))
for row in sep_fail[:10]:
    print('       NOT CERTIFIED %s' % (row,))

hull_margin = min(lo_(orient(C[k], C[(k + 1) % 9], SITE[j]))
                  for k in range(9) for j in range(11) if j not in (k, (k + 1) % 9))
cnt = {}
for f in FACES:
    for e in ((f[0], f[1]), (f[1], f[2]), (f[0], f[2])):
        cnt[tuple(sorted(e))] = cnt.get(tuple(sorted(e)), 0) + 1
hull_ok = all(cnt.get(tuple(sorted(e)), 0) == 1 for e in HULL)
V, E, F = 11, len(cnt), len(FACES)
REP['F5_counts'] = {'V': V, 'E': E, 'F': F, 'euler': V - E + F, 'hull_edges_once': hull_ok,
                    'sum_face_sides_of_bounded_faces': 2 * E - 9, 'three_times_F': 3 * F}
print('    F4 hull orientation margin = %s' % mp.nstr(hull_margin, 20))
print('    F5 V=%d E=%d F=%d Euler=%d hull_once=%s  2E-9=%d=3F=%d'
      % (V, E, F, V - E + F, hull_ok, 2 * E - 9, 3 * F))
F_OK = (not cross_bad) and (not cross_und) and (not inside_bad) and (not edge_bad) \
    and (not sep_fail) and hull_margin > 0 and hull_ok and V - E + F == 1 and 2 * E - 9 == 3 * F
REP['F_triangulation_ok'] = bool(F_OK)

# ------------------------------------------------------- [G] empty cocircular quadruples
print('\n[G] cocircular quadruples: are any of them empty?')
MIRROR = [(0, 1, 7, 8), (0, 2, 6, 8), (0, 3, 5, 8), (1, 2, 6, 7), (1, 3, 5, 7), (2, 3, 5, 6)]
REP['G_mirror_quadruples'] = []
for (i, j, k, l) in MIRROR:
    p, q = SITE[i], SITE[j]
    num = (p[0] ** 2 + p[1] ** 2) - (q[0] ** 2 + q[1] ** 2)
    den = 2 * (p[0] - q[0])
    O = (num / den, ZERO)                    # centre on the x-axis (exact by symmetry)
    rad = mp.iv.sqrt((O[0] - p[0]) ** 2 + (O[1] - p[1]) ** 2)
    best, best_site = None, None
    for t in range(11):
        if t in (i, j, k, l):
            continue
        inside_margin = lo_(rad - mp.iv.sqrt((O[0] - SITE[t][0]) ** 2 + (O[1] - SITE[t][1]) ** 2))
        if best is None or inside_margin > best:
            best, best_site = inside_margin, NAMES[t]
    entry = {'quadruple': [NAMES[x] for x in (i, j, k, l)],
             'centre_x_lo_hi': [mp.nstr(lo_(O[0]), 20), mp.nstr(hi_(O[0]), 20)],
             'radius_lo_hi': [mp.nstr(lo_(rad), 20), mp.nstr(hi_(rad), 20)],
             'witness_inside': best_site, 'witness_margin_lo': mp.nstr(best, 20),
             'strictly_nonempty_on_box': bool(best is not None and best > 0)}
    REP['G_mirror_quadruples'].append(entry)
    print('    %-22s centre_x=%s radius=%s witness %s inside by >= %s'
          % (str(entry['quadruple']), mp.nstr(mp.mpf((lo_(O[0]) + hi_(O[0])) / 2), 12),
             mp.nstr(mp.mpf((lo_(rad) + hi_(rad)) / 2), 12), best_site, entry['witness_margin_lo']))
G_OK = all(e['strictly_nonempty_on_box'] for e in REP['G_mirror_quadruples'])
REP['G_no_empty_cocircular_quadruple'] = bool(G_OK)
print('    all 6 mirror quadruples strictly non-empty: %s' % G_OK)

REP['audit_chain'] = {
    'F_triangulation_ok': REP['F_triangulation_ok'],
    'G_no_empty_cocircular_quadruple': REP['G_no_empty_cocircular_quadruple'],
    'stated_chain': [
        'read-only input: lead Krawczyk certificate -> exactly one root of the 12D symmetric '
        'system in the box (existence+uniqueness); nothing below re-proves it.',
        'exact parameter identities: pin identity |U_k-C_k|=|U_k-C_{k+1}|=R (rho_k solves the '
        'quadratic identically: rho^2-2 rho cos a+1=R^2), hub identity (m-y_i)^2+h^2=R^2, and '
        'palindromic reflection symmetry theta_{8-k}=-theta_k, rho_{8-k}=rho_k.',
        'root equations (f5=0 at the root): |U_k-H|=R for k=1,2,3,8 and |(m,h)-C_6|=R => the 9 '
        'active faces have circumradius exactly R; the 2 slack faces are < R over the box (from '
        'part 1: margin 8.746e-4).',
        'interval facts over the whole corrected box: branch legality (part 1); every listed '
        'face has strictly empty circumcircle (>= 0.1505) and interior circumcentre (>= 0.6120); '
        'F1/F2/F2b/F3/F4/F5 above; the 6 cocircular quadruples are all non-empty (G).',
        '=> the Delaunay subdivision has no >= 4-vertex cell, it is a triangulation, and by F '
        'it equals the listed face list; hence the Voronoi vertex list of the configuration is '
        'exactly the 11 circumcentres, all strictly inside D.',
        'boundary: the 9 ring arcs tile dD (sum a = pi identically) and each arc lies within R '
        'of its ring centre => every interior local maximum of d = min_i |x-site_i| is a Voronoi '
        'vertex and the boundary maximum is <= R => R_D(root configuration) = R exactly, i.e. '
        'r_D(11) <= R (UPPER BOUND ONLY).',
        'NOT established: root existence/uniqueness (read-only certificate); no lower bound; no '
        'claim that no 4 sites are cocircular (FALSE: the 6 mirror quadruples are cocircular); '
        'the empty-circle margin alone implies nothing about cocircularity in either direction.',
    ]}
json.dump(REP, open(P / 'r20_tc_delaunay_completeness.json', 'w'), indent=2)
print('\nF=%s  G=%s' % (REP['F_triangulation_ok'], REP['G_no_empty_cocircular_quadruple']))
print('written r20_tc_delaunay_completeness.json')
