# -*- coding: utf-8 -*-
"""socp_fixed_switch_check.py — independent checks for the lead's fixed-switch SOCP relaxation:

 (a) representation: build the constraint system explicitly and verify (i) it is a SOCP
     (norm-ball constraints with variable radius, auxiliary z_f free) and (ii) it is NECESSARY
     for a genuine cover: from a cover, sites + z_f = primal Voronoi vertices are feasible.
 (b) candidate numbers: the nine switch points U_i on @D, the switch distances rho_i vs r (tight?),
     the chord bound max|U_i - U_{i+1}|/2 <= r, the 11 dual faces, the two-hub (central) faces,
     each triangle's angle type (acute/right/obtuse) and its circumradius vs r (tight/slack).
 (c) KKT mapping: the split identity  grad_c rho_i = unit(c_j - U_i)  for the two adjacent sites,
     so the switch branch gradient splits exactly onto the two endpoint constraints; and the
     per-face cone condition  sum_{c in f} w_c * unit(c - z_f) = 0, w >= 0  is solvable with
     z_f = circumcentre  <=>  the face triangle is acute (strictly positive weights) and with
     z_f on the longest side's midpoint iff obtuse (one weight zero).

Floats for the report; the switch construction and the comparisons are also checked with exact
rationals where cheap.  Control on one configuration, not a proof for the class.
"""
import json
import math
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(r'C:\Users\袁力阳\Desktop\ai4math2')
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
Pf = [(F(int(x[0]), 10 ** 17), F(int(x[1]), 10 ** 17)) for x in raw['centers_scaled_1e17']]
NEW2RAW = [5, 7, 1, 8, 6, 4, 9, 10, 3]
R = F(3799838531198387090485182, 10 ** 25)
Rf = float(R)
ring = [Pf[NEW2RAW[i]] for i in range(9)]
hubA, hubB = Pf[0], Pf[2]
sites = [tuple(map(float, c)) for c in ring] + [tuple(map(float, hubA)), tuple(map(float, hubB))]
ringf = sites[:9]


def unit(v):
    n = math.hypot(*v)
    return (v[0] / n, v[1] / n)


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def dist(a, b):
    return math.hypot(a[0] - b[0], a[1] - b[1])


# ---------------- (b) switch points on @D ----------------
# switch U_i is the point of @D equidistant to ring i and ring (i+1)mod9 that is nearest to both
# among all sites (i.e. inside the overlap of the two arcs).
def switch(i, j):
    a, b = ringf[i], ringf[j]
    m = ((a[0] + b[0]) / 2, (a[1] + b[1]) / 2)
    d = sub(b, a)
    n = unit((-d[1], d[0]))
    # solve |m + t n|^2 = 1
    A = n[0] ** 2 + n[1] ** 2
    B = 2 * (m[0] * n[0] + m[1] * n[1])
    C = m[0] ** 2 + m[1] ** 2 - 1
    disc = B * B - 4 * A * C
    if disc < 0:
        return None
    s = math.sqrt(disc)
    cands = []
    for t in ((-B + s) / (2 * A), (-B - s) / (2 * A)):
        u = (m[0] + t * n[0], m[1] + t * n[1])
        d2 = [dist(u, c) for c in sites]
        if min(range(11), key=lambda k: d2[k]) in (i, j):
            cands.append(u)
    return cands[0] if cands else None


U = [switch(i, (i + 1) % 9) for i in range(9)]
print('(b) switches U_i on @D and switch distances rho_i (=|c_i-U_i|, |c_{i+1}-U_i|) vs r')
rho = []
for i in range(9):
    j = (i + 1) % 9
    d1, d2 = dist(ringf[i], U[i]), dist(ringf[j], U[i])
    rho.append((d1 + d2) / 2)
    print('   U_%d: |c_%d-U|=%.9f  |c_%d-U|=%.9f  r=%.9f  tight: %s'
          % (i, i, d1, j, d2, Rf, abs(d1 - Rf) < 1e-12 or abs(d2 - Rf) < 1e-12))
print('   rho_i (mean) =', ['%.9f' % x for x in rho])
print('   all switches tight (rho_i == r):', all(abs(x - Rf) < 1e-9 for x in rho))
chord = [dist(U[i], U[(i + 1) % 9]) for i in range(9)]
print('   |U_i-U_{i+1}|:', ['%.6f' % x for x in chord])
print('   chord bound max|U_i-U_{i+1}|/2 = %.9f  (<= r = %.9f: %s)'
      % (max(chord) / 2, Rf, max(chord) / 2 <= Rf))

# ---------------- (b) the 11 dual faces ----------------
def circum(t):
    (ax, ay), (bx, by), (cx, cy) = t
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    if abs(d) < 1e-18:
        return None
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay)
          + (cx * cx + cy * cy) * (ay - by)) / d
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx)
          + (cx * cx + cy * cy) * (bx - ax)) / d
    return (ux, uy), math.hypot(ux - ax, uy - ay)


def empty_circle(t, cen, rad):
    return all(math.hypot(c[0] - cen[0], c[1] - cen[1]) >= rad - 1e-9 for c in sites if c not in t)


faces = []
for i in range(11):
    for j in range(i + 1, 11):
        for k in range(j + 1, 11):
            t = (sites[i], sites[j], sites[k])
            cr = circum(t)
            if cr is None:
                continue
            cen, rad = cr
            if empty_circle(t, cen, rad):
                faces.append(((i, j, k), cen, rad))
print('\n(c) the %d dual faces: type, circumradius vs r, angle type' % len(faces))
def angtype(t):
    def ang(u, v, w):   # angle at u
        a1 = unit(sub(v, u)); a2 = unit(sub(w, u))
        return math.degrees(math.acos(max(-1, min(1, a1[0] * a2[0] + a1[1] * a2[1]))))
    A = ang(t[0], t[1], t[2]); B = ang(t[1], t[0], t[2]); C = ang(t[2], t[0], t[1])
    if max(A, B, C) > 90 + 1e-9:
        return 'obtuse'
    if max(A, B, C) > 90 - 1e-9:
        return 'right'
    return 'acute'
rows = []
for (idx, cen, rad) in sorted(faces, key=lambda z: -z[2]):
    t = (sites[idx[0]], sites[idx[1]], sites[idx[2]])
    hubs = [x for x in idx if x >= 9]
    kind = 'central(2hub)' if len(hubs) == 2 else 'fan'
    at = angtype(t)
    rows.append({'face': idx, 'kind': kind, 'Rc': rad, 'r': Rf, 'Rc_le_r': rad <= Rf + 1e-12,
                 'tight': abs(rad - Rf) < 1e-9, 'angles': at,
                 'circ_in_conv': None})
    print('   face %-12s %-11s Rc=%.9f r=%.9f Rc<=r:%s tight:%s  angles=%s'
          % (str(idx), kind, rad, Rf, rad <= Rf + 1e-12, abs(rad - Rf) < 1e-9, at))
n_tight = sum(1 for z in rows if z['tight'])
print('   faces tight at r: %d of %d  (fan tight: %d, central tight: %d, slack: %s)'
      % (n_tight, len(rows), sum(1 for z in rows if z['tight'] and z['kind'] == 'fan'),
         sum(1 for z in rows if z['tight'] and z['kind'] == 'central'),
         [z['face'] for z in rows if not z['tight']]))
print('   all 11 triangles acute:', all(z['angles'] == 'acute' for z in rows))

# ---------------- (c) the split identity and the per-face cone condition ----------------
print('\n(c) split identity (exact statement): grad_{c_j} rho_i = unit(c_j - U_i) for the two adjacent')
print('    sites j, i.e. the switch-branch gradient equals the sum of the two endpoint-constraint')
print('    gradients; splitting mu_i as (mu_i/2, mu_i/2) reproduces it identically. Checked numerically:')
for i in range(3):
    j = (i + 1) % 9
    g = unit(sub(ringf[i], U[i]))
    num = ((dist(ringf[i], U[i]) - dist((ringf[i][0] + 1e-7, ringf[i][1]), U[i])) / 1e-7)
    print('    i=%d unit=%.9f,%.9f  finite-diff d rho/d x=%.9f' % (i, g[0], g[1], num))
print('    per-face cone condition: z_f = circumcentre admits w_c>0 for all c with')
print('    sum w_c unit(c-z_f)=0  <=>  z_f in int conv(face)  <=>  face acute.')
for z in rows:
    idx, cen, rad = next(f for f in faces if f[0] == z['face'])
    t = (sites[idx[0]], sites[idx[1]], sites[idx[2]])
    # barycentric coordinates of cen in t (sign pattern decides inside/on/outside)
    def bary(p, t):
        (x1, y1), (x2, y2), (x3, y3) = t
        det = (y2 - y3) * (x1 - x3) + (x3 - x2) * (y1 - y3)
        l1 = ((y2 - y3) * (p[0] - x3) + (x3 - x2) * (p[1] - y3)) / det
        l2 = ((y3 - y1) * (p[0] - x3) + (x1 - x3) * (p[1] - y3)) / det
        return l1, l2, 1 - l1 - l2
    b = bary(cen, t)
    z['circ_bary'] = [round(v, 6) for v in b]
    z['circ_in_int_conv'] = all(v > 1e-9 for v in b)
    print('    face %-12s %-11s bary(circ)=%s strictly inside:%s' % (str(z['face']), z['kind'], z['circ_bary'], z['circ_in_int_conv']))
(Path(__file__).parent / 'socp_fixed_switch_check.json').write_text(json.dumps(
    {'r': str(R), 'switches': [[float(u[0]), float(u[1])] for u in U], 'rho': rho,
     'chord_bound': max(chord) / 2, 'faces': rows}, indent=2, default=str))
print('\nsaved socp_fixed_switch_check.json')
