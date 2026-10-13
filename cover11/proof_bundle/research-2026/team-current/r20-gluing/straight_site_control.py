# -*- coding: utf-8 -*-
"""straight_site_control.py — BOUNDED numeric control (one configuration, floats) for the
straight-site realization question raised by the lead:

  (i)  is the arc order of the nine ring cells on ∂D the same as their angular order?
  (ii) is each ring site's own angle inside its own arc (radial-wedge property)?
  (iii) is the polygon P through the ring sites in arc order simple, is it star-shaped
       about the origin, and do the two hubs lie strictly inside P?
  (iv) are the Delaunay triangles whose circumcentre lies in D exactly the faces of the clipped
       dual -- and does their union have the area of P (no extra exterior triangles)?

This is a CONTROL on the saved configuration, not a proof for the class.  Data: exact rational
centres (1e17 scale); r = saved rational upper object.  Ring/hub roles per C896 labelling.
"""
import json
import math
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(r'C:\Users\袁力阳\Desktop\ai4math2')
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
Pf = [(float(F(int(x[0]), 10 ** 17)), float(F(int(x[1]), 10 ** 17))) for x in raw['centers_scaled_1e17']]
NEW2RAW_RINGS = [5, 7, 1, 8, 6, 4, 9, 10, 3]
R = float(F(3799838531198387090485182, 10 ** 25))
sites = [Pf[NEW2RAW_RINGS[i]] for i in range(9)] + [Pf[0], Pf[2]]   # 9 rings + hubA(raw0), hubB(raw2)
rings, hubs = sites[:9], sites[9:]
N = 200000

# ---------------- (i)+(ii) arcs on ∂D ----------------
owner = []
for k in range(N):
    th = 2 * math.pi * k / N
    u = (math.cos(th), math.sin(th))
    d = [math.hypot(u[0] - c[0], u[1] - c[1]) for c in sites]
    owner.append(min(range(11), key=lambda j: d[j]))
# arc order of ring owners around the circle (start from an arbitrary index and rotate)
starts = [k for k in range(N) if owner[k] != owner[k - 1]]
order = [owner[k] for k in starts]
print('owner sequence over ∂D (11 sites, first appearance order):', order)
ring_arc_order = []
for k in starts:
    i = owner[k]
    if i < 9 and i not in ring_arc_order:
        ring_arc_order.append(i)
print('ring arcs in cyclic order:', ring_arc_order)
ang = [math.atan2(c[1], c[0]) for c in rings]
ang_order = sorted(range(9), key=lambda i: ang[i] % (2 * math.pi))
print('ring sites in angular order:', ang_order)
print('(i) arc order == angular order:', ring_arc_order == ang_order)

# radial-wedge: is arg(c_i) inside its own arc's angular span?
spans = {}
for idx, k in enumerate(starts):
    i = owner[k]
    k2 = starts[(idx + 1) % len(starts)]
    # span of angles covered by this arc
    a0 = 2 * math.pi * k / N
    a1 = 2 * math.pi * k2 / N
    spans.setdefault(i, []).append((a0, a1))


def in_span(a, a0, a1):
    if a1 < a0:
        a1 += 2 * math.pi
    aa = a
    if aa < a0:
        aa += 2 * math.pi
    return a0 - 1e-12 <= aa <= a1 + 1e-12


ok = 0
for i in range(9):
    if any(in_span(ang[i] % (2 * math.pi), a0, a1) for (a0, a1) in spans[i]):
        ok += 1
print('(ii) ring sites whose own angle lies in their arc: %d/9' % ok)

# ---------------- (iii) polygon P: simple? star-shaped? hubs inside? ----------------
P = [rings[i] for i in ring_arc_order]


def seg_int(p1, p2, q1, q2):
    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
    d1, d2 = cross(q1, q2, p1), cross(q1, q2, p2)
    d3, d4 = cross(p1, p2, q1), cross(p1, p2, q2)
    return ((d1 > 0) != (d2 > 0)) and ((d3 > 0) != (d4 > 0))


n = len(P)
simple = True
for i in range(n):
    for j in range(i + 1, n):
        if abs(i - j) in (0, 1) or (i == 0 and j == n - 1):
            continue
        if seg_int(P[i], P[(i + 1) % n], P[j], P[(j + 1) % n]):
            simple = False
print('(iii) polygon P simple:', simple)


def inside(poly, pt):
    x, y = pt
    c = False
    for i in range(len(poly)):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % len(poly)]
        if ((y1 > y) != (y2 > y)) and (x < (x2 - x1) * (y - y1) / (y2 - y1) + x1):
            c = not c
    return c


print('       hubs inside P:', [inside(P, h) for h in hubs])
# star-shaped about the origin: every P vertex visible from the origin?  check origin inside P and
# each edge seen from origin
print('       origin inside P:', inside(P, (0.0, 0.0)))

# ---------------- (iv) Delaunay triangles with circumcentre in D vs area(P) ----------------
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


tris = []
for i in range(11):
    for j in range(i + 1, 11):
        for k in range(j + 1, 11):
            t = (sites[i], sites[j], sites[k])
            cr = circum(t)
            if cr is None:
                continue
            cen, rad = cr
            if empty_circle(t, cen, rad):
                tris.append((i, j, k, cen, rad))
inside_tris = [t for t in tris if math.hypot(t[3][0], t[3][1]) <= 1.0]
print('(iv) empty-circle triangles: %d ; with circumcentre inside D: %d' % (len(tris), len(inside_tris)))


def area(t):
    (ax, ay), (bx, by), (cx, cy) = t
    return abs((bx - ax) * (cy - ay) - (by - ay) * (cx - ax)) / 2


def poly_area(poly):
    s = 0.0
    for i in range(len(poly)):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % len(poly)]
        s += x1 * y2 - x2 * y1
    return abs(s) / 2


sum_in = sum(area((sites[t[0]], sites[t[1]], sites[t[2]])) for t in inside_tris)
print('       area(P) = %.12f ; sum of inside-centre Delaunay triangles = %.12f ; ratio = %.9f'
      % (poly_area(P), sum_in, sum_in / poly_area(P)))
print('       hub degrees (number of incident faces with centre inside D):',
      [sum(1 for t in inside_tris if h in t[:3]) for h in (9, 10)])
print('       ring degrees:', [sum(1 for t in inside_tris if i in t[:3]) for i in range(9)])
print('       total faces:', len(inside_tris), '(Euler check: V=11, E should be 21 if trivalent)')
