# -*- coding: utf-8 -*-
"""
calib_ring_control.py -- members/threehub-cc2

The first run's "control" (all 14 centres on a circle of radius 4/3) is NOT a cover
of D: the origin is at distance 4/3 > U from every centre.  So the 4/3 in the
literature entry "Friedman 13/14/15/25" is not a single-ring circumradius.

HYPOTHESIS TO TEST (calibration of the instrument on a KNOWN answer).
The n14 construction has TWO radii classes:
  * "rim" centres at distance 4/3 from the origin, on m equally spaced directions;
  * "core" centres on the triangular lattice of spacing r = 1/3 (so that the three
    disks of radius r about any lattice point of a triangular lattice tile the plane,
    hence every point is within r of some lattice point).
Test: (a) find the minimal number m of rim centres, at distance 4/3, that covers the
boundary circle |x| = 1 together with their neighbours -- i.e. the condition that the
rim centres' radius-r disks cover annulus part; (b) total = m rim + core count = 14;
(c) the resulting configuration must have covering radius exactly 1/3.

Known answer to reproduce: U_extended ~ 0.331732034276 = covering radius of the
"1/3-triangular lattice + rim" construction with 14 centres (C411 upper bound).

This script only measures; it does not prove.  It exists so that every later number I
report is tied to a known control.
"""
import json, math
import numpy as np

R = 1.0 / 3.0
SP = R                      # lattice spacing
D = 4.0 / 3.0               # absolute value of rim centre distances


def tri_lattice(count):
    """triangular lattice points (i*j grid) sorted by norm, take `count` smallest."""
    pts = []
    for i in range(-12, 13):
        for j in range(-12, 13):
            x = SP * (i + 0.5 * j)
            y = SP * (math.sqrt(3) / 2) * j
            pts.append((x, y))
    pts.sort(key=lambda p: p[0] ** 2 + p[1] ** 2)
    return np.array(pts[:count])


def rim(m, phase=0.0):
    ang = phase + 2 * math.pi * np.arange(m) / m
    return np.stack([D * np.cos(ang), D * np.sin(ang)], axis=1)


def cover_radius(centers, nth=400, nr=200):
    th = np.linspace(0, 2 * math.pi, nth, endpoint=False)
    rr = np.linspace(1.0, 0.0, nr)
    TT, RT = np.meshgrid(th, rr)
    P = np.stack([(RT * np.cos(TT)).ravel(), (RT * np.sin(TT)).ravel()], axis=1)
    c = np.asarray(centers)
    d = np.sqrt(((P[:, None, :] - c[None, :, :]) ** 2).sum(axis=2)).min(axis=1)
    k = int(np.argmax(d))
    return float(d[k]), P[k].tolist()


print("=== (a) rim-only: what does m rim centres at 4/3 and radius r cover? ===")
for m in range(3, 16):
    cr, wp = cover_radius(rim(m), nth=1440, nr=400)
    print(f"  m={m:2d} rim-only covering radius of D = {cr:.6f}   worst {wp}")
print()
print("=== (b) triangular core lattice of radius 1/3: covering radius of D (core only) ===")
for cnt in [7, 10, 11, 12, 13]:
    lat = tri_lattice(cnt)
    cr, wp = cover_radius(lat, nth=1440, nr=400)
    print(f"  {cnt:2d} lattice pts: covering radius of D = {cr:.6f}  worst {wp}")
    if cnt == 10:
        np.save("research-2026/next-cover-global/members/threehub-cc2/evidence/"
                "tri10.npy", lat)
print()
print("=== (c) mixtures: m rim centres at 4/3 + k lattice points, total 14 ===")
for m in [3, 4, 5, 6]:
    k = 14 - m
    best = None
    for phase in np.linspace(0, 2 * math.pi / m, 12, endpoint=False):
        C = np.vstack([rim(m, phase), tri_lattice(k)])
        cr, wp = cover_radius(C, nth=1440, nr=400)
        if best is None or cr < best[0]:
            best = (cr, wp, phase)
    print(f"  m={m:2d} rim + {k:2d} lattice = 14 centres: covering radius = "
          f"{best[0]:.9f}  worst {best[1]}  phase {best[2]:.4f}")
