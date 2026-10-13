# -*- coding: utf-8 -*-
"""r20-alternative / debug: which points of the current-hubs split are (wrongly?) accepted as K?"""
import json, os
import numpy as np
from itertools import combinations
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))


def in_K(p, Cs, r, tol=1e-8, atol=1e-7):
    if np.linalg.norm(p) >= 1:
        return False, "|p|>=1"
    d = np.linalg.norm(Cs - p, axis=1)
    if d.min() < r - tol:
        return False, "covered min-r=%+.2e" % (d.min() - r)
    act = np.where(d <= r + atol)[0]
    if len(act) <= 1:
        return True, "active<=1 (active=%s)" % (act.tolist())
    v = Cs[act] - p
    ang = np.sort(np.arctan2(v[:, 1], v[:, 0]))
    gaps = np.diff(np.concatenate([ang, ang[:1] + 2 * np.pi]))
    gap = float(gaps.max())
    return (gap >= np.pi - 1e-9), "closed gap=%.6f (active=%s)" % (gap, act.tolist())


def circ_circ(p1, p2, r):
    d = np.linalg.norm(p2 - p1)
    if d > 2 * r or d == 0:
        return []
    m = 0.5 * (p1 + p2); u = (p2 - p1) / d
    h = np.sqrt(max(0.0, r * r - d * d / 4)); w = np.array([-u[1], u[0]])
    return [m + h * w, m - h * w]


def line_vertices(n, t, Cs, r):
    out = []
    for i, c in enumerate(Cs):
        z = t - n @ c
        if abs(z) > r:
            continue
        m = c + z * n
        h = np.sqrt(max(0.0, r * r - z * z)); w = np.array([-n[1], n[0]])
        for s in (-1, 1):
            p = m + s * h * w
            ok, why = in_K(p, Cs, r)
            if ok:
                out.append((p, i, why))
    return out


raw = json.load(open(os.path.join(ROOT, "n11", "upper", "certified_object.json"), encoding="utf-8-sig"))
C = np.array([[float(a) / 1e17, float(b) / 1e17] for a, b in raw["centers_scaled_1e17"]])
R = 0.3799838531198387090485182
rad = np.linalg.norm(C, axis=1)
ring = [i for i in range(11) if rad[i] >= 1 - R]
hubs = [i for i in range(11) if rad[i] < 1 - R]
Cr = C[ring]
h1, h2 = C[hubs[0]], C[hubs[1]]
n = (h2 - h1) / np.linalg.norm(h2 - h1)
t = (h2 @ h2 - h1 @ h1) / (2 * np.linalg.norm(h2 - h1))
print("hubs:", hubs, " h1=", h1, " h2=", h2, " bisector: n=", n, " t=%.12f" % t)
print("h1 side = {n.x <= t};  h2 side = {n.x >= t}")
LV = line_vertices(n, t, Cr, R)
print("line-circle vertices accepted as K:", len(LV))
for p, i, why in LV:
    print("   p=(%+.9f,%+.9f) |p|=%.6f owner=ring%d  d_h1=%.6f d_h2=%.6f side=%s  %s"
          % (p[0], p[1], np.linalg.norm(p), ring[i],
             np.linalg.norm(p - h1), np.linalg.norm(p - h2), "+" if n @ p - t > 0 else "-", why))
print("\nring-ring vertices in K and their sides:")
for i, j in combinations(range(len(ring)), 2):
    for p in circ_circ(Cr[i], Cr[j], R):
        ok, why = in_K(p, Cr, R)
        if ok:
            print("   p=(%+.9f,%+.9f) d_h1=%.6f d_h2=%.6f side=%s %s"
                  % (p[0], p[1], np.linalg.norm(p - h1), np.linalg.norm(p - h2), "+" if n @ p - t > 0 else "-", why))
