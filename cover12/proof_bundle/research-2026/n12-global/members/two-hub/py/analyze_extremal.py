"""analyze_extremal.py -- structure of the best k=10 configurations found.

For a saved search JSON: recompute R_cand, list the maximizers (candidate points
at distance ~R), classify them, and print the local structure:
  * norms / angles of the 10 rings and 2 hubs,
  * for the maximizers: which disks are at distance R (<= R+tol), the multiplicity,
  * the hub-union boundary geometry: exposed arc measures, hub distance d,
  * the ring boundary arcs (halfwidths) and the sum.
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent.parent / "finite-reduction" / "py"))
import k10_feas as K  # noqa: E402
import candlib  # noqa: E402


def analyze(path, tol=1e-7, topk=6):
    d = json.load(open(path))
    C = np.array(d["centers"])
    r = d["row"]["r"]
    val, arg, P = K.R_cand(C)
    D = P[:, None, :] - C[None, :, :]
    dist = np.sqrt((D * D).sum(axis=2))
    f = dist.min(axis=1)
    order = np.argsort(f)[::-1]
    print("file:", Path(path).name, " r=%.12f  R_cand=%.12f  R_ref=%.12f"
          % (r, val, d["row"]["R_ref"]))
    nrm = np.hypot(C[:, 0], C[:, 1])
    ang = np.arctan2(C[:, 1], C[:, 0])
    print("ring norms:", np.round(nrm[:10], 5))
    print("ring angles:", np.round(np.sort(ang[:10]), 5))
    al = [math.acos(max(-1, min(1, (1 + nrm[i] ** 2 - r * r) / (2 * nrm[i]))))
          for i in range(10)] if nrm[:10].min() > 0 else None
    if al:
        print("ring halfwidths:", np.round(sorted(al), 5), " sum=%.6f (pi=%.6f)"
              % (sum(al), math.pi))
    print("hub norms: %.6f %.6f   angle between hubs: %.6f"
          % (nrm[10], nrm[11], abs((ang[10] - ang[11] + math.pi) % (2 * math.pi) - math.pi)))
    dv = C[10] - C[11]
    dist_h = float(np.hypot(*dv))
    print("hub distance d=%.6f  (2r=%.6f)" % (dist_h, 2 * r))
    if 0 < dist_h < 2 * r:
        b = math.acos(dist_h / (2 * r))
        print("  exposed arc halfwidth b=%.6f  |E_j|=%.6f each  total %.6f"
              % (b, 2 * math.pi - 2 * b, 2 * (2 * math.pi - 2 * b)))
    # core condition check
    a = 1 - 2 * r
    def beta(t):
        if t <= 0:
            return math.pi
        if t + a <= r:
            return math.pi
        if abs(t - a) >= r:
            return 0.0
        return math.acos(max(-1, min(1, (t * t + a * a - r * r) / (2 * t * a))))
    b1, b2 = beta(nrm[10]), beta(nrm[11])
    delta = abs((ang[10] - ang[11] + math.pi) % (2 * math.pi) - math.pi)
    print("core a=%.6f  beta1=%.6f beta2=%.6f  beta1+beta2=%.6f  need>=2pi-delta=%.6f  %s"
          % (a, b1, b2, b1 + b2, 2 * math.pi - delta, b1 + b2 >= 2 * math.pi - delta - 1e-9))
    print("top maximizers (distance value, position, nearest disks with distance):")
    for k in order[:topk]:
        if f[k] < val - 1e-6:
            break
        near = [i for i in range(12) if dist[k, i] <= f[k] + tol]
        print("  f=%.9f  x=(%.6f,%.6f) |x|=%.6f  nearest=%s  dists=%s"
              % (f[k], P[k][0], P[k][1], float(np.hypot(*P[k])), near,
                 np.round(dist[k, near], 9)))
    return dict(R=val, C=C, r=r)


if __name__ == "__main__":
    for p in sys.argv[1:]:
        analyze(p)
        print()
