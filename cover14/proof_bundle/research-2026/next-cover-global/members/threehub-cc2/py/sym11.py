# -*- coding: utf-8 -*-
"""
sym11.py -- members/threehub-cc2

ONE focused run on the only family where the angular computation is clean:
  * hubs: equilateral triple at circumradius t, rotated so its directions sit at the
    antipodes of three of the active directions;
  * active centres: EQUALLY SPACED 11-gon of radius rho (rho >= 1-r);
  * measure the covering radius of D on a 2D grid, minimise over (rho, t) subject to
    the hub core condition C(t) <= U.
This is a LOWER-bound family (a single family, so its min is an upper bound for the
family only); it is reported as such.  Its interest is that the worst points are then
computable in closed form, which is what a rigorous certificate would need.
"""
import math, json
import numpy as np

U = 0.33173203427623414
A = 1.0 - 2.0 * U
INACT = 1.0 - U
T = 2 * math.pi / 11
NACT = 11


def grid2d(n):
    xs = np.linspace(-1.0, 1.0, n)
    X, Y = np.meshgrid(xs, xs)
    m = X * X + Y * Y <= 1.0 + 1e-12
    return np.stack([X[m], Y[m]], axis=1)


def maxmin(pts, C, chunk=40000):
    C = np.asarray(C, float)
    best = -1.0
    for i in range(0, len(pts), chunk):
        P = pts[i:i + chunk]
        d = np.sqrt(((P[:, None, :] - C[None, :, :]) ** 2).sum(axis=2)).min(axis=1)
        best = max(best, float(d.max()))
    return best


PF = grid2d(601)


def sym_family(rho, t, phase=0.0):
    ang = phase + T * np.arange(NACT)
    act = np.stack([rho * np.cos(ang), rho * np.sin(ang)], axis=1)
    # hubs at the antipodes of active directions 0, 4, 8 (equilateral triple)
    hp = phase + T * np.array([0, 4, 8]) + math.pi
    hub = np.stack([t * np.cos(hp), t * np.sin(hp)], axis=1)
    cr = max(math.hypot(x, y) for x, y in hub)
    return act, hub, cr


print("=== symmetric family: 11-gon active + equilateral hub at antipode directions ===")
print(f"  U={U:.12f}  1-U={INACT:.9f}  2U={2*U:.9f}")
best = None
for rho in [0.70, 0.75, 0.80, 0.85, 0.90, 0.95, 1.00, 1.05]:
    for t in [0.20, 0.25, 0.30, 0.328]:
        for ph in [0.0, T / 2]:
            act, hub, cr = sym_family(rho, t, ph)
            if cr > U:
                continue
            f = maxmin(PF, np.vstack([hub, act]))
            if best is None or f < best[0]:
                best = (f, rho, t, ph)
            print(f"  rho={rho:.2f} t={t:.3f} phase={ph:.3f} core_radius={cr:.6f}  "
                  f"coverD={f:.6f}  {'<U' if f < U else '>=U'}")
print()
print(f"  best in the symmetric family: coverD={best[0]:.9f} at rho={best[1]}, t={best[2]}, "
      f"phase={best[3]}  ({best[0]/U:.6f} * U)")

print()
print("=== closed-form worst-point check for the symmetric family (rho=1, phase=0) ===")
act, hub, cr = sym_family(1.0, 0.30, 0.0)
pts = np.vstack([act, hub])
print("  candidate worst points (computed by hand):")
for name, p in [("boundary mid-gap S1", (math.cos(T / 2), math.sin(T / 2))),
                ("annulus inner, mid-gap", (2 * U * math.cos(T / 2), 2 * U * math.sin(T / 2))),
                ("hub-disk boundary nearest active", None),
                ("core far point", (A * math.cos(math.pi / 3), A * math.sin(math.pi / 3)))]:
    if p is None:
        continue
    d = min(math.hypot(p[0] - c[0], p[1] - c[1]) for c in pts)
    print(f"    {name:34s} p={tuple(round(q,6) for q in p)}  nearest={d:.9f}")
print()
print("=== how much does the hub (t) choice matter at rho=1? ===")
for t in [0.10, 0.20, 0.30, 0.328]:
    act, hub, cr = sym_family(1.0, t, 0.0)
    print(f"  t={t:.3f} core_radius={cr:.6f} coverD={maxmin(PF, np.vstack([hub, act])):.6f}")
