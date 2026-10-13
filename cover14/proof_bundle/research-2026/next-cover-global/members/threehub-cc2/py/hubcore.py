# -*- coding: utf-8 -*-
"""
hubcore.py -- members/threehub-cc2

CHARACTERISE the hub layer exactly (this is the constraint that killed the earlier
searches): the three hubs of radius U must cover the closed core B(0,a), a = 1-2U.
Then measure the hub-core covering radius C(t, psi) on a fine grid, to get the exact
threshold t* from which hubs are legal.

Also report, for legal hub triples, the best coverD attainable with 11 active centres
(restricted search: rho = 1-U or 1.0, angles optimised) -- a lower-bound reading.

C(t,psi) := max over a fine polar grid of B(0,a) of min_j |x - h_j|;
legal <=> C <= U.
"""
import json, math
import numpy as np

U = 0.33173203427623414
A = 1.0 - 2.0 * U
INACT = 1.0 - U

ct = np.linspace(0, 2 * math.pi, 400, endpoint=False)
cr = np.linspace(A, 0.0, 200)
TT, RT = np.meshgrid(ct, cr)
P = np.stack([(RT * np.cos(TT)).ravel(), (RT * np.sin(TT)).ravel()], axis=1)


def core_radius(hub):
    hub = np.asarray(hub, float)
    d = np.sqrt(((P[:, None, :] - hub[None, :, :]) ** 2).sum(axis=2)).min(axis=1)
    return float(d.max())


def hub_tri(t, psi):
    return np.array([[t * math.cos(psi + 2 * math.pi * k / 3),
                      t * math.sin(psi + 2 * math.pi * k / 3)] for k in range(3)])


print("=== hub-core covering radius C(t) for equilateral triples at circumradius t ===")
print("   (the hubs are the ONLY disks that can cover B(0,a): an active centre with")
print("    |c| >= 1-U has |c - x| >= |c| - |x| >= (1-U) - a = U - U = ... check below)")
print()
print("   proof that active disks cannot help: for |c| >= 1-U and |x| <= a,")
print("     |c-x| >= |c| - a >= (1-U) - (1-2U) = U ,")
print("   and the inequality is STRICT for |c| > 1-U or |x| < a; equalities need")
print("   |c| = 1-U and |x| = a with x = -a c/|c|, i.e. only the antipodal boundary point.")
print()
for t in [0.20, 0.25, 0.30, 0.35, 0.39, 0.40, 0.405, 0.41, 0.42, 0.43, 0.45, 0.50, 0.55]:
    C = core_radius(hub_tri(t, 0.0))
    print(f"  t={t:.3f}  C={C:.9f}  U-C={U-C:+.3e}  legal={C <= U}")
print()
print("=== psi dependence at t=0.42 (rotation of the hub triangle) ===")
for psi in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]:
    print(f"  psi={psi:.2f} C={core_radius(hub_tri(0.42, psi)):.9f}")
print()
print("=== ablation: can the 11 active centres cover S1 by themselves (rho = 1-U)? ===")
th = np.linspace(0, 2 * math.pi, 20000, endpoint=False)
cs, sn = np.cos(th), np.sin(th)
for rho in [INACT, 0.70, 0.75, 0.8, 0.9, 1.0]:
    best = 1e9
    for shift in np.linspace(0, 2 * math.pi / 11, 60, endpoint=False):
        ang = shift + 2 * math.pi * np.arange(11) / 11
        dx = cs[:, None] - rho * np.cos(ang)[None, :]
        dy = sn[:, None] - rho * np.sin(ang)[None, :]
        d = float(np.sqrt(dx * dx + dy * dy).min(axis=1).max())
        best = min(best, d)
    print(f"  rho={rho:.6f}  uniform 11-gon best coverD = {best:.9f}  (U={U:.9f}) "
          f"deficit={best-U:+.3e}")
print()
print("=== the pure arithmetic bound (no hubs at all): 11 active disks, radius r,")
print("    centres |c| >= 1-r, must cover S1 ===")
print("  For a centre c, the covered arc on S1 has half-width")
print("      alpha(delta) = arccos((1 + (1-delta)^2 - r^2)/(2(1-delta))),  delta = 1-|c|,")
print("  and alpha(0) = arccos(1 - r^2/2) = 2 asin(r/2).  With 11 arcs:")
print("      11 * 2 asin(r/2) >= 2 pi  =>  r >= 2 sin(pi/11) = %.9f" % (2 * math.sin(math.pi / 11)))
print("  (uses only the best case delta_i = 0; the true bound is larger).")
