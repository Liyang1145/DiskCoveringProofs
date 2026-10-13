"""Numeric study of the 9-ring + 2-hub covering of the unit disk.

We evaluate the true covering radius R_D(C) = max_{x in D} min_i |x-c_i| of a
configuration (a NECESSARY and SUFFICIENT condition for covering at radius r is
R_D(C) <= r).  Fast numeric only; certified objects live elsewhere.

Two families:
 (A) 9 rings at a common radius rho, equally spaced, + 2 hubs (incl. at origin)
 (B) free 9 rings (angles) + 2 hubs, local optimisation
"""
import numpy as np, sys, os
from scipy.optimize import minimize

# ---------- covering radius evaluation ----------
def covering_radius(C, ntheta=2880, nd=280, refine=True):
    """max over D of min_i |x-c_i|, to ~1e-9 by (coarse grid) + (local refine)."""
    th = np.linspace(0, 2*np.pi, ntheta, endpoint=False)
    U = np.stack([np.cos(th), np.sin(th)], 1)
    best = -1.0; bp = None
    for d in np.linspace(0, 1, nd):
        P = d * U
        v = np.sqrt(((P[:, None, :] - C[None, :, :]) ** 2).sum(-1).min(1))
        k = int(np.argmax(v))
        if v[k] > best:
            best = float(v[k]); bp = P[k].copy()
    if refine:
        # Nelder-Mead on -min-dist, started at bp (a max of a non-smooth function)
        f = lambda p: -np.sqrt(((p - C) ** 2).sum(1).min())
        res = minimize(f, bp, method='Nelder-Mead',
                       options=dict(xatol=1e-13, fatol=1e-15, maxiter=4000))
        if -res.fun > best:
            best = -res.fun; bp = res.x
    return best, bp

def make_family_A(rho, r=0.38, hub_scale=0.0, hub_angle=0.0):
    th = np.arange(9) * (2 * np.pi / 9)
    C = [np.array([rho * np.cos(t), rho * np.sin(t)]) for t in th]
    C.append(np.array([hub_scale * np.cos(hub_angle), hub_scale * np.sin(hub_angle)]))
    C.append(np.array([-hub_scale * np.cos(hub_angle), -hub_scale * np.sin(hub_angle)]))
    return np.array(C)

if __name__ == "__main__":
    r = 0.38
    print("=== Family A: 9 rings at radius rho (equal spacing) + 2 hubs at +-s*u ===")
    print("  rho    s     R_D      (r=0.38)")
    for rho in (0.62, 0.70, 0.76, 0.80, 0.85, 0.90, 0.925):
        for s in (0.0, 0.1, 0.2, 0.24):
            C = make_family_A(rho, r, s)
            Rd, bp = covering_radius(C, ntheta=1440, nd=200)
            print("  %.3f  %.2f  %.7f   %s" % (rho, s, Rd, "" if Rd <= r else "*"))
