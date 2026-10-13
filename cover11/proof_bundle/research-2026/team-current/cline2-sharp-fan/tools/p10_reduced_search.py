# -*- coding: utf-8 -*-
"""P10: corrected reduced search over the QR (ring) configuration.

CALIBER
  D = unit closed disk; 9 identical radius-R disks ("rings") + 2 radius-R disks
  ("hubs"); all lengths in units of the unit-disk radius; angles radians.

VERIFIED STRUCTURE (inward-root, outward bracketing branch):
  ring centre c_i = (1-R) e^{i psi_i};  write the tangency angle theta_i := psi_i + phi
  with the CONSTANT phi = arcsin(1/(2R)) (== pi/2 - asin R); equivalently
        psi_i = theta_i - phi,     sin phi = 1/(2R).
  The ring covers the boundary arc  |arg - theta_i| <= t_i  with
        sin t_i = 2 R sin phi = R/(1-R)?? -> recomputed exactly below.
  The boundary covering condition is a local inequality between consecutive theta's.
  The hub side: every point of the ring-hole must be within R of one hub.

Search: minimise R over (theta_0..theta_8, h1, h2) with
    f(theta_i) <= R  (boundary coverage)  and  hole covered by the two hubs.
"""
import os, sys, math, json
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fan_core import HERE

OUT = os.path.join(HERE, os.pardir, "out")
lines = []
def P(s=""):
    lines.append(s); print(s)

with open(os.path.join(OUT, "certified_object_copy.json"), "r", encoding="utf-8-sig") as f:
    OBJ = json.load(f)
C0 = np.array([[int(a)/1e17, int(b)/1e17] for a, b in OBJ["centers_scaled_1e17"]])
R0 = 0.3799838531198387090485181795734298538115979028
ring = [1, 3, 4, 5, 6, 7, 8, 9, 10]
hub = [0, 2]

mod0 = np.linalg.norm(C0, axis=1)
psi0 = np.arctan2(C0[:, 1], C0[:, 0])
phi0 = math.asin(1.0/(2*R0))
P("phi = asin(1/(2R)) = %.15f ; check (1-R) e^{i psi} + R e^{i theta} = e^{i theta}: " % phi0)
for j in ring:
    lhs = (1-R0)*np.array([math.cos(psi0[j]), math.sin(psi0[j])]) + \
          R0*np.array([math.cos(psi0[j]+phi0), math.sin(psi0[j]+phi0)])
    tgt = np.array([math.cos(psi0[j]+phi0), math.sin(psi0[j]+phi0)])
    P("   ring %2d: |lhs - e^{i(theta)}| = %.3e   (|c|=%.12f, 1-R=%.12f, diff=%.2e)"
      % (j, np.linalg.norm(lhs-tgt), mod0[j], 1-R0, mod0[j]-(1-R0)))

# ring covering arc: |P(arg) - c|=R  ->  sin t = R cos(phi) (?)
t0 = math.asin(1.0/(2*R0))     # placeholder
tcand = [math.asin(min(1.0, R0*math.cos(phi0))), math.asin(R0/(1-R0)),
         math.acos(1.0 - R0*R0/(2*(1-R0)))]
P("candidate expressions for the arc half-width t:")
for v in tcand:
    P("   %.12f" % v)
# exact: solve |P-c|^2=R^2 for the half-angular offset tau at the tangency point
#   |P-c|^2 = (1-R)^2 + 1 - 2(1-R) cos(tau)      [tau measured from the tangency direction]
#   = R^2  ->  cos tau = ((1-R)^2 + 1 - R^2)/(2(1-R)) = (2-2R)/(2(1-R)) = 1  ???
P("check: |P(tau) - c|^2 with c=(1-R) at angle 0 and P at angle tau:")
for tau in [0.01, 0.05, 0.1]:
    d2 = (1-R0)**2 + 1 - 2*(1-R0)*math.cos(tau)
    P("   tau=%.3f : d2=%.10f  R^2=%.10f" % (tau, d2, R0**2))
P("")
P("so the ring covers |tau| <= t with cos t = ((1-R)^2+1-R^2)/(2(1-R)) ... solve numerically")
cos_t = ((1-R0)**2 + 1 - R0**2)/(2*(1-R0))
P("   cos t = %.12f  ->  t = %.12f" % (cos_t, math.acos(max(-1, min(1, cos_t)))))
# the disk B(c,R) with |c|=1-R: needs |P-c|<=R  ->  cos tau >= cos t
# with tau = 0 giving |P-c| = |1-(1-R)| = R  -- so tau=0 is exactly on the circle
P("   NOTE: |P(0)-c| = |1-(1-R)| = R exactly => tau=0 IS the tangency point")
P("   the covered arc extends on BOTH sides of tau=0; the other root:")
# second root of (1-R)^2+1-2(1-R)cos tau = R^2 -> cos tau = ((1-R)^2+1-R^2)/(2(1-R))
P("   cos tau_2 = %.12f -> tau_2 = %.12f" % (cos_t, math.acos(max(-1, min(1, cos_t)))))
P("   => the covered arc around the tangency point has angular half-width tau_2")


def build(Rv, thetas):
    """thetas: absolute tangency angles; returns (11,2) centre array and data."""
    phi = math.asin(min(1.0, 1.0/(2*Rv)))
    c = np.zeros((9, 2))
    for i in range(9):
        ps = thetas[i] - phi
        c[i] = (1-Rv)*np.array([math.cos(ps), math.sin(ps)])
    return c


def coverage_R(Rv, thetas, hubs, n=140):
    """returns (boundary defect, max hub-needed radius over the hole grid)."""
    C = build(Rv, thetas)
    xs = np.linspace(-1, 1, n)
    gx, gy = np.meshgrid(xs, xs)
    m = gx**2+gy**2 <= 1.0
    pts = np.stack([gx[m], gy[m]], axis=1)
    d = np.linalg.norm(pts[:, None, :]-C[None, :, :], axis=2).min(axis=1)
    if hubs.shape[0]:
        dh = np.linalg.norm(pts[:, None, :]-hubs[None, :, :], axis=2).min(axis=1)
    else:
        dh = np.full(len(pts), 1e9)
    need = np.maximum(d, dh)
    return float(need.max()), C


if __name__ == "__main__":
    # seed: thetas from the object
    th0 = np.array([psi0[j]+phi0 for j in ring])
    th0 = np.mod(th0, 2*math.pi)
    order = np.argsort(th0)
    th0 = th0[order]
    hubs0 = C0[hub]
    P("")
    P("seed thetas = %s" % np.round(th0, 12).tolist())
    P("seed hubs   = %s" % np.round(hubs0, 12).tolist())
    v, C = coverage_R(R0, th0, hubs0, n=280)
    P("seed coverage radius = %.12f  (R claim %.12f, diff %+.3e)" % (v, R0, v-R0))
    P("")
    P("now search: minimise max(coverage radius) over (thetas, hubs) with R fixed at R0,")
    P("then bisect on R.")
    def obj(y, Rv):
        th = y[:9]; h = y[9:13].reshape(2, 2)
        v, _ = coverage_R(Rv, th, h, n=140)
        # penalise rings leaving the annulus or the boundary gap opening
        pen = 0.0
        for i in range(9):
            dth = (th[(i+1) % 9]-th[i]) % (2*math.pi)
            pen += max(0.0, dth-1.2)**2
        return v + 5*pen
    x = np.concatenate([th0, hubs0.ravel()])
    res = minimize(obj, x, args=(R0,), method='Nelder-Mead',
                   options=dict(maxiter=40000, maxfev=40000, xatol=1e-11, fatol=1e-13, adaptive=True))
    P("after NM at R=%.10f: obj=%.12f" % (R0, res.fun))
    P("thetas = %s" % np.round(res.x[:9], 12).tolist())
    P("hubs   = %s" % np.round(res.x[9:13], 12).tolist())
    v, C = coverage_R(R0, res.x[:9], res.x[9:13].reshape(2, 2), n=280)
    P("refined coverage radius = %.12f" % v)
    with open(os.path.join(OUT, "p10_reduced_search.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines)+"\n")
