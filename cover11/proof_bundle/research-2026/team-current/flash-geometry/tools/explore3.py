import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import *

rr = 0.38
m = 9
rhoT = tiling_rho_uniform(m, rr)

def hole_entry(theta, rho, phi, rr):
    """First radius d>=0 along direction theta where (d,theta) is OUTSIDE B((rho,phi),rr).
    (near root of d^2-2 rho cos(theta-phi) d + rho^2-rr^2 = 0), clipped to D."""
    ct = np.cos(theta - phi)
    disc = rr*rr - (rho*np.sin(theta - phi))**2
    if disc <= 0:
        return None           # ray never enters the disk
    d = rho*ct - np.sqrt(disc)
    if d < 0:
        return 0.0            # origin already outside
    return d

print("Rays at the two tangent directions theta, and the gap width between the")
print("hole-entry points on those two rays (both points are in cl(hole)).")
print("\n rho      alpha     hw        d(th)     d(th+2a)   dist(p,q)  2rr      alpha-hw")
for rho in (0.63, 0.65, 0.7, 0.72, 0.75, rhoT, 0.8, 0.9):
    hw = arc_halfwidth(rho, rr)
    for alpha in (np.pi/m, hw, 0.5*(np.pi/m+hw)):
        d1 = hole_entry(0.0, rho, 0.0, rr)
        d2 = hole_entry(2*alpha, rho, 0.0, rr)
        d3 = hole_entry(2*alpha, rho, 2*alpha, rr)
        d4 = hole_entry(0.0, rho, 2*alpha, rr)
        # point on ray theta is in cl(hole) iff outside BOTH disks
        # -> need max over the two disks of their entry radius
        D1 = max(x for x in (d1, d4) if x is not None)
        D2 = max(x for x in (d2, d3) if x is not None)
        D1 = min(D1, 1.0); D2 = min(D2, 1.0)
        p = np.array([D1, 0.0]); q = np.array([D2*np.cos(2*alpha), D2*np.sin(2*alpha)])
        print("%.4f  %.6f  %.6f  %.6f  %.6f  %.8f  %.4f  %+.6f" % (
            rho, alpha, hw, D1, D2, np.linalg.norm(p-q), 2*rr, alpha-hw))
