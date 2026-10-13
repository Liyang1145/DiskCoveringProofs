import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import *
from scipy.optimize import brentq

rr = 0.38
m = 9
rhoT = tiling_rho_uniform(m, rr)
print("rho_tile =", rhoT, " sqrt(1-rr^2)=", np.sqrt(1-rr*rr))

def hole_depth(theta, rho, rr, mcenter=0.0):
    """max d>=0 with (d cos th, d sin th) outside B((rho,0),rr); the ray always
    has a direction (theta=pi) where the point far out is outside when rho<1..."""
    # solve d^2 - 2 rho cos(th) d + rho^2 - rr^2 = 0
    b = -2*rho*np.cos(theta - mcenter)
    c = rho*rho - rr*rr
    disc = b*b - 4*c
    if disc <= 0:
        return None
    return 0.5*(-b + np.sqrt(disc))

def hole_dmax_rays(rho, rr, alpha):
    """rays theta and theta+2alpha (symmetric about the mid direction alpha):
    max radius d such that both points are outside B(pa,rr) and B(pb,rr) and in D."""
    out = []
    for th in (0.0, 2*alpha):
        vals = []
        for (pr, ph) in ((rho, 0.0), (rho, 2*alpha)):
            d = hole_depth(th, pr, rr, ph)
            vals.append(d)
        out.append(min([v for v in vals if v is not None]))
    return out

print("\n rho      alpha     half-width   d(0)     d(2a)    diam(pts)  2rr")
for rho in (0.63, 0.65, 0.7, rhoT, 0.8, 0.9):
    for alpha in (np.pi/m, arc_halfwidth(rho, rr), 0.5*(np.pi/m+arc_halfwidth(rho, rr))):
        d0, d2 = hole_dmax_rays(rho, rr, alpha)
        p0 = np.array([d0, 0.0]); p2 = np.array([d2*np.cos(2*alpha), d2*np.sin(2*alpha)])
        print("%.4f  %.6f  %.6f  %.6f %.6f  %.8f  %.4f" % (rho, alpha, arc_halfwidth(rho,rr), d0, d2, np.linalg.norm(p0-p2), 2*rr))
