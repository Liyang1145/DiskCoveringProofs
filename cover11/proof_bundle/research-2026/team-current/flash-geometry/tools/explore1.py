import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import *

np.set_printoptions(precision=10, suppress=False)

rr = 0.38
m = 9
rho_tile = tiling_rho_uniform(m, rr)
print("rr=", rr, " m=", m)
print("uniform tiling rho =", rho_tile, " (check halfwidth:", arc_halfwidth(rho_tile, rr), "pi/m=", np.pi/m, ")")
print("arc ends at |.|:", np.sqrt(rho_tile**2 + 1 - 2*rho_tile*np.cos(np.pi/m)))

rho0 = 0.7
print("\nrho0=", rho0, "halfwidth=", arc_halfwidth(rho0, rr), "total arcs=", m*arc_halfwidth(rho0, rr))

def analyse(rho_a, rho_b, rr, alpha):
    """centers at angles 0 and 2alpha; report pocket geometry."""
    pa = np.array([rho_a, 0.0])
    pb = np.array([rho_b*np.cos(2*alpha), rho_b*np.sin(2*alpha)])
    wa = arc_halfwidth(rho_a, rr); wb = arc_halfwidth(rho_b, rr)
    ea = (pa, wa)   # arc ends: phi=-wa..+wa
    ends = []
    for (p, w, phi) in ((pa, wa, 0.0), (pb, wb, 2*alpha)):
        for s in (-1, 1):
            ends.append(np.array([np.cos(phi + s*w), np.sin(phi + s*w)]))
    corners = pocket_corners(rho_a, 0.0, rho_b, 2*alpha, rr)
    # the pocket is the region outside both disks, inside unit circle, on the
    # "near" side (containing the point at angle alpha, radius 1-?)
    alpha_mid = alpha
    pt_mid = np.array([ (1-rr)*np.cos(alpha_mid), (1-rr)*np.sin(alpha_mid)])
    # candidate vertices: corners outside both disks
    verts = [c for c in corners if np.linalg.norm(c-pa) >= rr-1e-12 and np.linalg.norm(c-pb) >= rr-1e-12]
    # arc-end points that belong to this pocket (angularly between the two centers)
    ang_ok = []
    for q in ends:
        th = np.arctan2(q[1], q[0])
        if 0.0 < th < 2*alpha:
            ang_ok.append(q)
    allpts = verts + ang_ok
    c, R = min_enclosing_ball(allpts)
    return dict(alpha=alpha, wa=wa, wb=wb, verts=verts, arcends=ang_ok, R=R, c=c,
                pt_mid=pt_mid, corners=corners)

for alpha in (np.pi/m, 0.5*(np.pi/m + arc_halfwidth(rho0, rr)), arc_halfwidth(rho0, rr)):
    d = analyse(rho0, rho0, rr, alpha)
    print("\nalpha=%.10f  halfwidth=%.10f" % (alpha, d['wa']))
    print("  corners:", [np.round(v,8) for v in d['corners']])
    print("  verts:", [np.round(v,8) for v in d['verts']])
    print("  arc ends in pocket:", [np.round(v,8) for v in d['arcends']])
    print("  MEB of listed pts:", np.round(d['c'],8), "R=%.10f" % d['R'])
