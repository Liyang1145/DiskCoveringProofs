import json, io, sys, os
import numpy as np
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from geom import *

d = json.load(io.open('n11/upper/certified_object.json', encoding='utf-8'))
C = [(int(a)/1e17, int(b)/1e17) for a, b in d['centers_scaled_1e17']]
R = 0.379983853119838709049
print("R_cert =", R)
print("centers and |c_i| (R-r margin):")
for i, (x, y) in enumerate(C):
    rho = np.hypot(x, y)
    print("  %2d  (%+.10f, %+.10f)  |c|=%.10f   |c|-%0.8f" % (i, x, y, rho, rho - R))
print("\nactual R_D of this object (float):")
def R_D(C, Rmax):
    # max over D of min_i |p-c_i|  -> brute force on fine angular/radial grid
    best = 0.0; bp = None
    for th in np.linspace(0, 2*np.pi, 721):
        # for each direction, solve max over d in [0,1]
        u = np.array([np.cos(th), np.sin(th)])
        for d in np.linspace(0, 1, 401):
            p = d*u
            v = min(np.linalg.norm(p - np.array(c)) for c in C)
            if v > best:
                best = v; bp = p
    return best, bp
b, bp = R_D(C, R)
print("   grid max = %.10f at %s" % (b, np.round(bp, 8)))
