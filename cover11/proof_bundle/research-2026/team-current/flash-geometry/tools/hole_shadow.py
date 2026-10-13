"""Shadow / depth necessary-condition instrument, calibrated on the certified
9+2 object, plus a direct measurement of the ring hole.

Objects: rings = 9 centres with |a_i| >= 1-r (these are the only centres that can
reach the boundary); hubs = 2 centres with |h| < 1-r (they cannot reach it).

Facts used (exact, elementary):
 * hub covering a point p forces |h| >= |p| - r; hence |h| >= 1-2r if p on ∂D
   (but a hub with |h| < 1-r cannot cover ∂D at all: |u-h| >= 1-|h| > r).
 * any disc centered h covers directions within arcsin(r/|h|) of h's direction.
"""
import numpy as np, io, json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

r = 0.38
d = json.load(io.open('n11/upper/certified_object.json', encoding='utf-8'))
C = np.array([[int(a)/1e17, int(b)/1e17] for a, b in d['centers_scaled_1e17']])
rho = np.hypot(C[:, 0], C[:, 1])
hubs = np.where(rho < 1 - r)[0]
rings = np.where(rho >= 1 - r)[0]
print("ring indices", rings, "|a| in [%.6f, %.6f]" % (rho[rings].min(), rho[rings].max()))
print("hub  indices", hubs, "|h| =", np.round(rho[hubs], 6))

# --- hole of the ring discs, on a polar grid, and its depth function D(psi)
nth, nd = 2000, 1200
thg = np.linspace(0, 2*np.pi, nth, endpoint=False)
dg = np.linspace(0, 1, nd)
U = np.stack([np.cos(thg), np.sin(thg)], 1)
hole = np.zeros((nth, nd), dtype=bool)
D = np.zeros(nth)          # max |p| with p in hole along direction psi
for i, t in enumerate(thg):
    P = dg[:, None] * U[i]
    dist = np.sqrt(((P[:, None, :] - C[None, rings, :]) ** 2).sum(-1)).min(1)
    out = dist > r
    hole[i] = out
    if out.any():
        D[i] = dg[out].max()
print("\nhole depth D(psi): min=%.6f max=%.6f  (1-2r=%.4f, 3r-1=%.4f)" %
      (D.min(), D.max(), 1-2*r, 3*r-1))
for s in (3*r-1, 0.16, 0.20, 0.24, 0.28, 0.30):
    m = (D >= s).sum() * (2*np.pi/nth)
    print("  measure{psi : D(psi) >= %.3f} = %.6f rad" % (s, m))
print("  total measure{psi: D>0} = %.6f rad" % ((D > 0).sum()*(2*np.pi/nth)))

# --- hub shadow bound: 2 hubs, each |h| in [1-2r, 2r] -> shadow halfwidth <= arcsin(r/(1-2r))
print("\n(1-2r=%.4f)  2*arcsin(r/(1-2r)) = %.6f rad ; 2 hubs = %.6f rad" %
      (1-2*r, 2*np.arcsin(r/(1-2*r)), 4*np.arcsin(r/(1-2*r))))
print("   with |h| >= 1-2r at r=0.38 the bound is *inactive* for r=0.38 (%.3f > measures above)"
      % (4*np.arcsin(r/(1-2*r))))

# --- where is the hole? report the geometry: is the hole a disc around origin?
Hpts = np.array([dg[j]*U[i] for i in range(nth) for j in range(nd) if hole[i, j]])
print("\n|H| samples %d ; |p| range [%.6f, %.6f]" % (len(Hpts), np.hypot(Hpts[:, 0], Hpts[:, 1]).min(),
                                                    np.hypot(Hpts[:, 0], Hpts[:, 1]).max()))
# fit the largest disc centered at origin inside the hole
print("largest disc B(0,s) inside hole: s = %.6f" % D.min())
np.save(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'out_hole_depth.npy'), D)
np.save(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'out_hole_pts.npy'), Hpts)
