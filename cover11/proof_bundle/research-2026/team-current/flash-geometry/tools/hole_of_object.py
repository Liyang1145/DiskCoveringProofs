"""The real object: 9 'ring' disks + 2 'hub' disks, r=0.38.
Compute (a) which centers can cover the boundary, (b) the hole H left by the
ring disks, (c) the minimum enclosing ball of cl(H), (d) the 2-centre radius."""
import numpy as np, io, json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

R = 0.38
C = np.array([[-0.272895996459, 0.006668378389],[0.149383897340, -0.003650285444],
              [-0.601004899510, 0.613473162701],[-0.892255389841, 0.021802797907],
              [-0.630250890600, -0.583386685480],[-0.111771859805, -0.691900204080],
              [0.339226041852, -0.682101378580],[0.757189304513, -0.316961250956],
              [0.771766637062, 0.279600290120],[0.372136405079, 0.664718808271],
              [-0.077844643124, 0.696533597950]])
rho = np.hypot(C[:, 0], C[:, 1])
print("|c| =", np.round(rho, 6), "  1-r=0.62, 2r=0.76")
hubs = np.where(rho < 1 - R)[0]
rings = np.where(rho >= 1 - R)[0]
print("hubs (|c|<1-r, cannot reach boundary):", hubs, rho[hubs])
print("rings (centers of 'boundary disks'):", rings, np.round(rho[rings], 6))
print("ring |c| range: [%.6f, %.6f]  ; 2r=%.4f" % (rho[rings].min(), rho[rings].max(), 2*R))

# boundary coverage by ring disks only
th = np.linspace(0, 2*np.pi, 2000001)
P = np.stack([np.cos(th), np.sin(th)], 1)
d2all = ((P[:, None, :] - C[None, :, :])**2).sum(-1)
mn_ring = np.sqrt(d2all[:, rings].min(1))
mn_all = np.sqrt(d2all.min(1))
print("\nboundary: max over |x|=1 of min over RINGS = %.8f  (r=%.4f)" % (mn_ring.max(), R))
k = int(np.argmax(mn_ring)); print("   worst boundary pt of ring-only cover:", np.round(P[k], 6), " angle/pi=%.6f" % (th[k]/np.pi))
print("boundary: max over |x|=1 of min over ALL 11 = %.8f" % mn_all.max())

# hole of the ring disks, sampled on a polar grid: first radius where covered
print("\nHole H = points of D outside all 9 ring disks.")
nth, nd = 720, 400
thg = np.linspace(0, 2*np.pi, nth, endpoint=False)
dg = np.linspace(0, 1, nd)
Hpts = []
for t in thg:
    u = np.array([np.cos(t), np.sin(t)])
    for d in dg:
        p = d*u
        if np.min(np.linalg.norm(C[rings] - p, axis=1)) > R:
            Hpts.append(p)
Hpts = np.array(Hpts)
if len(Hpts):
    print("  sampled hole points: %d ; max |p| = %.6f ; min |p| = %.6f" %
          (len(Hpts), np.hypot(Hpts[:, 0], Hpts[:, 1]).max(), np.hypot(Hpts[:, 0], Hpts[:, 1]).min()))
    from geom import min_enclosing_ball
    c, rr_ = min_enclosing_ball(list(Hpts))
    print("  MEB of sampled hole: centre", np.round(c, 6), " radius %.6f" % rr_)
else:
    print("  no hole at this resolution -> ring disks already cover D?")
