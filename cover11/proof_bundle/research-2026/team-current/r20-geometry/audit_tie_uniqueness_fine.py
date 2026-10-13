"""r20-geometry: corrected adversarial search for the tie-uniqueness hypothesis.

Corrected parameterization (the previous version erroneously allowed rU1 != rU2, i.e. U not
equidistant, hence U not a tie):
   U on the unit circle (take U = (1,0)), ring radius r = 1/2, s = sqrt(1-r^2).
   BOTH centres at distance rU <= r from U (so U is a common covered tie):
        c_k = U - rU (cos phi_k, sin phi_k),  |phi_k| <= acos(r)  (else c_k outside B(0,s)).
   d = |c_1-c_2|, k = sqrt(r^2-d^2/4), radical line m + t n (orientation: U = m + t_+ n),
   V = m + t_- n,  F = max(|V-c_1|, |V-c_2|) - r.
   F <= 0  <=>  the second crossing V is covered by both disks
           <=>  the tie in the common overlap is NOT unique (mechanism hypothesis fails)
           <=>  t_- >= -k, i.e. p_in = m - k n is NOT in int D.
Also screened: G = m.n (the sign that controls t_-+k), and disc - k^2.
"""
import json, math, random
import numpy as np
from scipy.optimize import minimize

r = 0.5
s = math.sqrt(1 - r * r)
U = np.array([1.0, 0.0])
amax = math.acos(r)                      # admissible |phi|

rng = random.Random(11)


def geom(rU, phi1, phi2):
    if not (0 < rU <= r):
        return None
    c1 = U - rU * np.array([math.cos(phi1), math.sin(phi1)])
    c2 = U - rU * np.array([math.cos(phi2), math.sin(phi2)])
    if np.linalg.norm(c1) > s + 1e-15 or np.linalg.norm(c2) > s + 1e-15:
        return None
    d = np.linalg.norm(c2 - c1)
    if d <= 1e-9 or d >= 2 * r:
        return None
    m = 0.5 * (c1 + c2)
    n = np.array([-(c2 - c1)[1], (c2 - c1)[0]]) / d
    k = math.sqrt(r * r - d * d / 4)
    mn = m @ n
    disc = mn * mn - (m @ m) + 1
    if disc <= 0:
        return None
    roots = [-mn + math.sqrt(disc), -mn - math.sqrt(disc)]
    tU = (U - m) @ n
    if tU < 0:
        n = -n
        roots = [-x for x in roots]
        tU = -tU
    tp, tm = max(roots), min(roots)
    V = m + tm * n
    F = max(np.linalg.norm(V - c1), np.linalg.norm(V - c2)) - r
    return dict(F=F, d=d, k=k, mn=mn, tm=tm, tp=tp, tU=tU, disc_minus_k2=disc - k * k,
                c1=c1, c2=c2, n=n, m=m, pin=m - k * n, pout=m + k * n,
                nin=np.linalg.norm(m - k * n), nout=np.linalg.norm(m + k * n))


def obj(v):
    g = geom(v[0], v[1], v[2])
    return 1e3 if g is None else g["F"]


best = None
START = 60
for kk in range(START):
    rU = rng.uniform(1e-3, r)
    p1 = rng.uniform(-amax, amax)
    p2 = rng.uniform(-amax, amax)
    res = minimize(obj, [rU, p1, p2], method="Nelder-Mead",
                   options=dict(maxiter=1200, xatol=1e-13, fatol=1e-15))
    g = geom(*res.x)
    if g is None:
        continue
    if best is None or g["F"] < best[0]:
        best = (g["F"], res.x.copy(), g)

F, x, g = best
print("corrected search: %d local starts, min F = %.6e" % (START, F))
print("   worst point rU=%.6f phi1=%.6f phi2=%.6f ; d=%.6f k=%.6f m.n=%+.6f disc-k^2=%+.3e"
      % (x[0], x[1], x[2], g["d"], g["k"], g["mn"], g["disc_minus_k2"]))
print("   t_+ = %+.6f (t_+-k = %+.3e) ; t_- = %+.6f (t_-+k = %+.6e)"
      % (g["tp"], g["tp"] - g["k"], g["tm"], g["tm"] + g["k"]))
print("   |p_in| = %.6f  |p_out| = %.6f   (p_in in int D: %s)"
      % (g["nin"], g["nout"], g["nin"] < 1))

# coarse deterministic screen with the corrected parameterization
grid = (1e9, None, None)
for i1 in range(0, 61):
    for i2 in range(0, 61):
        for j in range(0, 11):
            p1 = -amax + 2 * amax * i1 / 60
            p2 = -amax + 2 * amax * i2 / 60
            rU = r * (j + 1) / 11
            gg = geom(rU, p1, p2)
            if gg is None:
                continue
            if gg["F"] < grid[0]:
                grid = (gg["F"], (rU, p1, p2), gg)
print("grid screen (61x61x11 points): min F = %.6e at %s" % (grid[0], tuple(round(q, 4) for q in grid[1])))

# structural checks over the same admissible set (do the two sufficient conditions hold?)
mn_min = 1e9
disc_min = 1e9
for i1 in range(0, 31):
    for i2 in range(0, 31):
        for j in range(0, 6):
            p1 = -amax + 2 * amax * i1 / 30
            p2 = -amax + 2 * amax * i2 / 30
            rU = r * (j + 1) / 6
            gg = geom(rU, p1, p2)
            if gg is None:
                continue
            mn_min = min(mn_min, gg["mn"])
            disc_min = min(disc_min, gg["disc_minus_k2"])
print("over the admissible grid: min(m.n) = %+.6f  min(disc-k^2) = %+.3e" % (mn_min, disc_min))
json.dump(dict(local_min_F=float(F), local_x=[float(q) for q in x],
               grid_min_F=float(grid[0]), grid_x=[float(q) for q in grid[1]],
               min_mn=float(mn_min), min_disc_minus_k2=float(disc_min),
               note="F>0 <=> tie in the common overlap is unique and p_in in int D"),
          open("audit_tie_uniqueness_fine.json", "w"), indent=1)
print("\nwrote audit_tie_uniqueness_fine.json")
