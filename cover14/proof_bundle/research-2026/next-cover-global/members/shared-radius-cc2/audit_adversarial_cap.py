"""
Adversarial test of the universal-cap bound in its realizable form.

Constraint set (per the lead's geometry, U = 1):
  * the central triangle has vertices u1,u2,u3 (used only via directions;
    their magnitudes are bounded by U),
  * C_k is the circumcenter of (O, u_i, u_j) realising radius T_k = |C_k| <= U,
    i.e. |C_k - u_i| = |C_k - u_j| = T_k with |u_i| <= U,
  * hexagon edges: u_i -> C_k and C_k -> u_j, all of length <= U.

We maximize  S = sum of the six triangle areas (O,u_i,C_k) and (O,C_k,u_j)
by random search + coordinate ascent over:
  * angles of u1,u2,u3,
  * magnitudes |u_i| in (0,1],
  * T_k in (0,1]  (for the symmetric configuration T_k = |m| + h, h = the
    offset from the midpoint of chord (u_i,u_j));
and compare with 3 sqrt(3)/2 = 2.598076211...
"""
import json
import numpy as np

PI = np.pi
rng = np.random.default_rng(777)
BOUND = 3 * np.sqrt(3) / 2


def config_from(a1, a2, a3, r1, r2, r3, T):
    """a=angles, r=magnitudes of u_i, T=circumradii.
    Circumcenters: C_k = midpoint(u_i,u_j) + h_k * perp, with
    |C_k|^2 = |m|^2 + h_k^2 and T_k^2 = |C_k - u_i|^2 = |m|^2 + h_k^2 + ...
    Take the consistent solution: the center of the circle through O, u_i, u_j
    lies at distance T_k from all three points, so
       C_k = M + s * perp,   M = (u_i+u_j)/2,
       |C_k| = T_k  (since |C_k - O| = T_k)  ->  s = sqrt(T_k^2 - |M|^2)
    and  |C_k - u_i| = T_k automatically.  Branch s>=0 chosen."""
    ang = np.array([a1, a2, a3])
    rad = np.array([r1, r2, r3])
    u = np.stack([rad * np.cos(ang), rad * np.sin(ang)])
    C = np.zeros((2, 3))
    pairs = [(0, 1), (1, 2), (2, 0)]
    for k, (i, j) in enumerate(pairs):
        M = 0.5 * (u[:, i] + u[:, j])
        d = np.linalg.norm(M)
        if T[k] < d:
            return None
        perp = np.array([-(u[1, j] - u[1, i]), (u[0, j] - u[0, i])])
        n = np.linalg.norm(perp)
        if n < 1e-14:
            return None
        perp = perp / n
        C[:, k] = M + np.sqrt(max(T[k] ** 2 - d ** 2, 0.0)) * perp
    return u, C


def areas(u, C):
    O = np.zeros(2)
    t = [
        [O, u[:, 0], C[:, 0]],
        [O, C[:, 0], u[:, 1]],
        [O, u[:, 1], C[:, 1]],
        [O, C[:, 1], u[:, 2]],
        [O, u[:, 2], C[:, 2]],
        [O, C[:, 2], u[:, 0]],
    ]
    return np.array([0.5 * np.cross(np.asarray(b) - np.asarray(a),
                                    np.asarray(c) - np.asarray(a)) for a, b, c in t])


def value(params):
    a1, a2, a3, r1, r2, r3, T1, T2, T3 = params
    cfg = config_from(a1, a2, a3, r1, r2, r3, [T1, T2, T3])
    if cfg is None:
        return -1e9, None
    u, C = cfg
    # realizability checks: all radii <= U =1, all six side lengths <= 1
    if max(r1, r2, r3, T1, T2, T3) > 1 + 1e-12:
        return -1e9, None
    d = min(np.linalg.norm(C[:, 0] - u[:, 0]), np.linalg.norm(C[:, 0] - u[:, 1]),
            np.linalg.norm(C[:, 1] - u[:, 1]), np.linalg.norm(C[:, 1] - u[:, 2]),
            np.linalg.norm(C[:, 2] - u[:, 2]), np.linalg.norm(C[:, 2] - u[:, 0]))
    if d > 1 + 1e-9:
        return -1e9, None
    a = areas(u, C)
    return float(a.sum()), (u, C, a)


def ascent(p0, sweeps=400, step0=0.5):
    p = np.asarray(p0, float).copy()
    p = np.clip(p, 1e-6, None)
    p[3:6] = np.clip(p[3:6], 1e-6, 1.0)
    p[6:9] = np.clip(p[6:9], 1e-6, 1.0)
    best, _ = value(p)
    step = step0
    for _ in range(sweeps):
        imp = False
        for i in range(9):
            for sg in (1, -1):
                c = p.copy()
                c[i] = c[i] + sg * step
                if i >= 3:
                    c[i] = min(max(c[i], 1e-6), 1.0)
                else:
                    c[i] = max(c[i], 1e-6)
                v, _ = value(c)
                if v > best * (1 + 1e-13):
                    best, p, imp = v, c, True
        if not imp:
            step *= 0.5
            if step < 1e-11:
                break
    return best, p


out = {}
# start from a regular-hexagon-like configuration: u_i at 120 deg on radius 1,
# T_k = 1  (that makes C_k on the unit circle -> the regular hexagon)
starts = [np.array([0.0, 2 * PI / 3, 4 * PI / 3, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0]),
          np.array([0.0, 2 * PI / 3, 4 * PI / 3, 0.9, 0.9, 0.9, 0.95, 0.95, 0.95]),
          np.array([0.3, 2.2, 4.4, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0]),
          np.array([0.0, 2 * PI / 3, 4 * PI / 3, 1.0, 1.0, 1.0, 0.99, 0.99, 0.99])]
for _ in range(400):
    starts.append(np.concatenate([rng.uniform(0, 2 * PI, 3),
                                  rng.uniform(0.3, 1.0, 3),
                                  rng.uniform(0.3, 1.0, 3)]))
best = (-1e9, None, None)
for s in starts:
    v, p = ascent(s, sweeps=300)
    if v > best[0]:
        vv, extra = value(p)
        best = (v, p, extra)
out['max_sum6'] = float(best[0])
out['argmax_params'] = np.asarray(best[1]).tolist()
out['bound_3sqrt3_over_2'] = float(BOUND)
out['ratio'] = float(best[0] / BOUND)
if best[2] is not None:
    u, C, a = best[2]
    out['argmax_geometry'] = dict(u=u.tolist(), C=C.tolist(),
                                  six_areas=a.tolist(),
                                  side_lengths=[float(np.linalg.norm(C[:, 0] - u[:, 0])),
                                                float(np.linalg.norm(C[:, 0] - u[:, 1])),
                                                float(np.linalg.norm(C[:, 1] - u[:, 1])),
                                                float(np.linalg.norm(C[:, 1] - u[:, 2])),
                                                float(np.linalg.norm(C[:, 2] - u[:, 2])),
                                                float(np.linalg.norm(C[:, 2] - u[:, 0]))],
                                  T=[float(np.linalg.norm(C[:, k])) for k in range(3)])
# exact regular hexagon reference
uR = np.stack([np.cos(np.array([0, 2 * PI / 3, 4 * PI / 3])),
               np.sin(np.array([0, 2 * PI / 3, 4 * PI / 3]))])
CR = -uR / 2.0                     # circumcenters of (O,u_i,u_j) on unit circle
aR = areas(uR, CR)
out['regular_hexagon_geometry'] = dict(sum6=float(aR.sum()), six_areas=aR.tolist(),
                                       side_lengths=[
                                           float(np.linalg.norm(CR[:, 0] - uR[:, 0])),
                                           float(np.linalg.norm(CR[:, 0] - uR[:, 1])),
                                           float(np.linalg.norm(CR[:, 1] - uR[:, 1])),
                                           float(np.linalg.norm(CR[:, 1] - uR[:, 2])),
                                           float(np.linalg.norm(CR[:, 2] - uR[:, 2])),
                                           float(np.linalg.norm(CR[:, 2] - uR[:, 0]))],
                                       T=[float(np.linalg.norm(CR[:, k])) for k in range(3)])

print(json.dumps(out, indent=1))
with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\adversarial_cap.json", 'w') as f:
    json.dump(out, f, indent=1)
