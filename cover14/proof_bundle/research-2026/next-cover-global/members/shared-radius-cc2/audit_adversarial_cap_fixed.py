"""
Adversarial test of the universal-cap bound, CORRECTED.

Geometry model (U=1).  Local interface around face f:
  * central triangle vertices u1,u2,u3 with |u_i| = r_i <= 1,
  * the circle through u_i and u_j whose center C_k is at distance T_k<=1 from
    all three of O,u_i,u_j (C_k is the "other endpoint" of the two facets on
    edge u_i u_j, possibly mirror-reflected to the other side),
  * for a circle through O, u_i, u_j with radius T_k, the center satisfies
        C_k = M +- s * perp,   M = (u_i+u_j)/2,  s = sqrt(T_k^2 - |M|^2)
    (equivalently x = T_k, y_k = T_k and the chord is common), so
        |M| <= T_k <= 1.
  * hexagon walk: u1, C1, u2, C2, u3, C3 (C1 for chord u1u2, etc.)
  * quantity of interest: sum of the SIX oriented triangle areas
        A = sum_k [ (O,u_i,C_k) + (O,C_k,u_j) ]
    which equals the shoelace (signed) area of the walk.
  * claim to test:  A <= 3 sqrt(3)/2 = 2.598076211353316  whenever all six
    hexagon side lengths |u_i - C_k|, |C_k - u_j| are <= 1.
"""
import json
import numpy as np

PI = np.pi
rng = np.random.default_rng(20260519)
BOUND = 3 * np.sqrt(3) / 2
PAIRS = [(0, 1), (1, 2), (2, 0)]


def centers(u, T, signs):
    """all centers for given circumradii T and branch signs +-1."""
    C = np.zeros((2, 3))
    for k, (i, j) in enumerate(PAIRS):
        M = 0.5 * (u[:, i] + u[:, j])
        d = float(np.linalg.norm(M))
        if T[k] < d - 1e-12:
            return None
        dv = u[:, j] - u[:, i]
        perp = np.array([-dv[1], dv[0]])
        n = np.linalg.norm(perp)
        if n < 1e-14:
            return None
        perp = perp / n
        C[:, k] = M + signs[k] * np.sqrt(max(T[k] ** 2 - d ** 2, 0.0)) * perp
    return C


def eval_params(a1, a2, a3, r1, r2, r3, T1, T2, T3, signs):
    ang = np.array([a1, a2, a3])
    rad = np.array([r1, r2, r3])
    u = np.stack([rad * np.cos(ang), rad * np.sin(ang)])
    T = np.array([T1, T2, T3])
    C = centers(u, T, signs)
    if C is None:
        return -1e9, None, None
    # realizability: all three radii <= 1 and all six hexagon sides <= 1
    if max(r1, r2, r3, T1, T2, T3) > 1 + 1e-12:
        return -1e9, None, None
    walk = np.array([u[:, 0], C[:, 0], u[:, 1], C[:, 1], u[:, 2], C[:, 2]]).T
    sl = [np.linalg.norm(walk[:, (k + 1) % 6] - walk[:, k]) for k in range(6)]
    if max(sl) > 1 + 1e-9:
        return -1e9, None, None
    x, y = walk[0], walk[1]
    sa = 0.5 * float(np.sum(x * np.roll(y, -1) - np.roll(x, -1) * y))
    return sa, walk, sl


def val(p):
    a1, a2, a3, r1, r2, r3, T1, T2, T3 = p[:9]
    signs = np.sign(p[9:12]) if len(p) > 9 else np.array([1.0, 1.0, 1.0])
    signs = np.where(signs == 0, 1.0, signs)
    return eval_params(a1, a2, a3, r1, r2, r3, T1, T2, T3, signs)


def ascent(p0, sweeps=500, step0=0.4):
    p = np.asarray(p0, float).copy()
    p[3:6] = np.clip(p[3:6], 1e-4, 1.0)
    p[6:9] = np.clip(p[6:9], 1e-4, 1.0)
    p[9:12] = np.where(p[9:12] >= 0, 1.0, -1.0)
    best = val(p)[0]
    step = step0
    for _ in range(sweeps):
        imp = False
        for i in range(12):
            for sg in (1, -1):
                c = p.copy()
                if i < 9:
                    c[i] = c[i] + sg * step
                    if i >= 3:
                        c[i] = min(max(c[i], 1e-4), 1.0)
                    else:
                        c[i] = c[i] % (2 * PI)
                else:
                    c[i] = -c[i]
                v = val(c)[0]
                if v > best * (1 + 1e-13) or (best <= 0 < v):
                    best, p, imp = v, c, True
        if not imp:
            step *= 0.5
            if step < 1e-12:
                break
    return best, p


out = {}
# reference: what does the best "regular-like" configuration give?
# u_i on the unit circle at 120 deg, T_k as large as allowed
best = (-1e9, None)
starts = []
for T in [0.5773502691896258, 0.7, 0.85, 0.99, 1.0]:
    for sg in [(1, 1, 1), (-1, -1, -1), (1, -1, 1)]:
        for r in [1.0, 0.9, 0.7]:
            starts.append(np.concatenate([[0.0, 2 * PI / 3, 4 * PI / 3],
                                          [r] * 3, [T] * 3, np.array(sg, float)]))
for _ in range(800):
    starts.append(np.concatenate([rng.uniform(0, 2 * PI, 3),
                                  rng.uniform(0.3, 1.0, 3),
                                  rng.uniform(0.3, 1.0, 3),
                                  rng.choice([-1.0, 1.0], 3)]))
for s in starts:
    v, p = ascent(s, sweeps=250)
    if v > best[0]:
        best = (v, p)
sa, walk, sl = val(best[1])
out['max_signed_area'] = float(best[0])
out['bound'] = float(BOUND)
out['ratio'] = float(best[0] / BOUND)
out['argmax_params'] = np.asarray(best[1]).tolist()
if walk is not None:
    out['argmax_geometry'] = dict(walk=walk.tolist(), side_lengths=sl,
                                  side_max=float(max(sl)))

# also maximize the ABSOLUTE value and the sum of |areas|
def val_abs(p):
    sa, w, sl = val(p)
    return abs(sa), w, sl


best2 = (-1e9, None)
for s in starts:
    v, p = ascent(s, sweeps=200)
    va = abs(v)
    if va > best2[0]:
        best2 = (va, p)
out['max_abs_signed_area'] = float(best2[0])
out['max_abs_ratio'] = float(best2[0] / BOUND)

# exact reference points
ref = {}
for r, T, sg in [(1.0, 1.0, (1, 1, 1)), (1.0, 1.0, (-1, -1, -1)),
                 (1.0, 0.5773502691896258, (1, 1, 1)), (1.0, 0.9, (1, 1, 1))]:
    p = np.concatenate([[0.0, 2 * PI / 3, 4 * PI / 3], [r] * 3, [T] * 3, np.array(sg, float)])
    sa, w, sl = val(p)
    ref[f"r={r},T={T},sg={sg}"] = dict(sa=sa, side_lengths=sl if sl is None else [round(s, 6) for s in sl])
out['references'] = ref

print(json.dumps(out, indent=1))
with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\adversarial_cap_fixed.json", 'w') as f:
    json.dump(out, f, indent=1)
