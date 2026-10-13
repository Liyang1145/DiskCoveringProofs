"""
Corrected realizability + sharpness audit of the cap bound  A <= 3 sqrt3/2 U^2.

Assembly (U = 1, R = U, face circumcenter O, face radius R = |u_i| = 1):
  u1,u2,u3 on the circle of radius R about O  (equilateral by construction of
  the face; here we also test non-equilateral placements that still satisfy
  |u_i| <= 1),
  for each chord (u_i,u_j): the two facets on that edge have a common chord,
  so their circumcircles are identical; its center is C_k with |C_k| = T_k <= 1
  and |C_k - u_i| = |C_k - u_j| = T_k.  Mirror reflection chooses the sign.
Quantities:
  * six facet half-areas? -- the full facet triangle area with base = chord and
    apex at the origin is  (1/2)|chord x C_k|  (base chord, apex the center of
    the other circle).  We monitor both this and the shoelace identity.
  * hexagon walk u1,C1,u2,C2,u3,C3 : all six side lengths must be <= 1.
  * bound test: |signed area| <= (1/4)cot(pi/6) * sum side^2 <= 3sqrt3/2.
"""
import json
import numpy as np

PI = np.pi
rng = np.random.default_rng(31415)
BOUND = 3 * np.sqrt(3) / 2
PAIRS = [(0, 1), (1, 2), (2, 0)]


def build(angles, rads, T, signs):
    u = np.stack([np.asarray(rads) * np.cos(np.asarray(angles)),
                  np.asarray(rads) * np.sin(np.asarray(angles))])
    C = np.zeros((2, 3))
    for k, (i, j) in enumerate(PAIRS):
        M = 0.5 * (u[:, i] + u[:, j])
        d = float(np.linalg.norm(M))
        if T[k] < d - 1e-12:
            return None, None
        dv = u[:, j] - u[:, i]
        perp = np.array([-dv[1], dv[0]])
        n = np.linalg.norm(perp)
        if n < 1e-14:
            return None, None
        C[:, k] = M + signs[k] * np.sqrt(max(T[k] ** 2 - d ** 2, 0.0)) * (perp / n)
    return u, C


def measure(angles, rads, T, signs):
    u, C = build(angles, rads, T, signs)
    if C is None:
        return None
    if max(list(T) + list(rads)) > 1 + 1e-12:
        return None
    walk = np.array([u[:, 0], C[:, 0], u[:, 1], C[:, 1], u[:, 2], C[:, 2]]).T
    x, y = walk[0], walk[1]
    sa = 0.5 * float(np.sum(x * np.roll(y, -1) - np.roll(x, -1) * y))
    sl = np.array([np.linalg.norm(walk[:, (k + 1) % 6] - walk[:, k]) for k in range(6)])
    # facet triangle at chord (i,j) with apex the origin: area = 0.5*|u_i x u_j|
    fa = np.array([0.5 * abs(float(np.cross(u[:, i], u[:, j]))) for i, j in PAIRS])
    return dict(sa=sa, sl=sl, fa=fa, u=u, C=C, walk=walk)


out = {}
# --- (1) random realizable configurations: verify the chain
n_bad = 0
worst_ratio = 0.0
worst = None
n_ok = 0
for _ in range(20000):
    if rng.random() < 0.5:
        angles = np.array([0.0, 2 * PI / 3, 4 * PI / 3]) + rng.normal(0, 0.15, 3)
        rads = np.ones(3)
    else:
        angles = rng.uniform(0, 2 * PI, 3)
        rads = rng.uniform(0.4, 1.0, 3)
    T = rng.uniform(0.2, 1.0, 3)
    signs = rng.choice([-1.0, 1.0], 3)
    m = measure(angles, rads, T, signs)
    if m is None or m['sl'].max() > 1 + 1e-9:
        continue
    n_ok += 1
    ss = float((m['sl'] ** 2).sum())
    bd = (1 / 4) / np.tan(PI / 6) * ss
    if abs(m['sa']) > bd + 1e-10:
        n_bad += 1
    r = abs(m['sa']) / BOUND
    if r > worst_ratio:
        worst_ratio = r
        worst = dict(sa=m['sa'], ss=ss, bd=bd, sl=m['sl'].tolist())
out['random_configs'] = dict(n_ok=n_ok, n_bound_violations=n_bad,
                            worst_ratio_vs_3sqrt3over2=float(worst_ratio),
                            worst=worst)

# --- (2) exact sharpness: regular hexagon  (u_k and C_k alternate on unit circle)
angles = np.array([0.0, 2 * PI / 3, 4 * PI / 3])
rads = np.ones(3)
T = np.full(3, 1.0)
for signs in [(-1.0, -1.0, -1.0), (1.0, 1.0, 1.0)]:
    m = measure(angles, rads, T, signs)
    if m is not None and m['sl'].max() <= 1 + 1e-9:
        out[f'unit_circle_hexagon_signs{signs}'] = dict(
            signed_area=float(m['sa']), side_lengths=m['sl'].tolist(),
            sum_sq=float((m['sl'] ** 2).sum()),
            bound_used=float((1 / 4) / np.tan(PI / 6) * (m['sl'] ** 2).sum()),
            ratio_to_3sqrt3over2=float(abs(m['sa']) / BOUND))

# --- (3) the special T = 1/sqrt(3) configuration (circumcenter of equilateral)
m3 = measure(angles, rads, np.full(3, 1 / np.sqrt(3)), (1.0, 1.0, 1.0))
if m3 is not None:
    out['T_equilateral_circumcenter'] = dict(signed_area=float(m3['sa']),
                                             side_lengths=m3['sl'].tolist(),
                                             T=float(1 / np.sqrt(3)))

# --- (4) does the six-triangle sum equal the shoelace area? (orientation test)
def six_area_sum(u, C):
    t = [[np.zeros(2), u[:, 0], C[:, 0]], [np.zeros(2), C[:, 0], u[:, 1]],
         [np.zeros(2), u[:, 1], C[:, 1]], [np.zeros(2), C[:, 1], u[:, 2]],
         [np.zeros(2), u[:, 2], C[:, 2]], [np.zeros(2), C[:, 2], u[:, 0]]]
    return sum(0.5 * float(np.cross(np.asarray(b) - np.asarray(a),
                                    np.asarray(c) - np.asarray(a))) for a, b, c in t)


diffs = []
for _ in range(3000):
    angles = rng.uniform(0, 2 * PI, 3)
    rads = rng.uniform(0.3, 1.0, 3)
    T = rng.uniform(0.2, 1.0, 3)
    signs = rng.choice([-1.0, 1.0], 3)
    u, C = build(angles, rads, T, signs)
    if C is None:
        continue
    walk = np.array([u[:, 0], C[:, 0], u[:, 1], C[:, 1], u[:, 2], C[:, 2]]).T
    x, y = walk[0], walk[1]
    sa = 0.5 * float(np.sum(x * np.roll(y, -1) - np.roll(x, -1) * y))
    diffs.append(six_area_sum(u, C) - sa)
out['cancellation_identity'] = dict(max_abs_diff=float(np.max(np.abs(diffs))),
                                    holds=bool(np.max(np.abs(diffs)) < 1e-10),
                                    n=int(len(diffs)))
print(json.dumps(out, indent=1))
with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\cap_audit_final.json", 'w') as f:
    json.dump(out, f, indent=1)
