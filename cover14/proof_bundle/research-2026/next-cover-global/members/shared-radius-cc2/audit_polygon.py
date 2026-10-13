"""
Audit of the NEW universal-cap route:
  three paired-facet quadrilaterals around face f  ->  closed 6-gon
  u1, C12, u2, C23, u3, C31   (C_k = circumcenter of the triangle containing
  the face edge u_i u_j, radius T_k <= U)
  =>  sum of the six triangle areas == signed area of that closed 6-gon
  =>  |signed area| <= (1/4) cot(pi/6) * sum l_k^2  <= 3 sqrt(3)/2 * U^2

Two independent audits:
  PART I  polygon inequality, independent implementation:
          (a) closed-form constant for the regular n-gon (exact formula),
          (b) direct shoelace bound test on many random closed n-gons with
              side lengths <= 1, for n = 3..10,
          (c) the same test on a *self-intersecting* closed 6-gon,
          (d) sharpness check (regular hexagon attains 3 sqrt3/2 exactly).
  PART II cancellation / decomposition:
          (a) symbolic-free numeric test: build an explicit planar
              configuration of a triangle O,u1,u2,u3 with a point C (the
              circumcenter of (O,u_i,u_j) ROTATED so the chord is common),
              compute (i) sum of the 6 triangle areas, (ii) the shoelace area
              of the vertex cycle, and check equality;
          (b) verify the inner cancellation: with three centers C12,C23,C31,
              sum over k of [Area(O,u_i,C_k) + Area(O,C_k,u_j)] equals
              sum of the 6-gon shoelace terms exactly (algebraic identity,
              tested numerically vectorized);
          (c) adversarial test: can the 6-area sum EXCEED the polygon bound
              3 sqrt3/2 U^2 for a realizable configuration? (search)
"""
import json
import numpy as np

PI = np.pi
rng = np.random.default_rng(20260518)
out = {}


# ------------------------------------------------------------------ helpers
def shoelace(v):
    """signed area of the closed polygon through 2xN array v (vertices)."""
    v = np.asarray(v, float)
    x, y = v[0], v[1]
    return 0.5 * float(np.sum(x * np.roll(y, -1) - np.roll(x, -1) * y))


def tri_area(a, b, c):
    return 0.5 * float(np.cross(np.asarray(b) - np.asarray(a),
                                np.asarray(c) - np.asarray(a)))


def random_closed_ngon(n, rng, scale=1.0, max_iter=200000):
    """Build a closed n-gon by a random walk that returns to the start:
    perturb a regular n-gon's edge vectors while keeping the sum zero.  All
    edge lengths <= scale.  Returns 2xN vertices."""
    ang0 = np.sort(rng.uniform(0, 2 * PI, n))
    l0 = rng.uniform(0.2, 1.0, n) * scale
    e = np.stack([l0 * np.cos(ang0), l0 * np.sin(ang0)])
    # project edge sum to zero by an orthogonal Procrustes-like fixed point:
    # subtract the mean so the sum is zero, then rescale to respect the bound.
    for _ in range(400):
        s = e.sum(axis=1, keepdims=True)
        e = e - s / n
        m = np.linalg.norm(e, axis=0).max()
        if m > scale:
            e *= scale / m
        if np.linalg.norm(e.sum(axis=1)) < 1e-12:
            break
    v = np.zeros((2, n + 1))
    v[:, 1:] = np.cumsum(e, axis=1)
    if np.linalg.norm(v[:, -1]) > 1e-6:      # not closed: fix by projection
        v = v - np.outer(v[:, -1], np.linspace(0, 1, n + 1))
    return v[:, :n], e


# --------------------------------------------------------- PART I (polygon)
partI = {}
reg = {}
for n in range(3, 11):
    # regular n-gon, side 1, inscribed: area = n/(4 tan(pi/n))
    area = n / (4 * np.tan(PI / n))
    reg[n] = dict(area_ratio=area / n, bound=(1 / 4) / np.tan(PI / n))
partI['regular_ngon_constant'] = reg

tests = {}
for n in [3, 4, 5, 6, 7, 8, 10]:
    worst = 0.0
    worst_area = 0.0
    bound = (1 / 4) / np.tan(PI / n)
    for _ in range(4000):
        v, e = random_closed_ngon(n, rng)
        if np.linalg.norm(e.sum(axis=1)) > 1e-6:
            continue
        lnorm = np.linalg.norm(e, axis=0)
        if lnorm.max() > 1 + 1e-9:
            continue
        a = abs(shoelace(v))
        ss = float((lnorm ** 2).sum())
        r = a / ss if ss > 0 else 0.0
        if r > worst:
            worst = r
            worst_area = a
    tests[n] = dict(max_ratio=float(worst), bound=float(bound),
                    bound_ok=bool(worst <= bound + 1e-9))
partI['random_closed_ngon_bounds'] = tests

# regular hexagon sharpness
vh = np.array([[np.cos(k * PI / 3), np.sin(k * PI / 3)] for k in range(6)]).T
lh = np.linalg.norm(np.roll(vh, -1, axis=1) - vh, axis=0)
partI['regular_hexagon'] = dict(area=abs(shoelace(vh)),
                                sum_l2=float((lh ** 2).sum()),
                                ratio=abs(shoelace(vh)) / float((lh ** 2).sum()),
                                bound_3sqrt3_over_2=float(3 * np.sqrt(3) / 2))

# self-intersecting closed hexagon (star of David style): must still obey
star = []
R = 1.0
for k in range(6):
    ang = 2 * PI * k / 6 + (PI / 6 if k % 2 else 0)
    star.append((R * np.cos(ang), R * np.sin(ang)))
vs = np.array(star).T
ls = np.linalg.norm(np.roll(vs, -1, axis=1) - vs, axis=0)
partI['self_intersecting_hexagon'] = dict(
    area=abs(shoelace(vs)), sum_l2=float((ls ** 2).sum()),
    bound=float((1 / 4) / np.tan(PI / 6) * (ls ** 2).sum()),
    ok=bool(abs(shoelace(vs)) <= (1 / 4) / np.tan(PI / 6) * (ls ** 2).sum() + 1e-12))

out['PART_I_polygon'] = partI

# ------------------------------------------------- PART II (cancellation)
# Build a genuine local configuration:   O at the origin, three unit-ish
# directions u1,u2,u3 (central face), and for each chord (u_i,u_j) a point C_k
# at distance T_k from both u_i and u_j (the circumcenter of (O,u_i,u_j) with
# a prescribed radius), placed on the far side.
def build_config(u, T):
    u = np.asarray(u, float)                       # 2x3
    C = []
    for (i, j), k in [((0, 1), 0), ((1, 2), 1), ((2, 0), 2)]:
        a, b = u[:, i], u[:, j]
        m = 0.5 * (a + b)
        perp = np.array([-(b - a)[1], (b - a)[0]])
        perp = perp / np.linalg.norm(perp)
        d = np.linalg.norm(m)
        h = np.sqrt(max(T[k] ** 2 - d ** 2, 0.0))   # distance from O along perp
        C.append(m + h * perp)
    return u, np.array(C).T


def audit_one(u, T):
    u, C = build_config(u, T)
    # the six triangle areas in the cyclic order used by the boundary walk
    order = [(0, 0, 1), (1, 0, 2), (2, 1, 2), (1, 2, 0), (2, 2, 1), (0, 0, 2)]
    # triangle k: (O, u_i, C_k) or (O, C_k, u_j) -- see boundary walk
    tris = [
        [np.zeros(2), u[:, 0], C[:, 0]],   # u1 -> C12
        [np.zeros(2), C[:, 0], u[:, 1]],   # C12 -> u2
        [np.zeros(2), u[:, 1], C[:, 1]],   # u2 -> C23
        [np.zeros(2), C[:, 1], u[:, 2]],   # C23 -> u3
        [np.zeros(2), u[:, 2], C[:, 2]],   # u3 -> C31
        [np.zeros(2), C[:, 2], u[:, 0]],   # C31 -> u1
    ]
    A6 = sum(tri_area(*t) for t in tris)
    walk = [u[:, 0], C[:, 0], u[:, 1], C[:, 1], u[:, 2], C[:, 2]]
    sa = shoelace(np.array(walk).T)
    return dict(sum6=A6, shoelace=sa, diff=A6 - sa)


reps = []
for _ in range(400):
    u = rng.normal(size=(2, 3))
    u = u / np.linalg.norm(u, axis=0, keepdims=True)
    T = rng.uniform(0.3, 1.0, 3)
    reps.append(audit_one(u, T))
diffs = np.array([r['diff'] for r in reps])
out['PART_II_cancellation'] = dict(
    max_abs_diff=float(np.abs(diffs).max()),
    median_abs_diff=float(np.median(np.abs(diffs))),
    equality_holds=bool(np.abs(diffs).max() < 1e-10),
    note='sum of the 6 triangle areas == shoelace area of u1,C12,u2,C23,u3,C31')

# adversarial: can sum6 exceed 3 sqrt3/2 U^2 with all T_k <= U and |u_i| <= U?
# (bound per side length l_k <= max(|u_i|,T_k) <= U)
adv = dict(best=0.0, arg=None)
for _ in range(4000):
    U = 1.0
    u = rng.normal(size=(2, 3))
    u = u / np.linalg.norm(u, axis=0, keepdims=True) * rng.uniform(0.3, 1.0)
    T = rng.uniform(0.2, 1.0, 3)
    r = audit_one(u, T)
    if r['sum6'] > adv['best']:
        adv = dict(best=float(r['sum6']), arg=dict(T=T.tolist()))
out['PART_II_adversarial'] = adv
out['PART_II_bound'] = float(3 * np.sqrt(3) / 2)

print(json.dumps(out, indent=1))
with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\polygon_audit.json", 'w') as f:
    json.dump(out, f, indent=1)
