"""
DECISIVE: realizable configurations, strict domain, compare both readings of
"sum of the three paired facet areas":

   reading (S)  sum_i [signed area of quad (u_i, A_i, u_{i+1}, O)]  (= shoelace
                of the 6-gon, the lead's identity)
   reading (A)  sum_i [unsigned |quad area|]  (only equals (S) if all quads are
                positively oriented)

Domain per the certificate: three facet triangles each with the central angle
beta_i at O, R = |O u_i| <= U, T_i = |A_i - u_i| <= U, and sum beta_i < 2pi
(the closed surface condition; beta_i are the facet angles at the OTHER
vertices in the real application, but for the local relaxation they are the
angles at O of the three facet triangles).

Search over random realizable configurations (angles, radii, neighbour radii)
via coordinate ascent, maximising (S) and (A), and record the best geometry.
"""
import json
import numpy as np

PI = np.pi
rng = np.random.default_rng(8888)
BOUND = 3 * np.sqrt(3) / 2


def signed_area(poly):
    poly = np.asarray(poly, float)
    x, y = poly[:, 0], poly[:, 1]
    return 0.5 * float(np.sum(x * np.roll(y, -1) - np.roll(x, -1) * y))


def config(betas, R, Ts):
    """u_i on circle radius R with *consecutive* central angles such that the
    three facet triangles are (O,u_i,A_i) etc.  For the local relaxation the
    three facets are independent; here we place u1,u2,u3 on the circle with
    the pairwise angles beta_1 (u1-u2), beta_2 (u2-u3), beta_3 (u3-u1) -- this
    is possible iff the three points can realise those separations, i.e.
    beta_1+beta_2 >= beta_3 etc. and sum <= 2pi.  We place them by trilateration."""
    b1, b2, b3 = betas
    # place u1 at angle 0, u2 at b1, u3 at angle phi with |u1-u3| = 2R sin(b3/2)
    u1 = np.array([R, 0.0])
    u2 = np.array([R * np.cos(b1), R * np.sin(b1)])
    # solve for phi from dot(u1,u3) = R^2 cos b3
    c = np.cos(b3)
    # also need angle(u2,u3) = b2
    phi = None
    for cand in [b1 + b2, b1 - b2, -b1 + b2, 2 * PI - (b1 + b2)]:
        u3 = np.array([R * np.cos(cand), R * np.sin(cand)])
        ang1 = np.arccos(np.clip(np.dot(u1, u3) / R ** 2, -1, 1))
        ang2 = np.arccos(np.clip(np.dot(u2, u3) / R ** 2, -1, 1))
        if abs(ang1 - b3) < 1e-6 and abs(ang2 - b2) < 1e-6:
            phi = cand
            break
    if phi is None:
        return None
    u3 = np.array([R * np.cos(phi), R * np.sin(phi)])
    P = np.array([u1, u2, u3])
    O = np.zeros(2)
    A = []
    for k in range(3):
        i, j = k, (k + 1) % 3
        M = 0.5 * (P[i] + P[j])
        d = np.linalg.norm(M)
        T = Ts[k]
        if T < d - 1e-12:
            return None
        dv = P[j] - P[i]
        perp = np.array([-dv[1], dv[0]])
        perp = perp / np.linalg.norm(perp)
        A.append(M + np.sqrt(max(T ** 2 - d ** 2, 0.0)) * perp)
    return P, np.array(A)


def evaluate(p):
    b1, b2, b3, R, T1, T2, T3 = p
    if min(b1, b2, b3) <= 1e-6 or max(b1, b2, b3) >= PI - 1e-6:
        return None
    if abs(b1 + b2 + b3 - 2 * PI) > 1e-6 and (b1 + b2 + b3) >= 2 * PI:
        return None
    if not (0 < R <= 1) or not all(0 < t <= 1 for t in (T1, T2, T3)):
        return None
    cfg = config((b1, b2, b3), R, (T1, T2, T3))
    if cfg is None:
        return None
    P, A = cfg
    quads = []
    for k in range(3):
        i, j = k, (k + 1) % 3
        quads.append(signed_area(np.array([P[i], A[k], P[j], np.zeros(2)])))
    sum_signed = float(sum(quads))
    sum_abs = float(sum(abs(q) for q in quads))
    walk = []
    for k in range(3):
        walk.append(P[k]); walk.append(A[k])
    walk = np.array(walk)
    shoe = signed_area(walk)
    sl = [float(np.linalg.norm(walk[(k + 1) % 6] - walk[k])) for k in range(6)]
    return dict(sum_signed=sum_signed, sum_abs=sum_abs, shoelace=shoe,
                side_lengths=sl, side_max=max(sl), quads=quads,
                sum_beta=float(b1 + b2 + b3))


def objective(p, mode='S'):
    r = evaluate(p)
    if r is None:
        return -1e9, None
    return (r['sum_signed'] if mode == 'S' else r['sum_abs']), r


def ascent(p0, mode='S', sweeps=400, step0=0.3):
    p = np.asarray(p0, float)
    best, _ = objective(p, mode)
    step = step0
    for _ in range(sweeps):
        imp = False
        for i in range(7):
            for sg in (1, -1):
                c = p.copy()
                c[i] = c[i] + sg * step
                if i >= 3:
                    c[i] = min(max(c[i], 1e-6), 1.0)
                if i == 0:
                    c[i] = c[i] % (2 * PI)
                v, _ = objective(c, mode)
                if v > best * (1 + 1e-13) or (best <= 0 < v):
                    best, p, imp = v, c, True
        if not imp:
            step *= 0.5
            if step < 1e-11:
                break
    return best, p


out = {}
for mode in ['S', 'A']:
    best = (-1e9, None, None)
    starts = [np.array([PI / 3, PI / 3, PI / 3, 1.0, 1.0, 1.0, 1.0]),
              np.array([PI / 2, PI / 2, PI / 2, 1.0, 1.0, 1.0, 1.0]),
              np.array([0.8, 0.8, 1.4, 1.0, 1.0, 1.0, 1.0]),
              np.array([1.0, 1.0, 1.0, 1.0, 0.9, 1.0, 0.95]),
              np.array([PI / 2, PI / 2, PI / 2, 1.0, 0.5, 0.5, 0.5])]
    for _ in range(600):
        b = rng.uniform(0.2, 3.0, 3)
        starts.append(np.concatenate([b, [rng.uniform(0.5, 1.0)],
                                      rng.uniform(0.3, 1.0, 3)]))
    for s in starts:
        v, p = ascent(s, mode)
        if v > best[0]:
            r = evaluate(p)
            best = (v, p, r)
    out[f'best_{mode}'] = dict(value=None if best[0] < -1e8 else float(best[0]),
                               params=None if best[1] is None else np.asarray(best[1]).tolist(),
                               bound=float(BOUND),
                               detail=None if best[2] is None else {k: v for k, v in best[2].items() if k != 'side_lengths'})
    print(mode, json.dumps(out[f'best_{mode}'], default=float)[:900], flush=True)

with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\realizable_max.json", 'w') as f:
    json.dump(out, f, indent=1, default=float)
