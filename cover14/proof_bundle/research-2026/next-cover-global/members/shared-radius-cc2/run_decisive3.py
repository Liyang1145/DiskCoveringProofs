import json
import sys
import numpy as np
sys.path.insert(0, r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2")
import direct_full as DF
import envelope_clean as EC

PI = DF.PI
rng = np.random.default_rng(31337)
out = {}

# ---- (A) global search with the fully corrected direct solver
best = DF.global_search(seed=2027, n_restart=400, nx=201)
out['A_direct_global'] = dict(A=float(best[0]), beta=np.asarray(best[1]).tolist(),
                              x=float(best[2]), y=np.asarray(best[3]).tolist(),
                              Bsum=float(np.sum(best[1])))
print('A', json.dumps(out['A_direct_global']), flush=True)

# targeted asymmetric sweep, sum in [pi, 2pi), dense, inner_max cheap version
# (x_hi found by bisection on sum theta = pi for y=1)
def x_hi_y1(beta, iters=90):
    beta = np.asarray(beta, float)
    one = np.ones(3)
    lo, hi = 1e-9, 1.0
    f = lambda x: DF.theta(beta, x, one).sum() - PI
    if f(1.0) >= 0:
        return 1.0
    if f(lo) < 0:
        return 0.0
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        if f(mid) >= 0:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)

def val_y1(beta):
    beta = np.asarray(beta, float)
    if beta.sum() >= 2 * PI:
        return 0.0
    x = x_hi_y1(beta)
    if x <= 0:
        return 0.0
    if not DF.theta_ok(beta, x, np.ones(3)):
        return 0.0
    return x * float(np.sin(beta).sum())

grid_best = (0.0, None)
for b1 in np.linspace(0.05, PI - 0.05, 120):
    for b2 in np.linspace(0.05, PI - 0.05, 120):
        b3 = PI - b1 - b2
        if not (0.05 < b3 < PI - 0.05):
            continue
        v = val_y1([b1, b2, b3])
        if v > grid_best[0]:
            grid_best = (v, [b1, b2, b3])
# also grid over sums > pi
for b1 in np.linspace(0.05, PI - 0.05, 90):
    for b2 in np.linspace(0.05, PI - 0.05, 90):
        b3 = 2 * PI - 0.3 - b1 - b2
        if not (0.05 < b3 < PI - 0.05):
            continue
        v = val_y1([b1, b2, b3])
        if v > grid_best[0]:
            grid_best = (v, [b1, b2, b3])
out['A_grid_junction_and_high_sum'] = dict(A=float(grid_best[0]),
                                           beta=list(map(float, grid_best[1])),
                                           Bsum=float(np.sum(grid_best[1])))
print('grid', json.dumps(out['A_grid_junction_and_high_sum']), flush=True)

# Monte-Carlo over the whole domain with local polish
def polish(b, step0=0.05):
    b = np.asarray(b, float)
    best = val_y1(b)
    step = step0
    for _ in range(200):
        imp = False
        for i in range(3):
            for sg in (1, -1):
                c = b.copy()
                c[i] = min(max(c[i] + sg * step, 1e-6), PI - 1e-6)
                if c.sum() >= 2 * PI - 1e-9:
                    continue
                v = val_y1(c)
                if v > best * (1 + 1e-13):
                    best, b, imp = v, c, True
        if not imp:
            step *= 0.5
            if step < 1e-10:
                break
    return best, b

mc = (0.0, None)
for _ in range(4000):
    u = np.clip(rng.dirichlet(np.ones(3)) * rng.uniform(0.2, 6.28), 1e-6, PI - 1e-6)
    if u.sum() >= 2 * PI - 1e-9:
        continue
    v, b = polish(u)
    if v > mc[0]:
        mc = (v, b)
out['A_mc_polished'] = dict(A=float(mc[0]), beta=mc[1].tolist(), Bsum=float(mc[1].sum()))
print('mc', json.dumps(out['A_mc_polished']), flush=True)

# ---- (B) tangent-majorant test at the lead's candidate
beta0 = np.array([0.9223829833, 1.1925065472, 1.1925065472])
A0 = val_y1(beta0)
h = 1e-6
g = np.zeros(3)
for i in range(3):
    e = np.zeros(3); e[i] = h
    bp, bm = beta0 + e, beta0 - e
    g[i] = (val_y1(bp) - val_y1(bm)) / (2 * h)
out['B_grad'] = dict(A0=A0, grad=g.tolist(), spread=float(g.max() - g.min()),
                     mean=float(g.mean()))
print('grad', json.dumps(out['B_grad']), flush=True)

def excess(b, v, d):
    b = np.asarray(b, float)
    if b.sum() >= 2 * PI - 1e-12:
        return -np.inf
    return (v * b.sum() + d) - val_y1(b)

# tangent plane at beta0 (as a function of beta only; its normal is g)
tb = (-np.inf, None)
for _ in range(6000):
    u = np.clip(rng.dirichlet(np.ones(3)) * rng.uniform(0.2, 6.28), 1e-6, PI - 1e-6)
    if u.sum() >= 2 * PI - 1e-9:
        continue
    e = A0 + float(g @ (u - beta0)) - val_y1(u)
    if e > tb[0]:
        tb = (e, u)
b = np.asarray(tb[1], float).copy()
step = 0.05
for _ in range(600):
    imp = False
    for i in range(3):
        for sg in (1, -1):
            c = b.copy()
            c[i] = min(max(c[i] + sg * step, 1e-6), PI - 1e-6)
            if c.sum() >= 2 * PI - 1e-9:
                continue
            e = A0 + float(g @ (c - beta0)) - val_y1(c)
            if e > tb[0]:
                tb, b, imp = (e, c), c, True
    if not imp:
        step *= 0.5
        if step < 1e-11:
            break
out['B_tangent_max_excess'] = dict(excess=float(tb[0]), argmax=b.tolist(),
                                   A0=A0)
print('tangent', json.dumps(out['B_tangent_max_excess']), flush=True)

# diagonal test of the same tangent
diag_excess = np.empty(0)
ts = np.linspace(1e-6, 2 * PI / 3 - 1e-9, 300001)
de = A0 + (g.sum()) * (ts - beta0.sum() / 3) - np.array([val_y1([t, t, t]) for t in ts[::1]])
i = int(np.argmax(de))
out['B_tangent_on_diag'] = dict(max=float(de.max()), t_at=float(ts[i]),
                                at_pi3=float(A0 + g.sum() * (PI / 3 - beta0.sum() / 3)
                                             - val_y1([PI / 3] * 3)),
                                at_pi2=float(A0 + g.sum() * (PI / 2 - beta0.sum() / 3)
                                             - val_y1([PI / 2] * 3)))
print('tangent diag', json.dumps(out['B_tangent_on_diag']), flush=True)

# ---- (C) best affine majorants: pure "3 sin(S/3)" bound check + tightness
tt = np.linspace(1e-6, 2 * PI / 3 - 1e-9, 300001)
S = 3 * tt
bound = 3 * np.sin(S / 3)
val = np.array([val_y1([t, t, t]) for t in tt])
out['C_jensen_bound_on_diag'] = dict(max_gap=float(np.max(bound - val)),
                                     at_pi3=float(3 * np.sin(PI / 3) - val_y1([PI / 3] * 3)),
                                     global_bound_value=float(3 * np.sin(PI / 2)))
best_gap = (-1.0, None)
for _ in range(3000):
    u = np.clip(rng.dirichlet(np.ones(3)) * rng.uniform(0.2, 6.28), 1e-6, PI - 1e-6)
    if u.sum() >= 2 * PI - 1e-9:
        continue
    gap = 3 * np.sin(u.sum() / 3) - val_y1(u)
    if gap > best_gap[0]:
        best_gap = (gap, u)
out['C_jensen_gap_random'] = dict(max_gap=float(best_gap[0]), argmax=best_gap[1].tolist())
print('C', json.dumps(out['C_jensen_gap_random']), flush=True)

with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\decisive3.json", 'w') as f:
    json.dump(out, f, indent=1, default=float)
print('DONE')
