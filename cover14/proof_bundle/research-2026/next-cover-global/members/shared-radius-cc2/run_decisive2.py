"""
Decisive run 2.

(a) dense global search for  sup_beta x0(beta) * sum sin(beta_i)
    over 0<beta_i<pi, Bsum<2pi.
(b) same search for the y=1 direct maximum (independent code path).
(c) tangent / affine-majorant test for the lead's candidate beta0:
      f(beta) = [A(beta0) + g . (beta-beta0)] - A(beta)
    maximize f over the domain; f = 0 at beta0 always; f > 0 anywhere means
    the tangent does NOT majorize globally.
    g = grad A(beta0), computed by central differences (and cross-checked
    against the Lagrange prediction cos(beta_i) = lambda x0).
(d) best *diagonal-slice* affine majorant (diag(t) = A(t,t,t)) and its global
    test -- the lead's "linear tangent" experiment.
"""
import json
import sys
import time
import numpy as np

sys.path.insert(0, r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2")
import envelope_clean as EC
import direct_corrected as DC

PI = EC.PI
rng = np.random.default_rng(20260301)
out = {}


def env(b):
    b = np.asarray(b, float)
    return float(EC.A_of_beta(b.reshape(3, 1), 'theorem')[0][0])


def env_batch(betas):
    return EC.A_of_beta(np.asarray(betas, float).T, 'theorem')[0]


# ---------------------------------------------------------- (a) global search
def ascent(b0, sweeps=300, step0=0.35):
    b = np.clip(np.asarray(b0, float), 1e-7, PI - 1e-7)
    if b.sum() >= 2 * PI - 1e-9:
        b = b * (2 * PI - 1e-6) / b.sum()
    best = env(b)
    step = step0
    for _ in range(sweeps):
        imp = False
        for i in range(3):
            for sg in (1, -1):
                c = b.copy()
                c[i] = min(max(c[i] + sg * step, 1e-7), PI - 1e-7)
                if c.sum() >= 2 * PI - 1e-9:
                    continue
                v = env(c)
                if v > best * (1 + 1e-14):
                    best, b, imp = v, c, True
        if not imp:
            step *= 0.5
            if step < 1e-12:
                break
    return best, b


starts = [[PI / 3] * 3, [PI / 2] * 3, [1.0] * 3, [0.5] * 3, [1.4] * 3,
          [2 * PI / 3 - 1e-6] * 3, [0.9, 1.2, 1.2], [2.0, 0.6, 0.6],
          [1.5, 1.5, 0.5], [2.5, 0.4, 0.4], [1.05, 1.05, 1.05],
          [PI - 1e-6, 0.5, 0.5], [0.6, 0.6, 2.0]]
gb = (-1.0, None)
for s in starts:
    v, b = ascent(s)
    if v > gb[0]:
        gb = (v, b)
for _ in range(600):
    if rng.random() < 0.5:
        u = rng.dirichlet(np.ones(3)) * 2 * PI * 0.99
    else:
        u = np.full(3, PI / 3) + rng.normal(0, 0.25, 3)
    u = np.clip(u, 1e-6, PI - 1e-6)
    if u.sum() >= 2 * PI - 1e-9:
        u = u * (2 * PI - 1e-6) / u.sum()
    v, b = ascent(u, sweeps=200)
    if v > gb[0]:
        gb = (v, b)
out['a_envelope_global'] = dict(max=float(gb[0]), beta=gb[1].tolist(),
                                Bsum=float(gb[1].sum()),
                                x0=float(EC.x0_theorem(gb[1])),
                                value_3sqrt3_over_2=float(3 * np.sqrt(3) / 2),
                                gap_to_3sqrt3_over_2=float(3 * np.sqrt(3) / 2 - gb[0]))
print('(a)', json.dumps(out['a_envelope_global'], indent=1), flush=True)

# ------------------------------------- (b) independent y=1 direct code path
best_b = (-1.0, None)
cands = [gb[1]] + [np.array(s) for s in starts]
for c in cands:
    A, x, y, ok = DC.A_direct_full(c)
    if ok and A > best_b[0]:
        best_b = (A, c)
for _ in range(60):
    u = np.clip(rng.dirichlet(np.ones(3)) * 2 * PI * 0.99, 1e-6, PI - 1e-6)
    if u.sum() >= 2 * PI - 1e-9:
        continue
    A, x, y, ok = DC.A_direct_full(u)
    if ok and A > best_b[0]:
        best_b = (A, u)
out['b_direct_global'] = dict(max=float(best_b[0]), beta=np.asarray(best_b[1]).tolist())
print('(b)', json.dumps(out['b_direct_global'], indent=1), flush=True)

# ------------------------------------------------- (c) tangent-majorant test
beta0 = np.array([0.9223829833, 1.1925065472, 1.1925065472])
A0 = env(beta0)
h = 1e-6
g = np.zeros(3)
for i in range(3):
    e = np.zeros(3)
    e[i] = h
    g[i] = (env(beta0 + e) - env(beta0 - e)) / (2 * h)
# Lagrange prediction: grad A = lambda*(1,1,1) at a stationary point
lam_pred = g[0]
out['c_tangent'] = dict(beta0=beta0.tolist(), A0=A0, grad=g.tolist(),
                        grad_spread=float(g.max() - g.min()),
                        lambda_pred=float(lam_pred),
                        cos_beta0=np.cos(beta0).tolist(),
                        cos_over_x0=[float(np.cos(beta0[i]) / EC.x0_theorem(beta0)[0]) for i in range(3)])


def tangent_excess(b):
    b = np.clip(np.asarray(b, float), 1e-9, PI - 1e-9)
    if b.sum() >= 2 * PI - 1e-12:
        return -np.inf
    return A0 + float(g @ (b - beta0)) - env(b)


tb = (-np.inf, None)
for _ in range(4000):
    if rng.random() < 0.5:
        u = rng.dirichlet(np.ones(3)) * rng.uniform(0.2, 6.28)
    else:
        u = beta0 + rng.normal(0, 0.4, 3)
    u = np.clip(u, 1e-6, PI - 1e-6)
    if u.sum() >= 2 * PI - 1e-9:
        continue
    v = tangent_excess(u)
    if v > tb[0]:
        tb = (v, u)
# local ascent on the excess
b = np.asarray(tb[1], float).copy()
step = 0.2
for _ in range(500):
    imp = False
    for i in range(3):
        for sg in (1, -1):
            c = b.copy()
            c[i] = min(max(c[i] + sg * step, 1e-7), PI - 1e-7)
            if c.sum() >= 2 * PI - 1e-9:
                continue
            v = tangent_excess(c)
            if v > tb[0]:
                tb, b, imp = (v, c), c, True
    if not imp:
        step *= 0.5
        if step < 1e-12:
            break
# also check along the diagonal explicitly (closed form)
ts = np.linspace(1e-7, PI - 1e-7, 200001)
diag_excess = A0 + (g.sum()) * (ts - (beta0.sum() / 3)) - 3 * np.sin(ts)
out['c_tangent'].update(dict(
    max_excess_sampled=float(tb[0]), argmax=tb[1].tolist(),
    excess_at_diag_pi3=float(A0 + g.sum() * (PI / 3 - beta0.sum() / 3) - 3 * np.sin(PI / 3)),
    max_excess_on_diag=float(diag_excess.max()),
    argmax_diag_t=float(ts[int(np.argmax(diag_excess))]),
))
print('(c)', json.dumps(out['c_tangent'], indent=1), flush=True)

# ---------------------------- (d) best diagonal-slice affine majorant, tested
# diag(t) = A(t,t,t) = 3 sin t for t <= pi/3, and x0(t)*3 sin t for t > pi/3.
# Build affine L(t)=v t + d that majorizes diag on (0, 2pi/3) and minimizes
# max_beta [L(Bsum) or L(sum/...)] -- we test two natural choices globally.
def diag_curve(t):
    t = np.atleast_1d(np.asarray(t, float))
    return env_batch(np.vstack([t, t, t]))


tt = np.linspace(1e-7, 2 * PI / 3 - 1e-9, 400001)
dd = diag_curve(tt)
v_tan = float((dd[200001] - dd[199999]) / (tt[200001] - tt[199999]))
d_tan = float(dd[200000] - v_tan * tt[200000])
out['d_diag_tangent'] = dict(t_at=float(tt[200000]), diag=float(dd[200000]),
                             v=v_tan, d=d_tan)

def lin_excess(b, v, d):
    b = np.asarray(b, float)
    if b.sum() >= 2 * PI - 1e-12:
        return -np.inf
    return (v * b.sum() + d) - env(b)

for name, (v, d) in {'diag_tangent_at_t': (v_tan, d_tan),
                     'diag_tangent_at_pi3': (0.0, float(3 * np.sqrt(3) / 2))}.items():
    best = (-np.inf, None)
    for _ in range(3000):
        u = np.clip(rng.dirichlet(np.ones(3)) * rng.uniform(0.2, 6.28), 1e-6, PI - 1e-6)
        if u.sum() >= 2 * PI - 1e-9:
            continue
        e = lin_excess(u, v, d)
        if e > best[0]:
            best = (e, u)
    b = np.asarray(best[1], float).copy()
    step = 0.2
    for _ in range(400):
        imp = False
        for i in range(3):
            for sg in (1, -1):
                c = b.copy()
                c[i] = min(max(c[i] + sg * step, 1e-7), PI - 1e-7)
                if c.sum() >= 2 * PI - 1e-9:
                    continue
                e = lin_excess(c, v, d)
                if e > best[0]:
                    best, b, imp = (e, c), c, True
        if not imp:
            step *= 0.5
            if step < 1e-12:
                break
    out.setdefault('d_linear_majorant_test', {})[name] = dict(
        v=v, d=d, max_excess=float(best[0]), argmax=best[1].tolist())
print('(d)', json.dumps(out['d_linear_majorant_test'], indent=1), flush=True)

with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\decisive2.json", 'w') as f:
    json.dump(out, f, indent=1, default=float)
print('DONE')
