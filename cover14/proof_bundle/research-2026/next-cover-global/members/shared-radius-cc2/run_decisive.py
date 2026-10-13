"""
Decisive tests.

T1  formula-vs-crossing:  x0 by bisection on H (H strictly decreasing) vs
    x0 by (B + sqrt(B^2-4AC))/(2A).  Flag mismatches, and check which root
    satisfies H(x) == pi (mod 2pi) on the principal branch.

T2  |A|:  scan/sweep of the envelope  A(beta) = x0(beta) * sum sin(beta_i)
    (valid because the x-constraint is x <= x0; see notes)  -> sup and argmax.

T3  DIRECT relaxed problem, no envelope reduction:
        maximize  x * sum_i y_i sin beta_i
        over  beta_i in (0,pi), sum beta < 2pi, 0<x<=1, 0<y_i<=1,
        s.t.  sum_i theta_i = pi,  0 < theta_i < pi - beta_i,
              theta_i = atan2(y_i sin beta_i, x - y_i cos beta_i)
    solved by: given (beta,x) solve for the largest common scale
    lambda in (0,1] with  g(lambda) = sum theta_i(lambda y) = pi
    (g is strictly increasing in lambda), then A = x * sum y_i sin beta_i.
    Optimum over (beta,x) by coordinate ascent + multi-start.
    Check: (a) A <= 3 everywhere, (b) argmax near (pi/2,pi/2,pi/2), x=1.
"""
import json
import sys
import time
import numpy as np

sys.path.insert(0, r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2")
import envelope_clean as EC

PI = EC.PI
rng = np.random.default_rng(424242)
out = {}

# ---------------------------------------------------------------- T1
n = 20000
beta = rng.dirichlet(np.ones(3) * 1.5, size=n).T * rng.uniform(0.05, 6.2, size=n)
beta = np.clip(beta, 1e-6, PI - 1e-9)
Bsum = beta.sum(axis=0)
m = Bsum > PI + 1e-9

x0_b = EC.x0_bisect(beta)
x0_f = EC.x0_theorem(beta)
mask = m & (Bsum < 2 * PI - 1e-9)
db = np.abs(EC.H(beta[:, mask], x0_b[mask]) - PI)
df = np.abs(EC.H(beta[:, mask], x0_f[mask]) - PI)
diff = np.abs(x0_b[mask] - x0_f[mask])
# Im P = 0 at both roots?
A_, B_, C_ = EC.coefsABC(beta[:, mask])
im_b = A_ * x0_b[mask] ** 2 - B_ * x0_b[mask] + C_
im_f = A_ * x0_f[mask] ** 2 - B_ * x0_f[mask] + C_
out['T1'] = dict(
    n_tested=int(mask.sum()),
    bisect_root_resid_max=float(db.max()),
    formula_root_resid_max=float(df.max()),
    x0_diff_max=float(diff.max()),
    n_x0_diff_gt_1e9=float((diff > 1e-9).sum()),
    imP_at_bisect_max=float(np.abs(im_b).max()),
    imP_at_formula_max=float(np.abs(im_f).max()),
    min_x0=float(x0_b[mask].min()), max_x0=float(x0_b[mask].max()),
)
print('T1 done', json.dumps(out['T1'], indent=1), flush=True)

# ---------------------------------------------------------------- T2
# diagonal sweep
ts = np.linspace(1e-6, 2 * PI / 3 - 1e-9, 400001)
bd = np.vstack([ts, ts, ts])
Ad, x0d = EC.A_of_beta(bd, 'theorem')
i = int(np.argmax(Ad))
out['T2_diag'] = dict(max=float(Ad.max()), t_at_max=float(ts[i]),
                      x0_at_max=float(x0d[i]),
                      A_at_pi3=float(EC.A_of_beta([PI / 3] * 3)[0]),
                      A_at_pi2=float(EC.A_of_beta([PI / 2] * 3)[0]),
                      A_at_t1=float(EC.A_of_beta([1.0] * 3)[0]))

# two-equal sweep (s,s,pi-s) junction and around
ss = np.linspace(1e-6, PI - 1e-6, 400001)
b2 = np.vstack([ss, ss, np.clip(PI - ss, 1e-9, PI - 1e-9)])
A2, x02 = EC.A_of_beta(b2, 'theorem')
j = int(np.argmax(A2))
out['T2_two_equal_at_junction'] = dict(max=float(A2.max()), s_at_max=float(ss[j]),
                                       beta=[float(ss[j]), float(ss[j]), float(PI - ss[j])],
                                       x0=float(x02[j]))
# two equal with sum > pi family: (s,s,u) with s fixed, u varies
best = (-1, None)
for s in np.linspace(0.05, PI - 0.05, 400):
    us = np.linspace(1e-6, min(PI - 1e-6, 2 * PI - 2 * s - 1e-6), 4000)
    bb = np.vstack([np.full_like(us, s), np.full_like(us, s), us])
    Av, x0v = EC.A_of_beta(bb, 'theorem')
    k = int(np.argmax(Av))
    if Av[k] > best[0]:
        best = (float(Av[k]), [float(s), float(s), float(us[k])], float(x0v[k]))
out['T2_two_equal_family_best'] = dict(A=best[0], beta=best[1], x0=best[2])

# random multi-start local search on the envelope (coordinate ascent in beta)
def env_scalar(b):
    return float(EC.A_of_beta(np.asarray(b, float).reshape(3, 1), 'theorem')[0][0])

def ascent(b0, sweeps=400, step0=0.4):
    b = np.clip(np.asarray(b0, float), 1e-7, PI - 1e-7)
    if b.sum() >= 2 * PI:
        b = b * (2 * PI - 1e-6) / b.sum()
    best = env_scalar(b)
    step = step0
    for _ in range(sweeps):
        imp = False
        for i in range(3):
            for sg in (1, -1):
                c = b.copy()
                c[i] = min(max(c[i] + sg * step, 1e-7), PI - 1e-7)
                if c.sum() >= 2 * PI - 1e-9:
                    continue
                v = env_scalar(c)
                if v > best * (1 + 1e-14):
                    best, b, imp = v, c, True
        if not imp:
            step *= 0.5
            if step < 1e-11:
                break
    return best, b

starts = [[PI / 3] * 3, [PI / 2] * 3, [1.0, 1.0, 1.0], [2 * PI / 3 - 1e-6] * 3,
          [0.9, 1.2, 1.2], [2.0, 0.6, 0.6], [1.5, 1.5, 0.5], [2.6, 0.3, 0.3]]
g_best = (-1, None)
for s in starts:
    v, b = ascent(s)
    if v > g_best[0]:
        g_best = (v, b)
for _ in range(300):
    u = rng.dirichlet(np.ones(3)) * 2 * PI * 0.98
    u = np.clip(u, 1e-6, PI - 1e-6)
    v, b = ascent(u, sweeps=200)
    if v > g_best[0]:
        g_best = (v, b)
out['T2_ascent_best'] = dict(A=float(g_best[0]), beta=g_best[1].tolist(),
                             Bsum=float(g_best[1].sum()),
                             x0=float(EC.x0_theorem(g_best[1])))
print('T2 done', json.dumps({k: v for k, v in out.items() if k.startswith('T2')}, indent=1), flush=True)

# ---------------------------------------------------------------- T3 direct
def theta_xy(beta, x, y):
    beta = np.asarray(beta, float)
    num = y * np.sin(beta)
    den = x - y * np.cos(beta)
    th = np.arctan2(num, den)
    return np.where(th < 0, th + 2 * PI, th)

def direct_A(beta, x, iters=80):
    """largest-lambda feasible value of x*sum y sin beta."""
    beta = np.asarray(beta, float)
    if beta.sum() >= 2 * PI:
        return -1.0
    one = np.ones(3)
    g1 = theta_xy(beta, x, one).sum()
    if g1 <= PI:                      # all y=1 feasible
        y = one
    else:
        lo, hi = 1e-12, 1.0           # find lambda with g = pi
        for _ in range(iters):
            mid = 0.5 * (lo + hi)
            gm = theta_xy(beta, x, mid * one).sum()
            if gm > PI:
                hi = mid
            else:
                lo = mid
            # keep g(lo) <= pi <= g(hi)
        lam = 0.5 * (lo + hi)
        y = lam * one
        # guard: recompute with exact bisection statement
        if theta_xy(beta, x, y).sum() > PI:
            y = lo * one
    th = theta_xy(beta, x, y)
    if np.any(th >= PI - beta - 1e-12):
        return -1.0
    return x * float((y * np.sin(beta)).sum())

def direct_ascent(b0, x0_, sweeps=200, step0=0.3):
    b = np.clip(np.asarray(b0, float), 1e-6, PI - 1e-6)
    x = float(np.clip(x0_, 1e-6, 1.0))
    best = direct_A(b, x)
    step = step0
    for _ in range(sweeps):
        imp = False
        for i in range(3):
            for sg in (1, -1):
                c = b.copy()
                c[i] = min(max(c[i] + sg * step, 1e-6), PI - 1e-6)
                if c.sum() >= 2 * PI - 1e-9:
                    continue
                for xs in (x,):
                    v = direct_A(c, xs)
                    if v > best * (1 + 1e-13):
                        best, b, imp = v, c, True
        for sg in (1, -1):
            xn = min(max(x + sg * step, 1e-6), 1.0)
            v = direct_A(b, xn)
            if v > best * (1 + 1e-13):
                best, x, imp = v, xn, True
        if not imp:
            step *= 0.5
            if step < 1e-10:
                break
    return best, b, x

t0 = time.time()
g3 = (-1, None, None)
s3 = [([PI / 2] * 3, 1.0), ([PI / 3] * 3, 1.0), ([PI / 2] * 3, 0.577),
      ([1.0, 1.0, 1.0], 1.0), ([1.2, 1.2, 0.9], 1.0), ([2.0, 0.55, 0.55], 1.0),
      ([2 * PI / 3 - 1e-4] * 3, 1.0), ([1.9, 1.1, 0.1], 1.0)]
for b0, x0_ in s3:
    v, b, x = direct_ascent(b0, x0_)
    if v > g3[0]:
        g3 = (v, b, x)
for i in range(120):
    u = rng.dirichlet(np.ones(3)) * rng.uniform(0.2, 6.1)
    u = np.clip(u, 1e-6, PI - 1e-6)
    if u.sum() >= 2 * PI:
        u = u * (2 * PI - 1e-6) / u.sum()
    v, b, x = direct_ascent(u, rng.uniform(0.2, 1.0), sweeps=120)
    if v > g3[0]:
        g3 = (v, b, x)
out['T3_direct'] = dict(A=float(g3[0]), beta=np.asarray(g3[1]).tolist(),
                        x=float(g3[2]), Bsum=float(np.sum(g3[1])),
                        seconds=time.time() - t0)
# spot checks: full-y=1 cases
out['T3_spot'] = {
    'pi2_pi2_pi2_x1': direct_A([PI / 2] * 3, 1.0),
    'pi3_x1': direct_A([PI / 3] * 3, 1.0),
    'diag1.2_x1': direct_A([1.2] * 3, 1.0),
    'diag2.0_x1': direct_A([2.0, 2.0, 2.0 / 1.0], 1.0),
    'pi2_x0.9': direct_A([PI / 2] * 3, 0.9),
    'cand_x0.9671': direct_A([0.9223829833, 1.1925065472, 1.1925065472], 0.9671084534),
    'cand_x1': direct_A([0.9223829833, 1.1925065472, 1.1925065472], 1.0),
    'cand_x0.6715': direct_A([0.9223829833, 1.1925065472, 1.1925065472], 0.6715),
}
print('T3 done', json.dumps(out['T3_direct'], indent=1), flush=True)
print(json.dumps(out['T3_spot'], indent=1), flush=True)

with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\decisive_results.json", 'w') as f:
    json.dump(out, f, indent=1, default=float)
print('ALL DONE', time.time() - t0)
