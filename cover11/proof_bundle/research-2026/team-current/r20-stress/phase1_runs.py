"""Phase-1 remaining bounded counterexample runs (13..20 of a 20-run budget) for the
sector-capacity mechanism, plus conditional (non-flat) domains.

Mechanism functional:  D_i = q_i / Lambda_i,  Lambda_i = box-max chord with switch caps
  caps_i = min(1, sin A_i / sin b_i);   R >= D_i  exactly;  claim was  min max_i D_i >= C529.
Runs 1..12 (mechanism_test.py) all found max_i D_i ~ 0.379431 < C529 = 0.3799838531..., all with
sector 2 nearly flat (alpha_2 -> pi).  Here: impose a uniform non-flat margin
  delta_all := min_i (pi - alpha_i) >= delta,   delta in {0.05,0.02,0.005,0.002,0.001}
and repeat the minimisation, to test whether the failure is confined to the flat branch.
"""
import os, json, math, time
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
from scipy.linalg import null_space, pinv
W = Path(__file__).parent; LEAD = W.parent / 'lead'; OUT = W / 'out'
zz = {'__file__': str(LEAD / 'check_angle_only.py')}
exec((LEAD / 'check_angle_only.py').read_text(encoding='utf-8').split("a=ns['x0'][:42]")[0], zz)
ns, shape = zz['ns'], zz['shape']
faces = ns['faces']
a0 = ns['x0'][:42]
R0 = float(shape(a0)[0])
eq = ns['eq'][:, :42]; Nr = null_space(eq)
h = 1e-6
con8 = lambda a: shape(a)[1][13:21]
J8 = np.column_stack([(con8(a0 + Nr @ (np.eye(29)[k] * h)) - con8(a0 - Nr @ (np.eye(29)[k] * h))) / (2 * h)
                      for k in range(29)])
T = null_space(J8)

def caps_of(a):
    c = np.zeros(9)
    for i in range(9):
        e = tuple(sorted((i, (i + 1) % 9)))
        for t, f in enumerate(faces):
            if e[0] in f and e[1] in f:
                k = f.index(next(v for v in f if v not in e))
                c[i] = min(1.0, math.sin(a[3 * t + k]) / math.sin(a[33 + i]))
                break
    return c

def eval_point(a):
    r, con, d = shape(a)
    g = np.exp(d['logg']); M = g.max(); u = g / M
    usw = u[11:20]; al, ww = d['alpha'], d['w']
    ell = np.array([math.sqrt(usw[(i - 1) % 9] ** 2 + usw[i] ** 2
                              - 2 * usw[(i - 1) % 9] * usw[i] * math.cos(al[i])) for i in range(9)])
    q = 2 * np.sin(ww / 2)
    c = caps_of(a)
    Lam1 = np.array([max(c[(i - 1) % 9], c[i],
                         math.sqrt(c[(i - 1) % 9] ** 2 + c[i] ** 2
                                   - 2 * c[(i - 1) % 9] * c[i] * math.cos(al[i]))) for i in range(9)])
    D1 = q / Lam1
    margin = min(list(a[:33]) + [math.pi - x for x in a[:33]] + list(a[33:42])
                 + [math.pi / 2 - x for x in a[33:42]] + list(al) + [math.pi - x for x in al]
                 + list(ww) + [math.pi - x for x in ww])
    flat = float(min(math.pi - x for x in al))
    return dict(R=float(r), res=float(abs(con).max()), D1=D1, margin=float(margin), flat=flat,
                alpha=al, w=ww, caps=c, usw=usw, u=u)

def newton_project(y, iters=40, tol=1e-15):
    for _ in range(iters):
        a = a0 + Nr @ y
        c = con8(a)
        if np.abs(c).max() < tol:
            break
        J = np.column_stack([(con8(a + Nr @ (np.eye(29)[k] * 1e-7)) - c) / 1e-7 for k in range(29)])
        y = y - pinv(J) @ c
    return y

def run(delta, eps0, seed, margin_floor=1e-4, maxiter=160):
    rr = np.random.default_rng(seed)
    coef = rr.normal(size=21); coef /= np.linalg.norm(coef)
    y = np.zeros(29) if eps0 == 0 else newton_project(T @ coef * eps0)
    p = eval_point(a0 + Nr @ y)
    z0 = np.r_[y, p['D1'].max()]
    def cons_eq(z): return shape(a0 + Nr @ z[:29])[1][13:21]
    def cons_D(z): return z[29] - eval_point(a0 + Nr @ z[:29])['D1']
    def cons_marg(z): return eval_point(a0 + Nr @ z[:29])['margin'] - margin_floor
    def cons_flat(z): return eval_point(a0 + Nr @ z[:29])['flat'] - delta
    o = minimize(lambda z: z[29], z0, method='SLSQP',
                 constraints=[{'type': 'eq', 'fun': cons_eq}, {'type': 'ineq', 'fun': cons_D},
                              {'type': 'ineq', 'fun': cons_marg}, {'type': 'ineq', 'fun': cons_flat}],
                 options={'maxiter': maxiter, 'ftol': 1e-14})
    a = a0 + Nr @ o.x[:29]
    p = eval_point(a)
    return dict(delta=delta, eps0=eps0, seed=seed, margin_floor=margin_floor, success=bool(o.success),
                maxD1=float(p['D1'].max()), R=p['R'], res=p['res'], margin=p['margin'],
                flat=p['flat'], alpha_deg=(p['alpha'] * 180 / math.pi).tolist(),
                caps=p['caps'].tolist(), usw=p['usw'].tolist(), D1=p['D1'].tolist(), a=a.tolist())

jobs = [(0.05, 0.10, 201, 1e-4), (0.02, 0.10, 202, 1e-4), (0.005, 0.10, 203, 1e-4),
        (0.002, 0.10, 204, 1e-4), (0.05, 0.30, 205, 1e-4), (0.005, 0.30, 206, 1e-4),
        (0.0, 0.10, 207, 1e-2), (0.001, 0.20, 208, 1e-4)]
runs = []
for (d, e0, sd, mf) in jobs:
    r = run(d, e0, sd, mf)
    runs.append(r)
    print('delta=%.4f start=%.2f seed=%d  maxD1=%.12f  R=%.12f  res=%.1e margin=%.1e flat=%.2e  viol=%s'
          % (d, e0, sd, r['maxD1'], r['R'], r['res'], r['margin'], r['flat'], r['maxD1'] < R0), flush=True)
res = dict(scope='runs 13..20: conditional non-flat domains; bounded SLSQP, numeric only',
           R0_reference=R0, runs=runs)
(OUT / 'phase1_runs.json').write_text(json.dumps(res, indent=2))
print('best overall maxD1 with delta>0 :', min([r['maxD1'] for r in runs if r['delta'] > 0]))
print('R0 =', R0)
