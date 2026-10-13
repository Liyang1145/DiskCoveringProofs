"""R20-stress mechanism calibration + local (second-order) falsification.

MECHANISM (sector-capacity loss decomposition), candidate-reverse-engineered:
  normalized radii u_f = gamma_f / max_f gamma_f  in (0,1]; sector i of the 9-ring has
  sides u_{i-1}, u_i (switch radii), included angle alpha_i, chord ell_i, and the six
  independent circle equations give  R = q_i / ell_i  with q_i = 2 sin(w_i/2).
  Valid caps c_i >= u_i give  ell_i <= Lambda_i(c) := max over box vertices of chord
  (chord^2 is convex in (u,v)) and hence the EXACT loss identity
        R = D_i + q_i (1/ell_i - 1/Lambda_i),    D_i := q_i / Lambda_i,  loss >= 0.
  Caps used:
    c_i = 1                                  (ceiling cap)          -> D0
    c_i = Gamma_i := min(1, sin A_i / sin b_i) (sine-law cap, exact identity
              gamma_face sin A_i = gamma_sw,i sin b_i, gamma_face <= 1)  -> D1
  D1 >= D0 pointwise.

SUFFICIENT GLOBAL INEQUALITY (mechanism):  min over legal angle shapes of max_i D_i >= r*.
Calibration: at the saved candidate every switch radius is at the ceiling (u_i = 1) and
Gamma_i = 1, so D1_i = D0_i = R = C529 for all nine sectors (lossless).

This script: (1) re-verify the calibration exactly; (2) second-order scan of max_i D1 on
the 21-dim legal manifold at the candidate (first order degenerates since ell_i <= Lambda_i
attains its maximum 1); (3) finite Newton-projected witnesses; (4) bounded multistart.
Writes only inside r20-stress/.
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
ns, shape, radii = zz['ns'], zz['shape'], zz['radii']
faces = ns['faces']
a0 = ns['x0'][:42]
R0, con0, det0 = shape(a0)
r_star = float(R0)                       # = C529 (saved certified object radius)
assert abs(con0).max() < 1e-12

eq = ns['eq'][:, :42]
Nr = null_space(eq)                      # 42 x 29
assert Nr.shape == (42, 29)
h = 1e-6
con8 = lambda a: shape(a)[1][13:21]
J8 = np.column_stack([(con8(a0 + Nr @ (np.eye(29)[k] * h)) - con8(a0 - Nr @ (np.eye(29)[k] * h))) / (2 * h)
                      for k in range(29)])
T = null_space(J8)                       # 29 x 21
assert T.shape == (29, 21)

def caps_of(a, sw_radii):
    """sine-law cap Gamma_i and geometric ceiling cap (=1)."""
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
    usw = u[11:20]
    al, ww = d['alpha'], d['w']
    ell = np.array([math.sqrt(usw[(i - 1) % 9] ** 2 + usw[i] ** 2
                              - 2 * usw[(i - 1) % 9] * usw[i] * math.cos(al[i])) for i in range(9)])
    q = 2 * np.sin(ww / 2)
    Lam0 = np.maximum(1.0, 2 * np.sin(al / 2))
    c = caps_of(a, usw)
    Lam1 = np.array([max(c[(i - 1) % 9], c[i],
                         math.sqrt(c[(i - 1) % 9] ** 2 + c[i] ** 2
                                   - 2 * c[(i - 1) % 9] * c[i] * math.cos(al[i]))) for i in range(9)])
    return dict(R=float(r), res=float(abs(con).max()), u=u, usw=usw, caps=c, ell=ell, q=q,
                alpha=al, w=ww, b=a[33:42], D0=q / Lam0, D1=q / Lam1, Lam0=Lam0, Lam1=Lam1,
                margin=float(min(list(a[:33]) + [math.pi - x for x in a[:33]]
                                 + list(a[33:42]) + [math.pi / 2 - x for x in a[33:42]]
                                 + list(al) + [math.pi - x for x in al]
                                 + list(ww) + [math.pi - x for x in ww])))

def newton_project(y, iters=40, tol=1e-15):
    """Newton onto the 8 nonlinear equality residuals (in y-coordinates)."""
    for _ in range(iters):
        a = a0 + Nr @ y
        c = con8(a)
        if np.abs(c).max() < tol:
            break
        J = np.column_stack([(con8(a + Nr @ (np.eye(29)[k] * 1e-7)) - c) / 1e-7 for k in range(29)])
        y = y - pinv(J) @ c
    return y

def point_from_dir(coef, eps):
    v = T @ coef
    v = v / np.linalg.norm(v)
    y = newton_project(eps * v)
    a = a0 + Nr @ y
    return a, eval_point(a)

# ---------- 1. calibration ----------
cal = eval_point(a0)
print('[1] calibration at candidate')
print('   R =', cal['R'], ' max|res| =', cal['res'])
print('   u_sw (switch normalized radii) =', np.round(cal['usw'], 12).tolist())
print('   caps Gamma                     =', np.round(cal['caps'], 12).tolist())
print('   D0 - R                         =', np.round(cal['D0'] - cal['R'], 12).tolist())
print('   D1 - R                         =', np.round(cal['D1'] - cal['R'], 12).tolist())
print('   R_i/ell_i spread               =', np.round([cal['q'][i] / cal['ell'][i] / cal['R'] - 1 for i in range(9)], 12).tolist())
print('   u (all 20, slack marked)       =', [(i, round(float(x), 9)) for i, x in enumerate(cal['u'])])

# ---------- 2. second-order local scan ----------
print('[2] second-order scan on the 21-dim legal manifold (eps-grid)')
rng = np.random.default_rng(2026)
coefs = [np.eye(21)[k] for k in range(21)]
for _ in range(60):
    v = rng.normal(size=21); coefs.append(v / np.linalg.norm(v))
scan = []
for k, coef in enumerate(coefs):
    row = []
    for eps in (0.01, 0.03, 0.06):
        try:
            a, p = point_from_dir(coef, eps)
            row.append(dict(eps=eps, R=p['R'], maxD1=float(p['D1'].max()), maxD0=float(p['D0'].max()),
                            argmax1=int(np.argmax(p['D1'])), argmax0=int(np.argmax(p['D0'])),
                            res=p['res'], margin=p['margin'],
                            second_order=(float(p['D1'].max()) - r_star) / eps ** 2))
        except Exception as e:
            row.append(dict(eps=eps, error=str(e)[:60]))
    scan.append(dict(k=k, kind='basis' if k < 21 else 'random', row=row))
best = min([r for s in scan for r in s['row'] if 'second_order' in r], key=lambda r: r['second_order'])
print('   best second-order coefficient:', {k: round(v, 6) if isinstance(v, float) else v for k, v in best.items()})

# also: is there a direction with max_i D1 < R0 at some eps?
viol = [r for s in scan for r in s['row'] if 'maxD1' in r and r['maxD1'] < r_star - 1e-9]
print('   sampled points with max D1 < R0:', len(viol), 'of', sum(len(s['row']) for s in scan))

# ---------- 3. refine a violator if present (or the best direction) ----------
cand = None
if viol:
    vbest = min(viol, key=lambda r: r['maxD1'])
    cand = vbest
print('[3] refinement of the most negative direction')
refine = []
kbest = int(best.get('k', 0))
for eps in (0.02, 0.04, 0.06, 0.09, 0.12, 0.16, 0.22):
    try:
        a, p = point_from_dir(coefs[kbest], eps)
        refine.append(dict(eps=eps, R=p['R'], maxD1=float(p['D1'].max()), maxD0=float(p['D0'].max()),
                           argmax=int(np.argmax(p['D1'])), res=p['res'], margin=p['margin'],
                           D1=p['D1'].tolist(), alpha_deg=(p['alpha'] * 180 / math.pi).tolist(),
                           w_deg=(p['w'] * 180 / math.pi).tolist(), caps=p['caps'].tolist(),
                           usw=p['usw'].tolist(), a=a.tolist()))
    except Exception as e:
        refine.append(dict(eps=eps, error=str(e)[:60]))
for r in refine:
    if 'maxD1' in r:
        print('   eps=%.3f  R=%.12f  maxD1=%.12f  (R0-maxD1)=%+.3e  res=%.1e margin=%.1e argmax=%d'
              % (r['eps'], r['R'], r['maxD1'], r_star - r['maxD1'], r['res'], r['margin'], r['argmax']))

# ---------- 4. bounded multistart global search for min max_i D1 ----------
print('[4] bounded multistart search: minimize t s.t. D1_i <= t, con8 = 0')
def cost(z):
    y, t = z[:29], z[29]
    a = a0 + Nr @ y
    p = eval_point(a)
    pen = 1e4 * np.abs(shape(a)[1][13:21]).sum()
    return t + pen

def run(start_eps, seed, maxiter=140):
    rr = np.random.default_rng(seed)
    coef = rr.normal(size=21); coef /= np.linalg.norm(coef)
    if start_eps == 0:
        y = np.zeros(29)
    else:
        y = newton_project(T @ coef * start_eps)
    a = a0 + Nr @ y
    p = eval_point(a)
    z0 = np.r_[y, p['D1'].max()]
    cons = [{'type': 'eq', 'fun': lambda z: shape(a0 + Nr @ z[:29])[1][13:21]},
            {'type': 'ineq', 'fun': lambda z: z[29] - eval_point(a0 + Nr @ z[:29])['D1']},
            {'type': 'ineq', 'fun': lambda z: eval_point(a0 + Nr @ z[:29])['margin'] - 1e-4}]
    o = minimize(lambda z: z[29], z0, method='SLSQP', constraints=cons,
                 options={'maxiter': maxiter, 'ftol': 1e-14})
    a = a0 + Nr @ o.x[:29]
    p = eval_point(a)
    return dict(eps0=start_eps, seed=seed, success=bool(o.success), t=float(o.x[29]),
                R=p['R'], maxD1=float(p['D1'].max()), maxD0=float(p['D0'].max()), res=p['res'],
                margin=p['margin'], a=a.tolist())

runs = []
for j, e0 in enumerate([0, 0.02, 0.05, 0.1, 0.2, 0.35, 0.6, 0.02, 0.05, 0.1, 0.2, 0.35]):
    runs.append(run(e0, 100 + j))
for r in runs:
    print('   start=%.2f  maxD1=%.12f  R=%.12f  res=%.1e margin=%.1e ok=%s'
          % (r['eps0'], r['maxD1'], r['R'], r['res'], r['margin'], r['success']))
best_run = min(runs, key=lambda r: r['maxD1'])
print('   best maxD1 =', best_run['maxD1'], ' R0 - best =', r_star - best_run['maxD1'])

out = dict(scope='mechanism calibration + bounded local/global falsification; numeric only',
           r_star=r_star,
           calibration={k: (v.tolist() if isinstance(v, np.ndarray) else v) for k, v in cal.items()},
           scan=[dict(k=s['k'], kind=s['kind'],
                      rows=[{kk: vv for kk, vv in r.items() if kk != 'a'} for r in s['row']]) for s in scan],
           refine=refine, runs=runs)
(OUT / 'mechanism_test.json').write_text(json.dumps(out, indent=2))
print('written', OUT / 'mechanism_test.json')
