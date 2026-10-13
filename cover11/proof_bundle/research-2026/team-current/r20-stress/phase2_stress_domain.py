"""Phase 2 (bounded, <=12 starts): counterexample test for the saved KKT stress
    Phi_KKT(a) = sum_f lam_f (log gamma_f + log R_shape)
on the LEGAL angle domain intersected with the main domain {R_shape <= 0.38}.

Scope / calibre (read before interpreting):
 * Domain: 13 linear angle equalities imposed exactly through the nullspace coordinate y
   (a = a0 + Nr y), 8 nonlinear residuals (2 sine cycles + 6 circle ratios) imposed as
   equality constraints, strict positivity margins >= 1e-4, and R_shape <= 0.38.
 * Objective: Phi_KKT with the lead's saved NUMERIC KKT multipliers (angle_stress_probe.py).
   On the exact feasible manifold Phi_KKT <= log R_shape always (weighted mean of b_f,
   b_f = log u_f + log R_shape <= log R_shape).  Candidate is stationary and TIGHT:
   Phi_KKT(a0) - log Tcert = +3e-15 (float64).  A violation needs
   spread := log R - Phi_KKT > log(R/Tcert) <= log(0.38/Tcert) = 4.2493e-5.
 * Secondary diagnostic: full 21-dim reduced Hessian of Phi_KKT on the feasible manifold at
   the candidate (NOT the lead's off-manifold linear-multiplier curvature test), with a
   projected line search if a negative eigenvalue exists.
 * A negative witness is a NUMERIC counterexample to this ONE stress functional; it is NOT a
   disproof of the covering lower bound.  Only a legal point with R < Tcert would threaten the
   conjectured optimum (and even then needs exact realization to become a disproof).

Writes only inside research-2026/team-current/r20-stress/.
"""
import os, json, math, time
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp
from scipy.optimize import minimize
from scipy.linalg import null_space, pinv

W = Path(__file__).parent; LEAD = W.parent / 'lead'; OUT = W / 'out'
T0 = time.time()

# ---------------- model + saved KKT stress multipliers (read-only reuse) ----------------
zz = {'__file__': str(LEAD / 'angle_stress_probe.py')}
exec((LEAD / 'angle_stress_probe.py').read_text(encoding='utf-8').split('y0=np.zeros(29)')[0], zz)
ns, shape, branches, Nr, a0 = zz['ns'], zz['shape'], zz['branches'], zz['N'], zz['a0']
lam, mu, act = zz['lam'], zz['mu'], zz['act']
station = float(zz['station'])
R0 = float(shape(a0)[0])

Tcert_str = '0.3799838531198386897222616061360932143087189561522153170163892'   # C249 certified upper bound
mp.mp.dps = 60
log_Tcert = float(mp.log(mp.mpf(Tcert_str)))
log_038 = float(mp.log(mp.mpf('0.38')))
spread_budget_038 = log_038 - log_Tcert
R_MAIN = 0.38
MAR_FLOOR = 1e-4

# ---------------- basic functionals ------------------------------------------------------
def eval_all(y):
    """returns (margin_min, R, max|21 res|, Phi, spread, u, alpha, w) or None."""
    a = a0 + Nr @ y
    r, con, d = shape(a)
    if not np.isfinite(r):
        return None
    al, ww = d['alpha'], d['w']
    mar = np.r_[a[:33], math.pi - a[:33], a[33:42], math.pi / 2 - a[33:42],
                al, math.pi - al, ww, math.pi - ww]
    if not np.all(np.isfinite(mar)):
        return None
    g = d['logg'] + math.log(max(d['rat'][0], 1e-100))
    phi = float(lam @ g[act])
    gg = np.exp(d['logg']); u = gg / gg.max()
    spread = float(-(lam @ np.log(u[act])))
    return dict(margin=float(mar.min()), R=float(r), res=float(abs(con).max()), phi=phi,
                spread=spread, u=u, alpha=al, w=ww, a=a)

def safe(v, fallback=-1e3):
    return v if (v is not None and np.isfinite(v)) else fallback

def phi_raw(y):
    """clean Phi (no R-penalty) for second-order diagnostics; large value off domain."""
    e = eval_all(y)
    if e is None or e['margin'] <= 1e-6:
        return 1e3
    return e['phi']

def obj(y):
    e = eval_all(y)
    if e is None:
        return 1e3
    if e['margin'] <= 0:
        return 1e3 - 1e3 * e['margin']
    v = e['phi']
    if e['R'] > R_MAIN:                      # soft pull for infeasible starts
        v += 1e3 * (e['R'] - R_MAIN)
    return v

def c_eq(y):
    e = eval_all(y)
    return np.full(8, 1e3) if e is None else (shape(e['a'])[1][13:21])

def c_R(y):
    e = eval_all(y)
    return -1e3 if e is None else (R_MAIN - e['R'])

def c_mar(y):
    e = eval_all(y)
    return -1e3 if e is None else (e['margin'] - MAR_FLOOR)

CONS = [{'type': 'eq', 'fun': c_eq}, {'type': 'ineq', 'fun': c_R}, {'type': 'ineq', 'fun': c_mar}]

def newton_project(y, iters=50, tol=1e-15):
    for _ in range(iters):
        a = a0 + Nr @ y
        c = shape(a)[1][13:21]
        if not np.all(np.isfinite(c)) or np.abs(c).max() < tol:
            break
        J = np.column_stack([(shape(a0 + Nr @ (y + np.eye(29)[k] * 1e-7))[1][13:21] - c) / 1e-7
                             for k in range(29)])
        y = y - pinv(J) @ c
    return y

def feasible(y, rmax=R_MAIN, need_mar=MAR_FLOOR):
    e = eval_all(y)
    return (e is not None and e['res'] < 1e-8 and e['R'] <= rmax + 1e-12
            and e['margin'] >= need_mar)

# ---------------- candidate calibration --------------------------------------------------
cal = eval_all(np.zeros(29))
print('[cal] R0=%.17g  Phi=%.17g  Phi-logTcert=%+.3e  spread=%.3e  res=%.1e  margin=%.1e'
      % (cal['R'], cal['phi'], cal['phi'] - log_Tcert, cal['spread'], cal['res'], cal['margin']))
print('[cal] stationarity of saved KKT weights = %.3e   |act| = %d   min lam = %.3e'
      % (station, len(act), float(lam.min())))
print('[cal] spread budget at R=0.38: log(0.38/Tcert) = %.6e' % spread_budget_038)

# ---------------- secondary diagnostic: 21-dim reduced Hessian at the candidate ----------
h = 1e-5
def grad_phi(y):
    return np.array([(phi_raw(y + np.eye(29)[k] * h) - phi_raw(y - np.eye(29)[k] * h)) / (2 * h)
                     for k in range(29)])
H = np.column_stack([(grad_phi(np.eye(29)[k] * 2e-4) - grad_phi(-np.eye(29)[k] * 2e-4)) / (4e-4)
                     for k in range(29)])
H = 0.5 * (H + H.T)
J8 = np.column_stack([(shape(a0 + Nr @ (np.eye(29)[k] * 1e-6))[1][13:21]
                       - shape(a0 - Nr @ (np.eye(29)[k] * 1e-6))[1][13:21]) / (2e-6) for k in range(29)])
Z = null_space(J8); assert Z.shape == (29, 21)
Hred = Z.T @ H @ Z; Hred = 0.5 * (Hred + Hred.T)
ev = np.linalg.eigvalsh(Hred)
print('[hess] reduced Hessian (21-dim feasible tangent) eigs: min=%.6e max=%.6e  n_neg=%d'
      % (ev.min(), ev.max(), int((ev < 0).sum())))
line = []
if ev.min() < 0:
    vec = Z @ np.linalg.eigh(Hred)[1][:, 0]
    vec = vec / np.linalg.norm(vec)
    for t in (1e-4, 3e-4, 1e-3, 3e-3, 1e-2, 3e-2, 6e-2):
        y = newton_project(t * vec)
        e = eval_all(y)
        if e is None:
            line.append(dict(t=t, error='eval failed')); continue
        line.append(dict(t=t, R=e['R'], phi=e['phi'], phi_minus_logTcert=e['phi'] - log_Tcert,
                         spread=e['spread'], res=e['res'], margin=e['margin'],
                         violated=bool(e['phi'] < log_Tcert and e['res'] < 1e-7
                                       and e['R'] <= R_MAIN and e['margin'] > 0), a=e['a'].tolist()))
    print('[hess] projected line search along negative eigvec:')
    for r in line:
        if 'phi' in r:
            print('    t=%.0e R=%.12f Phi-logTcert=%+.3e res=%.1e margin=%.1e viol=%s'
                  % (r['t'], r['R'], r['phi_minus_logTcert'], r['res'], r['margin'], r['violated']))

# ---------------- 12 starts ---------------------------------------------------------------
rng = np.random.default_rng(20260925)
T = null_space(J8)                                     # 21-dim tangent basis in y-space
def rand_dir():
    v = T @ rng.normal(size=21); return v / np.linalg.norm(v)

def boundary_start(vec, lo=1e-5, hi=5e-1):
    """first crossing R=0.38 along s -> Newton(y=s*v), then one bisection step inside."""
    s_prev = 0.0
    s = lo
    while s <= hi:
        y = newton_project(s * vec)
        e = eval_all(y)
        if e is not None and e['margin'] > 0 and e['R'] > R_MAIN:
            break
        s_prev = s; s *= 1.4
    else:
        return None
    for _ in range(40):
        sm = 0.5 * (s_prev + s)
        y = newton_project(sm * vec); e = eval_all(y)
        if e is not None and e['margin'] > 0 and e['R'] > R_MAIN:
            s = sm
        else:
            s_prev = sm
    return newton_project(0.995 * s_prev * vec)

starts = [('candidate', np.zeros(29))]
for j, eps in enumerate((0.02, 0.05, 0.1, 0.2, 0.5)):
    y = newton_project(eps * rand_dir())
    if not feasible(y):                                 # pull inside R<=0.38 if needed
        v = y / max(np.linalg.norm(y), 1e-30)
        s = np.linalg.norm(y)
        for _ in range(60):
            e = eval_all(y)
            if e is not None and e['margin'] > 0 and e['R'] <= R_MAIN:
                break
            s *= 0.7; y = newton_project(s * v)
    starts.append(('tangent_eps%g' % eps, y))
for j in range(3):
    y = boundary_start(rand_dir())
    if y is None:
        y = newton_project(1e-3 * rand_dir())
    starts.append(('boundary_R038_%d' % j, y))
# three starts descending from phase-1 witnesses (all have R ~ 0.389 > 0.38)
mt = json.loads((OUT / 'mechanism_test.json').read_text())
p1 = json.loads((OUT / 'phase1_runs.json').read_text())
wit = [('w_m06', np.array(min(mt['runs'], key=lambda r: r['maxD1'])['a'])),
       ('w_c00', np.array(p1['runs'][0]['a'])),
       ('w_c02', np.array(min(p1['runs'], key=lambda r: r['R'])['a']))]
for tag, aw in wit:
    yw = pinv(Nr) @ (aw - a0)
    yb = boundary_start(yw / np.linalg.norm(yw))
    starts.append((tag, yb if yb is not None else newton_project(yw)))

assert len(starts) <= 12, len(starts)
print('[runs] %d starts' % len(starts))

runs = []
for tag, y0 in starts:
    e0 = eval_all(y0)
    t0 = time.time()
    o = minimize(obj, y0, method='SLSQP', constraints=CONS,
                 options={'maxiter': 200, 'ftol': 1e-12})
    y = o.x
    e = eval_all(y)
    rec = dict(start=tag, nit=int(o.nit), success=bool(o.success), message=str(o.message)[:80],
               start_R=float(e0['R']) if e0 else None,
               start_phi_minus_logTcert=float(e0['phi'] - log_Tcert) if e0 else None,
               sec=round(time.time() - t0, 1))
    if e is None:
        rec['error'] = 'final eval failed'
    else:
        feasible_final = bool(e['res'] < 1e-6 and e['R'] <= R_MAIN + 1e-12 and e['margin'] > 0)
        rec.update(R=e['R'], phi=e['phi'], phi_minus_logTcert=e['phi'] - log_Tcert,
                   spread=e['spread'], res=e['res'], margin=e['margin'],
                   n_active=int((e['u'] > 1 - 1e-9).sum()),
                   u_min=float(e['u'].min()),
                   violated=bool(feasible_final and e['phi'] < log_Tcert - 1e-9),
                   tight=bool(feasible_final and abs(e['phi'] - log_Tcert) <= 1e-9),
                   feasible_final=feasible_final, a=e['a'].tolist())
    runs.append(rec)
    print('  %-18s ok=%-5s nit=%-4d R=%.12f Phi-logTcert=%+.4e spread=%.4e res=%.1e mar=%.1e -> viol=%s'
          % (tag, rec['success'], rec['nit'], rec.get('R', float('nan')),
             rec.get('phi_minus_logTcert', float('nan')), rec.get('spread', float('nan')),
             rec.get('res', float('nan')), rec.get('margin', float('nan')), rec.get('violated')), flush=True)

feas = [r for r in runs if r.get('feasible_final')]
best = min(feas, key=lambda r: r['phi']) if feas else None
summary = dict(
    n_starts=len(starts), n_runs=len(runs), n_feasible_final=len(feas),
    n_violations=int(sum(1 for r in runs if r.get('violated'))),
    n_tight=int(sum(1 for r in runs if r.get('tight'))),
    min_phi_minus_logTcert_over_feasible=(best['phi_minus_logTcert'] if best else None),
    argmin_start=(best['start'] if best else None),
    argmin_R=(best['R'] if best else None), argmin_spread=(best['spread'] if best else None),
    any_R_below_Tcert=bool(any(r.get('R', 9) < float(mp.mpf(Tcert_str)) for r in feas)),
)
out = dict(scope='phase-2 bounded counterexample test of Phi_KKT on D_legal with R<=0.38; numeric only',
           route='read-only reuse of lead angle model + saved numeric KKT multipliers',
           Tcert=Tcert_str, log_Tcert=log_Tcert, R_MAIN=R_MAIN, margin_floor=MAR_FLOOR,
           spread_budget_at_R038=spread_budget_038,
           stationarity_of_saved_KKT=station, n_active_candidate=int(len(act)),
           min_lam=float(lam.min()), calibration=cal,
           hessian_diag=dict(eigs=ev.tolist(), n_neg=int((ev < 0).sum()),
                             eps_grad=h, eps_hess=2e-4, line_search=line),
           starts=[s[0] for s in starts], runs=[{k: v for k, v in r.items() if k != 'a'} for r in runs],
           raws={r['start']: r.get('a') for r in runs}, summary=summary,
           runtime_s=round(time.time() - T0, 1))
def jable(o):
    if isinstance(o, np.ndarray):
        return o.tolist()
    if isinstance(o, dict):
        return {k: jable(v) for k, v in o.items()}
    if isinstance(o, (list, tuple)):
        return [jable(v) for v in o]
    if isinstance(o, np.floating):
        return float(o)
    if isinstance(o, np.integer):
        return int(o)
    return o

(OUT / 'phase2_stress_domain.json').write_text(json.dumps(jable(out), indent=2))
print('[summary]', json.dumps(summary, indent=2))
print('[done] runtime %.1f s -> out/phase2_stress_domain.json' % (time.time() - T0))
