"""Phase-2 follow-up (bounded, no new starts): independent verification of the phase-2
counterexample points + boundary refinement.

Verified points
  P1 = best feasible point with Phi < log Tcert inside {R <= 0.38}   (phase2 runs 2 and 8)
  P2 = deepest descent point on the LEGAL manifold found by the 21-dim reduced-Hessian
        line search (R ~ 0.3976, outside {R<=0.38});  this tests the stress inequality on
        the full legal domain D_legal, not on the main domain.
  control = saved candidate a0 (its exact object C529 has R = C529 > Tcert; the float64
        angle vector evaluates 2.8e-15 BELOW Tcert -> model storage precision, not a cover).

Independent paths per point
  A1 float64 lead model: R recovered from all 9 sector ratios; Phi from all 20 root gauges
    (gauge invariance control); 13 linear + 8 nonlinear residuals; positivity margins.
  A2 mpmath 50-digit re-implementation of the model formulas (sine-law tree over the factor
    graph, sector widths, chords, circle ratios) - independent arithmetic path.
  B  boundary refinement of P1 with R = 0.38 imposed as equality (the active boundary), and a
    Newton-reprojected projected-gradient descent on the boundary problem
    (max spread s.t. c8 = 0, R = 0.38) to decide whether the 1e-9-level violation is the
    constrained minimum or an early stop.

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

zz = {'__file__': str(LEAD / 'check_angle_only.py')}
exec((LEAD / 'check_angle_only.py').read_text(encoding='utf-8').split("a=ns['x0'][:42]")[0], zz)
ns, shape, radii = zz['ns'], zz['shape'], zz['radii']
zz2 = {'__file__': str(LEAD / 'angle_stress_probe.py')}
exec((LEAD / 'angle_stress_probe.py').read_text(encoding='utf-8').split('y0=np.zeros(29)')[0], zz2)
Nr, a0 = zz2['N'], ns['x0'][:42]
lam, act = zz2['lam'], zz2['act']

Tcert_str = '0.3799838531198386897222616061360932143087189561522153170163892'
C529_str = '0.379983853119838709048518179573429853811597902801556119905385'
mp.mp.dps = 50
log_Tcert = float(mp.log(mp.mpf(Tcert_str)))
R_MAIN = 0.38
MAR_FLOOR = 1e-4

phase2 = json.loads((OUT / 'phase2_stress_domain.json').read_text())

# ---------------------------------------------------------------- independent evaluators
def A1_eval(avec):
    r64, con64, d64 = shape(avec)
    al, ww = d64['alpha'], d64['w']
    gt0 = np.exp(d64['logg']); u0 = gt0 / gt0.max()
    usw = u0[11:20]
    ell = np.array([math.sqrt(usw[(i - 1) % 9] ** 2 + usw[i] ** 2
                              - 2 * usw[(i - 1) % 9] * usw[i] * math.cos(al[i])) for i in range(9)])
    q = 2 * np.sin(ww / 2)
    R_sec = q / ell
    phis = []
    for root in range(20):
        _r, _c, _d = shape(avec, root)
        phis.append(float(lam @ (_d['logg'][act] + math.log(_d['rat'][0]))))
    phis = np.array(phis)
    mar = np.r_[avec[:33], math.pi - avec[:33], avec[33:42], math.pi / 2 - avec[33:42],
                al, math.pi - al, ww, math.pi - ww]
    return dict(R_model=float(r64), R_sector_min=float(R_sec.min()), R_sector_max=float(R_sec.max()),
                R_sector_spread=float(R_sec.max() - R_sec.min()),
                phi_branches=float(lam @ (d64['logg'][act] + math.log(d64['rat'][0]))),
                phi_root_min=float(phis.min()), phi_root_max=float(phis.max()),
                phi_root_spread=float(phis.max() - phis.min()),
                lin_res=float(abs(ns['eq'][:, :42] @ avec - ns['rhs']).max()),
                nonlin_res=float(abs(con64[13:21]).max()), max21_res=float(abs(con64).max()),
                margin=float(mar.min()), u=u0.tolist())

edge = []
for k in range(21):
    f = int(np.argmax(ns['U'][k, 42:62])); g = int(np.argmax(ns['V'][k, 42:62]))
    edge.append((f, g))
adj = {}
for k, (f, g) in enumerate(edge):
    adj.setdefault(f, []).append((g, k, 1)); adj.setdefault(g, []).append((f, k, -1))
Am = [[mp.mpf(float(x)) for x in row] for row in ns['A'][:, :42]]
Bm = [[mp.mpf(float(x)) for x in row] for row in ns['B'][:, :42]]

def mp_eval(avec):
    a = [mp.mpf(float(x)) for x in avec]
    Aa = [mp.fsum([Am[j][i] * a[i] for i in range(42)]) for j in range(21)]
    Ba = [mp.fsum([Bm[j][i] * a[i] for i in range(42)]) for j in range(21)]
    ls = [mp.log(mp.sin(Aa[j])) - mp.log(mp.sin(Ba[j])) for j in range(21)]
    logg = {0: mp.mpf(0)}; todo = [0]
    for f in todo:
        for (g, k, d) in adj[f]:
            if g not in logg:
                logg[g] = logg[f] + d * ls[k]; todo.append(g)
    assert len(logg) == 20
    cy = [logg[f] - logg[g] + ls[k] for k, (f, g) in enumerate(edge)]
    tree = radii(avec, 0)[2]
    cy_res = [cy[k] for k in range(21) if k not in tree]
    gsw = [logg[11 + i] for i in range(9)]
    alv = [mp.mpf(float(ns['ac'][i])) + mp.fsum([mp.mpf(float(ns['alpha'][i][j])) * a[j] for j in range(42)])
           for i in range(9)]
    ell = []
    for i in range(9):
        ui = mp.e ** gsw[(i - 1) % 9]; vi = mp.e ** gsw[i]
        ell.append(mp.sqrt(ui ** 2 + vi ** 2 - 2 * ui * vi * mp.cos(alv[i])))
    L = [mp.atan2(mp.e ** gsw[i] * mp.sin(alv[i]), mp.e ** gsw[(i - 1) % 9] - mp.e ** gsw[i] * mp.cos(alv[i]))
         for i in range(9)]
    w = []
    for i in range(9):
        s = mp.mpf(0)
        for j in range(9):
            s += (-1) ** ((j - i) % 9) * (mp.pi - (mp.pi - alv[j] - L[j]) - L[(j + 1) % 9] - 2 * a[33 + j])
        w.append(s)
    q = [2 * mp.sin(w[i] / 2) for i in range(9)]
    logg_max = max(logg.values()); Rat0 = q[0] / ell[0]
    R = mp.e ** logg_max * Rat0
    phi = mp.fsum([mp.mpf(float(lam[t])) * (logg[int(act[t])] + mp.log(Rat0)) for t in range(len(act))])
    circ = [q[i] / ell[i] / Rat0 - 1 for i in range(1, 7)]
    lin = [mp.fsum([mp.mpf(float(ns['eq'][j][i])) * a[i] for i in range(42)]) - mp.mpf(float(ns['rhs'][j]))
           for j in range(13)]
    return dict(R=str(R), phi=str(phi), phi_minus_logTcert=str(phi - mp.log(mp.mpf(Tcert_str))),
                cycle_res_max=str(max(abs(x) for x in cy_res)),
                circle_res_max=str(max(abs(x) for x in circ)),
                lin_res_max=str(max(abs(x) for x in lin)))

def verify(tag, avec):
    A1 = A1_eval(avec); A2 = mp_eval(avec)
    print('[%s] A1: R=%.15f (sectors spread %.1e)  Phi-logTcert=%+.6e  root-gauge spread=%.1e  '
          'max21res=%.1e margin=%.3f nact=%d'
          % (tag, A1['R_model'], A1['R_sector_spread'], A1['phi_branches'] - log_Tcert,
             A1['phi_root_spread'], A1['max21_res'], A1['margin'], int((np.array(A1['u']) > 1 - 1e-9).sum())))
    print('        A2: R=%s  Phi-logTcert=%s  cycle/circle/lin res max = %s / %s / %s'
          % (mp.nstr(mp.mpf(A2['R']), 20), mp.nstr(mp.mpf(A2['phi_minus_logTcert']), 10),
             A2['cycle_res_max'][:9], A2['circle_res_max'][:9], A2['lin_res_max'][:9]))
    return A1, A2

P1 = np.array(phase2['raws'][phase2['summary']['argmin_start']])
P1b = np.array(phase2['raws']['tangent_eps0.02'])          # strictly inside R<0.38 (by ~3e-8)
P2 = None
best_line = None
for r in phase2['hessian_diag']['line_search']:
    if 'phi_minus_logTcert' in r and (best_line is None or r['phi_minus_logTcert'] < best_line['phi_minus_logTcert']):
        best_line = r
P2 = np.array(best_line['a'])
V1 = verify('P1 boundary', P1)
V1b = verify('P1b inside', P1b)
V2 = verify('P2 descent', P2)
V0 = verify('C0 candidate', a0)

# ---------------------------------------------------------------- B: boundary refinement
def eval_all(y):
    a = a0 + Nr @ y
    r, con, d = shape(a)
    if not np.isfinite(r):
        return None
    al2, ww2 = d['alpha'], d['w']
    mar2 = np.r_[a[:33], math.pi - a[:33], a[33:42], math.pi / 2 - a[33:42],
                 al2, math.pi - al2, ww2, math.pi - ww2]
    if not np.all(np.isfinite(mar2)):
        return None
    g = d['logg'] + math.log(max(d['rat'][0], 1e-100))
    gg = np.exp(d['logg']); uu = gg / gg.max()
    return dict(margin=float(mar2.min()), R=float(r), res=float(abs(con).max()),
                phi=float(lam @ g[act]), spread=float(-(lam @ np.log(uu[act]))), a=a)

def obj(y):
    e = eval_all(y)
    return 1e3 if (e is None or e['margin'] <= 0) else e['phi']
def c_eq(y):
    e = eval_all(y)
    return np.full(8, 1e3) if e is None else shape(e['a'])[1][13:21]
def c_R(y):
    e = eval_all(y)
    return 1e3 if e is None else (e['R'] - R_MAIN)
def c_mar(y):
    e = eval_all(y)
    return -1e3 if e is None else (e['margin'] - MAR_FLOOR)

y1 = pinv(Nr) @ (P1 - a0)
for _ in range(40):                                        # land exactly on R = 0.38
    e = eval_all(y1)
    if e is None or abs(e['R'] - R_MAIN) < 1e-15:
        break
    J = np.array([(eval_all(y1 + np.eye(29)[k] * 1e-7)['R'] - e['R']) / 1e-7 for k in range(29)])
    y1 = y1 - J * (e['R'] - R_MAIN) / (J @ J)
o = minimize(obj, y1, method='SLSQP',
             constraints=[{'type': 'eq', 'fun': c_eq}, {'type': 'eq', 'fun': c_R},
                          {'type': 'ineq', 'fun': c_mar}],
             options={'maxiter': 400, 'ftol': 1e-15})
eb = eval_all(o.x)
print('[B1] boundary SLSQP (R=0.38 eq): ok=%s nit=%d  Phi-logTcert=%+.6e  R=%.15f spread=%.6e'
      % (bool(o.success), int(o.nit), eb['phi'] - log_Tcert, eb['R'], eb['spread']))

# Newton-reprojected projected-gradient descent on the boundary problem (max spread)
yy = y1.copy(); traj = []
for it in range(150):
    e = eval_all(yy)
    if e is None:
        break
    traj.append(dict(it=it, R=e['R'], spread=e['spread'], phi_minus_logTcert=e['phi'] - log_Tcert,
                     res=e['res'], margin=e['margin']))
    h = 1e-6
    gphi = np.array([(eval_all(yy + np.eye(29)[k] * h)['phi'] - eval_all(yy - np.eye(29)[k] * h)['phi']) / (2 * h)
                     for k in range(29)])
    Jc = np.column_stack([(shape(a0 + Nr @ (yy + np.eye(29)[k] * 1e-7))[1][13:21]
                           - shape(a0 + Nr @ yy)[1][13:21]) / 1e-7 for k in range(29)])
    a_now = a0 + Nr @ yy
    gR = np.array([(shape(a0 + Nr @ (yy + np.eye(29)[k] * h))[0] - shape(a0 + Nr @ (yy - np.eye(29)[k] * h))[0])
                   / (2 * h) for k in range(29)])
    Za = null_space(np.vstack([Jc, gR[None, :]]))
    if Za.shape[1] == 0:
        break
    d = -(Za @ (Za.T @ gphi)); nrm = np.linalg.norm(d)
    if nrm < 1e-13:
        break
    d = d / nrm
    step = 5e-4
    for _try in range(30):
        ynew = yy + step * d
        for _np in range(6):                              # Newton re-projection
            e2 = eval_all(ynew)
            if e2 is None:
                break
            J2 = np.column_stack([(shape(a0 + Nr @ (ynew + np.eye(29)[k] * 1e-7))[1][13:21]
                                   - shape(a0 + Nr @ ynew)[1][13:21]) / 1e-7 for k in range(29)])
            J2R = np.array([(shape(a0 + Nr @ (ynew + np.eye(29)[k] * 1e-7))[0]
                             - shape(a0 + Nr @ ynew)[0]) / 1e-7 for k in range(29)])
            F = np.r_[shape(a0 + Nr @ ynew)[1][13:21], e2['R'] - R_MAIN]
            Jm = np.vstack([J2, J2R[None, :]])
            ynew = ynew - pinv(Jm) @ F
        enew = eval_all(ynew)
        if (enew is not None and enew['margin'] > MAR_FLOOR and enew['res'] < 1e-11
                and abs(enew['R'] - R_MAIN) < 1e-12 and enew['phi'] < e['phi'] - 1e-16):
            yy = ynew; break
        step *= 0.5
    else:
        break
print('[B2] Newton-reprojected boundary descent: %d steps, best Phi-logTcert=%+.6e, spread max=%.6e'
      % (len(traj), min(t['phi_minus_logTcert'] for t in traj), max(t['spread'] for t in traj)))
for t in traj[::max(1, len(traj) // 8)]:
    print('     it=%-3d R=%.15f spread=%.6e Phi-logTcert=%+.6e res=%.1e' %
          (t['it'], t['R'], t['spread'], t['phi_minus_logTcert'], t['res']))

out = dict(scope='phase-2 follow-up: independent verification of P1/P1b/P2/candidate + boundary refinement; numeric only',
           points=dict(P1=dict(start=phase2['summary']['argmin_start'], A1=V1[0], A2=V1[1]),
                       P1b=dict(label='strictly inside R<=0.38 (R ~ 0.38-3e-8)', A1=V1b[0], A2=V1b[1]),
                       P2=dict(label='deepest legal descent point from 21-dim reduced-Hessian line search',
                               R_float=float(best_line['R']),
                               phi_minus_logTcert_float=float(best_line['phi_minus_logTcert']),
                               A1=V2[0], A2=V2[1]),
                       C0=dict(label='saved candidate float64 angle vector', A1=V0[0], A2=V0[1],
                               C529_exact=C529_str, Tcert_exact=Tcert_str)),
           B_boundary_SLSQP=dict(success=bool(o.success), nit=int(o.nit), R=eb['R'],
                                 phi_minus_logTcert=eb['phi'] - log_Tcert, spread=eb['spread'],
                                 res=eb['res'], margin=eb['margin']),
           B_boundary_descent_trace=traj, runtime_s=round(time.time() - T0, 1))
(OUT / 'phase2_refine_verify.json').write_text(json.dumps(out, indent=2))
print('[done] %.1f s -> out/phase2_refine_verify.json' % (time.time() - T0))
