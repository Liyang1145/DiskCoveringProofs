"""Independent verification of the strongest witness from mechanism_test.py + extra diagnostics:
 (a) all 21 equality residuals, (b) positivity margins with argmin, (c) u / caps / D validity,
 (d) numeric box-sampling check of the convexity cap Lambda_i >= ell_i,
 (e) multi-step (path/Bellman-Ford) propagated caps ub_f = min over paths of sine-ratio products,
     and the resulting D-functionals, (f) cyclic quantities.
Read-only reuse of lead model; writes only in r20-stress/out.
"""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
W = Path(__file__).parent; LEAD = W.parent / 'lead'; OUT = W / 'out'
zz = {'__file__': str(LEAD / 'check_angle_only.py')}
exec((LEAD / 'check_angle_only.py').read_text(encoding='utf-8').split("a=ns['x0'][:42]")[0], zz)
ns, shape = zz['ns'], zz['shape']
faces = ns['faces']; edges = ns['edges']
a0 = ns['x0'][:42]
R0 = float(shape(a0)[0])
data = json.loads((OUT / 'mechanism_test.json').read_text())
best = min(data['runs'], key=lambda r: r['maxD1'])
a = np.array(best['a'])

r, con, d = shape(a)
g = np.exp(d['logg']); M = g.max(); u = g / M
usw = u[11:20]
al, ww = d['alpha'], d['w']
ell = np.array([math.sqrt(usw[(i - 1) % 9] ** 2 + usw[i] ** 2
                          - 2 * usw[(i - 1) % 9] * usw[i] * math.cos(al[i])) for i in range(9)])
q = 2 * np.sin(ww / 2)
Ri = q / ell
caps = np.zeros(9); Aang = np.zeros(9)
for i in range(9):
    e = tuple(sorted((i, (i + 1) % 9)))
    for t, f in enumerate(faces):
        if e[0] in f and e[1] in f:
            k = f.index(next(v for v in f if v not in e))
            Aang[i] = a[3 * t + k]
            caps[i] = min(1.0, math.sin(Aang[i]) / math.sin(a[33 + i]))
            break
Lam0 = np.maximum(1.0, 2 * np.sin(al / 2))
D0 = q / Lam0
Lam1 = np.array([max(caps[(i - 1) % 9], caps[i],
                     math.sqrt(caps[(i - 1) % 9] ** 2 + caps[i] ** 2
                               - 2 * caps[(i - 1) % 9] * caps[i] * math.cos(al[i]))) for i in range(9)])
D1 = q / Lam1

# ---- (e) multi-step propagated caps: log ub_f = min over paths of sum of edge logs, capped at 0
# edge ratios: for each of the 21 site-site edges, ratio r_e = u_g/u_f = sin(A_f)/sin(A_g)
# (internal: both site faces; boundary: face<->switch with switch angle b)
nodes = 20
Rlat = np.full((nodes, nodes), np.inf)
for ei, (i, j) in enumerate(edges):
    adj = []
    for t, f in enumerate(faces):
        if i in f and j in f:
            k = f.index(next(v for v in f if v not in (i, j)))
            adj.append((t, a[3 * t + k]))
    if len(adj) == 2:
        (t1, A1), (t2, A2) = adj
        # u_{t2}/u_{t1} = sin A1/sin A2 ; log ratio
        lr = math.log(math.sin(A1)) - math.log(math.sin(A2))
        Rlat[t1, t2] = lr; Rlat[t2, t1] = -lr
    else:
        bi = next(b for b in range(9) if {b, (b + 1) % 9} == {i, j})
        (t1, A1), = adj
        lr = math.log(math.sin(A1)) - math.log(math.sin(a[33 + bi]))   # u_sw/u_face
        Rlat[t1, 11 + bi] = lr; Rlat[11 + bi, t1] = -lr
# Bellman-Ford style: log ub_f = min over paths of sum(log ratio), starting from 1 at any node
logub = np.zeros(nodes)          # ub <= 1
for _ in range(nodes + 5):
    upd = False
    for f in range(nodes):
        for h in range(nodes):
            if np.isfinite(Rlat[f, h]) and logub[h] - Rlat[f, h] < logub[f] - 1e-15:
                logub[f] = logub[h] - Rlat[f, h]; upd = True
    if not upd:
        break
ub = np.exp(np.minimum(logub, 0.0))
ubsw = ub[11:20]
Lam_p = np.array([max(ub[(i - 1) % 9], ub[i],
                      math.sqrt(ub[(i - 1) % 9] ** 2 + ub[i] ** 2
                                - 2 * ub[(i - 1) % 9] * ub[i] * math.cos(al[i]))) for i in range(9)])
Dp = q / Lam_p

# validity controls: u <= caps, u <= ub, and R >= D
ctrl = dict(max_u_minus_caps=float((u[11:20] - caps).max()),
            max_u_minus_ub=float((u - ub).max()),
            min_R_minus_D1=float(r - D1.max()), min_R_minus_Dp=float(r - Dp.max()))

# ---- (d) numeric box check of Lambda >= ell : sample box [0,c]^2
rng = np.random.default_rng(7); worst = []
for i in range(9):
    lo = (caps[(i - 1) % 9], caps[i])
    mx = Lam1[i]
    for _ in range(4000):
        uu = rng.uniform(0, lo[0]); vv = rng.uniform(0, lo[1])
        val = math.sqrt(uu ** 2 + vv ** 2 - 2 * uu * vv * math.cos(al[i]))
        mx = max(mx, val)
    worst.append(float(mx - max(lo[0], lo[1], math.sqrt(lo[0] ** 2 + lo[1] ** 2 - 2 * lo[0] * lo[1] * math.cos(al[i])))))

# ---- (c) positivity margins with argmin
pos = []
for k in range(33):
    pos.append(('a[%d]' % k, float(a[k])))
    pos.append(('pi-a[%d]' % k, float(math.pi - a[k])))
for k in range(33, 42):
    pos.append(('a[%d]' % k, float(a[k])))
    pos.append(('pi/2-a[%d]' % k, float(math.pi / 2 - a[k])))
for i in range(9):
    pos.append(('alpha[%d]' % i, float(al[i])))
    pos.append(('pi-alpha[%d]' % i, float(math.pi - al[i])))
    pos.append(('w[%d]' % i, float(ww[i])))
    pos.append(('pi-w[%d]' % i, float(math.pi - ww[i])))
pos.sort(key=lambda t: t[1])

# ---- cycle residuals (the two non-tree sine products)
tree, other = d['tree'], d['other']
logg, cy = d['logg'], d['cycle']

out = dict(scope='independent check of the R20 witness; numeric calibration only',
           witness_source=dict(found_by='mechanism_test.py bounded SLSQP', eps0=best['eps0'], seed=best['seed']),
           R=float(r), R0_reference=R0, R_minus_R0=float(r - R0),
           max_abs_residual_21=float(abs(con).max()),
           max_abs_residual_8nonlinear=float(abs(con[13:21]).max()),
           positivity_min=pos[0], positivity_second=pos[1],
           cycle_residuals=cy.tolist(),
           u_norm=u.tolist(), u_switch=usw.tolist(),
           caps_one_step=caps.tolist(), ub_propagated=ub.tolist(),
           alpha_deg=(al * 180 / math.pi).tolist(), w_deg=(ww * 180 / math.pi).tolist(),
           b_deg=(a[33:42] * 180 / math.pi).tolist(),
           ell=ell.tolist(), q=q.tolist(), Ri_over_R=(Ri / r).tolist(),
           Lam0=Lam0.tolist(), D0=D0.tolist(), Lam1=Lam1.tolist(), D1=D1.tolist(),
           Lam_prop=Lam_p.tolist(), D_prop=Dp.tolist(),
           max_D0=float(D0.max()), max_D1=float(D1.max()), max_D_prop=float(Dp.max()),
           validity_controls=ctrl,
           box_sampling_max_excess=worst,
           a=a.tolist())
(OUT / 'witness_check.json').write_text(json.dumps(out, indent=2))

print('witness: R = %.15f   R0 = %.15f   R - R0 = %+.3e' % (r, R0, r - R0))
print('max|residual| all 21 = %.3e   nonlinear 8 = %.3e' % (abs(con).max(), abs(con[13:21]).max()))
print('positivity: tightest =', pos[0], ' second =', pos[1])
print('cycle residuals =', np.round(cy, 18).tolist())
print('u (20)          =', np.round(u, 9).tolist())
print('caps (9)        =', np.round(caps, 9).tolist())
print('ub propagated   =', np.round(ub, 9).tolist())
print('max D0 = %.12f   max D1 = %.12f   max D_prop = %.12f   (R0 = %.12f)' % (D0.max(), D1.max(), Dp.max(), R0))
print('validity        =', {k: '%.2e' % v for k, v in ctrl.items()})
print('box-check excess (should be ~0) =', ['%.2e' % x for x in worst])
print('alpha deg =', np.round(al * 180 / math.pi, 4).tolist())
print('w deg     =', np.round(ww * 180 / math.pi, 4).tolist())
