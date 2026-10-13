"""Robustness control for the phase-2 reduced-Hessian reading (step-size dependence).
Recomputes the 21-dim reduced Hessian of Phi_KKT at the candidate with two gradient steps
and two Hessian steps, and re-checks the deepest line-search point's legality.
Writes only inside research-2026/team-current/r20-stress/out.
"""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
from scipy.linalg import null_space

W = Path(__file__).parent; LEAD = W.parent / 'lead'; OUT = W / 'out'
zz = {'__file__': str(LEAD / 'check_angle_only.py')}
exec((LEAD / 'check_angle_only.py').read_text(encoding='utf-8').split("a=ns['x0'][:42]")[0], zz)
ns, shape = zz['ns'], zz['shape']
zz2 = {'__file__': str(LEAD / 'angle_stress_probe.py')}
exec((LEAD / 'angle_stress_probe.py').read_text(encoding='utf-8').split('y0=np.zeros(29)')[0], zz2)
Nr, a0, lam, act = zz2['N'], ns['x0'][:42], zz2['lam'], zz2['act']

def phi(y, floor=1e-6):
    a = a0 + Nr @ y
    r, con, d = shape(a)
    if not np.isfinite(r):
        return 1e3
    al, ww = d['alpha'], d['w']
    mar = min(a[:33].min(), (math.pi - a[:33]).min(), a[33:42].min(), (math.pi / 2 - a[33:42]).min(),
              al.min(), (math.pi - al).min(), ww.min(), (math.pi - ww).min())
    if mar <= floor:
        return 1e3
    return float(lam @ (d['logg'][act] + math.log(max(d['rat'][0], 1e-100))))

J8 = np.column_stack([(shape(a0 + Nr @ (np.eye(29)[k] * 1e-6))[1][13:21]
                       - shape(a0 - Nr @ (np.eye(29)[k] * 1e-6))[1][13:21]) / (2e-6) for k in range(29)])
Z = null_space(J8)
res = []
for hg in (1e-5, 1e-4):
    for hh in (1e-4, 5e-4):
        def grad(y):
            return np.array([(phi(y + np.eye(29)[k] * hg) - phi(y - np.eye(29)[k] * hg)) / (2 * hg)
                             for k in range(29)])
        H = np.column_stack([(grad(np.eye(29)[k] * hh) - grad(-np.eye(29)[k] * hh)) / (2 * hh)
                             for k in range(29)])
        H = 0.5 * (H + H.T)
        ev = np.linalg.eigvalsh(Z.T @ H @ Z)
        res.append(dict(h_grad=hg, h_hess=hh, min_eig=float(ev.min()), max_eig=float(ev.max()),
                        n_neg=int((ev < -1e-8).sum())))
        print('h_grad=%.0e h_hess=%.0e  min=%.6f max=%.6f n_neg=%d' % (hg, hh, ev.min(), ev.max(), int((ev < -1e-8).sum())))
# deepest line-search point legality (from phase2 JSON)
p2 = json.loads((OUT / 'phase2_stress_domain.json').read_text())
bl = min([r for r in p2['hessian_diag']['line_search'] if 'phi_minus_logTcert' in r],
         key=lambda r: r['phi_minus_logTcert'])
a2 = np.array(bl['a'])
r, con, d = shape(a2)
al, ww = d['alpha'], d['w']
mar = min(a2[:33].min(), (math.pi - a2[:33]).min(), a2[33:42].min(), (math.pi / 2 - a2[33:42]).min(),
          al.min(), (math.pi - al).min(), ww.min(), (math.pi - ww).min())
print('deepest line point: R=%.15f  max|21res|=%.2e  margin=%.4f  Phi-logTcert=%.6e'
      % (r, abs(con).max(), mar, float(lam @ (d['logg'][act] + math.log(d['rat'][0]))) - (-0.9676265189544054)))
out = dict(scope='robustness control for reduced Hessian + deepest line point; numeric',
           hessian=res, deepest_line=dict(R=float(r), max21_res=float(abs(con).max()), margin=float(mar),
                                          phi_minus_logTcert=float(lam @ (d['logg'][act] + math.log(d['rat'][0]))) + 0.9676265189544054))
(OUT / 'check_hessian_robustness.json').write_text(json.dumps(out, indent=2))
print('written out/check_hessian_robustness.json')
