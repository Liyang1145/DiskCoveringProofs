"""Evaluation of canonical weight choices in the weighted-spread channel
   Phi_lambda = sum_f lambda_f log gamma_f + log q_0 - log ell_0   (<= log R).
Candidates:
  U20  uniform on all 20 factors
  U18  uniform on the 18 candidate-active factors {0,1,2,3,4,6,8,9,10,11..19}
  U9   uniform on the 9 switch factors {11..19}
  KKT  lead's numeric multipliers (angle_stress_probe stationarity solve)
Evaluated at the candidate and at all 20 phase-1 witnesses.  Evaluations only, no new search.
"""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
W = Path(__file__).parent; LEAD = W.parent / 'lead'; OUT = W / 'out'
zz = {'__file__': str(LEAD / 'angle_stress_probe.py')}
exec((LEAD / 'angle_stress_probe.py').read_text(encoding='utf-8').split('y0=np.zeros(29)')[0], zz)
ns, shape, branches, a0 = zz['ns'], zz['shape'], zz['branches'], zz['a0']
lam_kkt, mu, act = zz['lam'], zz['mu'], zz['act']
ACTSET = [0, 1, 2, 3, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
log_C529 = math.log(0.37998385311983757)

def phis(a):
    g, c = branches(a)
    L = np.log(g)
    return dict(U20=float(np.mean(L) + 0) , U18=None, U9=None, KKT=None)

def eval_all(a):
    """branches(a)[0] already returns b_f = log gamma_f + log(rat[0]);  Phi_lambda = lambda @ b."""
    g, c = branches(a)
    out = {}
    out['U20'] = float(g.mean())
    out['U18'] = float(g[[i for i in ACTSET]].mean())
    out['U9'] = float(g[11:20].mean())
    out['KKT'] = float(lam_kkt @ g[act])
    return out

rows = []
r, con, d = shape(a0)
rows.append(('candidate', a0, float(r)))
for src, tag in [('mechanism_test.json', 'run'), ('phase1_runs.json', 'cond')]:
    data = json.loads((OUT / src).read_text())
    for i, rr in enumerate(data['runs']):
        rows.append(('%s%02d' % (tag, i), np.array(rr['a']), float(rr['R'])))

summary = {}
for name, a, R in rows:
    vals = eval_all(a)
    logR = math.log(R)
    rec = {k: dict(phi=v, margin_vs_logC529=v - log_C529, spread=logR - v) for k, v in vals.items()}
    summary[name] = dict(R=R, logR=logR, **{f'{k}_phi': v['phi'] for k, v in rec.items()},
                         **{f'{k}_margin': v['margin_vs_logC529'] for k, v in rec.items()})
    if name == 'candidate':
        print('candidate  R=%.15f' % R)
        for k, v in rec.items():
            print('   %-4s phi=%.12f  phi-logR=%+.3e  spread=%.3e' % (k, v['phi'], v['phi'] - logR, v['spread']))
w = [v for k, v in summary.items() if k != 'candidate']
for k in ['U20', 'U18', 'U9', 'KKT']:
    mg = [v[f'{k}_margin'] for v in w]
    print('%-4s over 20 witnesses: margin vs logC529 min=%+.3e max=%+.3e  n_negative=%d'
          % (k, min(mg), max(mg), sum(1 for x in mg if x < 0)))
(OUT / 'canonical_weights.json').write_text(json.dumps(dict(log_C529=log_C529, rows=summary), indent=2))
