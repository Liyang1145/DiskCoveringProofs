"""Evaluate the lead weighted-stress functional Phi_lambda = sum_f lam_f log gamma_f + mu.C
at (i) the candidate, (ii) all 20 phase-1 witnesses.  Evaluations only - no new optimisation.
Purpose: compare the two sufficient-inequality channels
   (A) sector-capacity:  log R >= log D_i (per sector)   [falsified in phase 1]
   (B) weighted stress:  log R >= Phi_lambda(a)          [lead's channel]
via the identity   log R = Phi_lambda + spread,  spread = log M - sum_f lam_f log u_f >= 0.
Read-only reuse of lead model + lead KKT weights; writes only in r20-stress/out.
"""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
from scipy.linalg import null_space
W = Path(__file__).parent; LEAD = W.parent / 'lead'; OUT = W / 'out'
zz = {'__file__': str(LEAD / 'angle_stress_probe.py')}
exec((LEAD / 'angle_stress_probe.py').read_text(encoding='utf-8').split('y0=np.zeros(29)')[0], zz)
ns, shape, branches, N, a0, lam, mu, act = [zz[k] for k in ['ns', 'shape', 'branches', 'N', 'a0', 'lam', 'mu', 'act']]
con0 = shape(a0)[1]
print('lead stationarity error', zz['station'], ' lam>0', float(lam.min()), ' |act|', len(act))

def stress(a):
    g, c = branches(a)
    return float(lam @ g[act] + mu @ c)

def report(name, a):
    r, con, d = shape(a)
    g = np.exp(d['logg']); M = g.max(); u = g / M
    s = stress(a)
    spread = math.log(M) - float(lam @ np.log(g[act]))
    return dict(name=name, R=float(r), logR=float(math.log(r)), stress=s, spread=float(spread),
                logR_minus_stress=float(math.log(r) - s), logR_minus_stress_over_R0=float(math.log(r) - s - math.log(0.37998385311983757)),
                max_slack=float(1 - u.min()), n_active_ceiling=int((u > 1 - 1e-9).sum()),
                res=float(abs(con).max()))

rows = [report('candidate', a0)]
for src, tag in [('mechanism_test.json', 'run'), ('phase1_runs.json', 'cond')]:
    data = json.loads((OUT / src).read_text())
    for i, r in enumerate(data['runs']):
        rows.append(report('%s%02d delta=%s' % (tag, i, r.get('delta', '')), np.array(r['a'])))
for row in rows:
    print('%-22s R=%.9f  stress=%.9f  logR-stress=%.3e  spread=%.4f  nceil=%2d  res=%.1e'
          % (row['name'], row['R'], row['stress'], row['logR_minus_stress'], row['spread'],
             row['n_active_ceiling'], row['res']))
bad = [r for r in rows if r['logR_minus_stress'] < 0]
print('rows with stress > log R (violates chain):', len(bad))
ok = [r for r in rows[1:] if r['stress'] >= math.log(0.37998385311983757)]
print('witnesses with stress >= log C529 :', len(ok), 'of', len(rows) - 1)
(OUT / 'stress_at_witnesses.json').write_text(json.dumps(
    dict(scope='evaluation of lead stress at phase-1 witnesses; numeric only',
         log_C529=math.log(0.37998385311983757), rows=rows), indent=2))
