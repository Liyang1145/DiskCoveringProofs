"""Phase-0 scope audit of the phase-1 M1 report (READ-ONLY, no optimisation, no lead files touched).

Checks performed (all against saved outputs + lead model, no rerun of any phase-1 search):
  1. existence check for any phase-2 output (the obligated second-stage run);
  2. recompute R at all 20 stored phase-1 witnesses with the lead model and compare with the
     recorded R, and test the load-bearing scope question: is every witness OUTSIDE the
     main domain {R_shape <= 0.38}?
  3. exact-threshold audit: C249 Tcert vs C529 vs the float64 constant 0.37998385311983757
     actually used in r20-stress/stress_eval.py & canonical_weights.py;
  4. the "+0.65" second-order coefficient: locate it in the saved scan and count the sampled
     directions / step sizes (finite-direction scan).
Writes only inside research-2026/team-current/r20-stress/.
"""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp

W = Path(__file__).parent; LEAD = W.parent / 'lead'; OUT = W / 'out'

zz = {'__file__': str(LEAD / 'check_angle_only.py')}
exec((LEAD / 'check_angle_only.py').read_text(encoding='utf-8').split("a=ns['x0'][:42]")[0], zz)
ns, shape = zz['ns'], zz['shape']
a0 = ns['x0'][:42]

rep = {'scope': 'phase-0 scope audit of r20-stress phase 1; numeric, read-only'}

# ---- 1. phase-2 output existence -------------------------------------------------------
p2 = sorted([p.name for p in OUT.glob('*') if 'phase2' in p.name.lower()])
rep['phase2_outputs_present'] = p2
all_out = sorted(p.name for p in OUT.glob('*'))
rep['out_listing'] = all_out

# ---- 2. witness radii vs the 0.38 main-domain boundary ---------------------------------
rows = []
mt = json.loads((OUT / 'mechanism_test.json').read_text())
p1 = json.loads((OUT / 'phase1_runs.json').read_text())
for src, tag, data in [('mechanism_test.json', 'm', mt), ('phase1_runs.json', 'c', p1)]:
    for i, r in enumerate(data['runs']):
        a = np.array(r['a'])
        assert a.shape == (42,)
        Rm, con, det = shape(a)
        rows.append(dict(id='%s%02d' % (tag, i), src=src, R_recorded=float(r['R']), R_recompute=float(Rm),
                         dr_R=float(Rm - r['R']), res=float(abs(con).max()),
                         outside_038=bool(Rm > 0.38), R_minus_038=float(Rm - 0.38)))
Rs = np.array([x['R_recompute'] for x in rows])
rep['n_witnesses'] = len(rows)
rep['witness_R_min'] = float(Rs.min()); rep['witness_R_max'] = float(Rs.max())
rep['n_witnesses_outside_038'] = int(sum(1 for x in rows if x['outside_038']))
rep['max_abs_recompute_minus_recorded_R'] = float(max(abs(x['dr_R']) for x in rows))
rep['max_residual_at_witnesses'] = float(max(x['res'] for x in rows))
rep['witnesses'] = rows
# the two witnesses cited in the report
rep['best_maxD1_witness'] = min(mt['runs'], key=lambda r: r['maxD1'])['maxD1']
rep['best_maxD1_R'] = min(mt['runs'], key=lambda r: r['maxD1'])['R']
rep['best_nonflat_maxD1'] = min([r['maxD1'] for r in p1['runs'] if r['delta'] > 0])
rep['best_nonflat_R'] = min([r for r in p1['runs'] if r['delta'] > 0], key=lambda r: r['maxD1'])['R']

# ---- 3. exact threshold audit -----------------------------------------------------------
Tcert_str = '0.3799838531198386897222616061360932143087189561522153170163892'
C529_str = '0.379983853119838709048518179573429853811597902801556119905385'
const_used = 0.37998385311983757          # literal in stress_eval.py / canonical_weights.py
R_model_a0 = float(shape(a0)[0])
mp.mp.dps = 60
d_T_C = mp.mpf(Tcert_str) - mp.mpf(C529_str)
rep['threshold_audit'] = dict(
    Tcert_float64=repr(float(Tcert_str)), C529_float64=repr(float(C529_str)),
    R_model_at_candidate=repr(R_model_a0),
    Tcert_minus_C529_exact=str(d_T_C),
    const_used_repr=repr(const_used),
    const_used_minus_Tcert_exact=str(mp.mpf(const_used) - mp.mpf(Tcert_str)),
    const_used_minus_Tcert_in_log=str(mp.log(mp.mpf(const_used)) - mp.log(mp.mpf(Tcert_str))),
    R_model_minus_Tcert_exact=str(mp.mpf(repr(R_model_a0)) - mp.mpf(Tcert_str)),
    R_model_minus_C529_exact=str(mp.mpf(repr(R_model_a0)) - mp.mpf(C529_str)),
    log_038_minus_log_Tcert=str(mp.log(mp.mpf('0.38')) - mp.log(mp.mpf(Tcert_str))),
    log_Tcert_minus_log_038=float(mp.log(mp.mpf(Tcert_str)) - mp.log(mp.mpf('0.38'))),
)
rep['threshold_audit']['spread_budget_at_R038'] = float(mp.log(mp.mpf('0.38')) - mp.log(mp.mpf(Tcert_str)))

# ---- 4. the finite-direction second-order scan ------------------------------------------
scan = mt['scan']
dirs = [(s['k'], s['kind']) for s in scan]
n_eps = len(scan[0]['rows'])
sec = [r['second_order'] for s in scan for r in s['rows'] if 'second_order' in r]
sec_ok = [r for s in scan for r in s['rows'] if 'second_order' in r]
best = min(sec_ok, key=lambda r: r['second_order'])
rep['second_order_scan'] = dict(
    n_directions=len(scan), n_basis=sum(1 for k, kind in dirs if kind == 'basis'),
    n_random=sum(1 for k, kind in dirs if kind == 'random'), n_eps=n_eps,
    eps_values=sorted({r['eps'] for s in scan for r in s['rows'] if 'second_order' in r}),
    n_evals_with_second_order=len(sec), min_second_order=float(best['second_order']),
    max_second_order=float(max(sec)), n_second_order_le_0=int(sum(1 for x in sec if x <= 0)),
    best_eps=best['eps'], note='pointwise secant coefficient (maxD1-R0)/eps^2, NOT a curvature certificate')
v_bad = [r for s in scan for r in s['rows'] if 'maxD1' in r and r['maxD1'] < mt['r_star'] - 1e-9]
rep['second_order_scan']['n_sampled_points_with_maxD1_below_R0'] = len(v_bad)
rep['second_order_scan']['R0_reference'] = mt['r_star']

(OUT / 'audit_scope_phase0.json').write_text(json.dumps(rep, indent=2))
print(json.dumps({k: v for k, v in rep.items() if k not in ('witnesses', 'out_listing')}, indent=2))
print('--- witnesses ---')
for x in rows:
    print('%-4s R=%.15f  (R-0.38)=%+.3e  |res|=%.1e  outside038=%s' %
          (x['id'], x['R_recompute'], x['R_minus_038'], x['res'], x['outside_038']))
