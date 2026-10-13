"""Driver: run the audit pieces and dump JSON + readable summary."""
import json
import sys
import time
import numpy as np

sys.path.insert(0, r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2")
import audit_envelope as AE

out = {}
t0 = time.time()
out['self_test'] = AE.self_test()
print('self_test done', time.time() - t0, flush=True)

out['diag'] = AE.diag_checks()
print('diag done', time.time() - t0, flush=True)

best_dir, arg_dir = AE.search_directions(seed=2026, n_restart=120, sweeps=1200)
out['direction_search'] = dict(best=best_dir, arg=arg_dir.tolist(),
                               profile=AE.ray_profile(arg_dir))
out['direction_search']['profile']['d'] = arg_dir.tolist()
print('direction search done', best_dir, arg_dir, time.time() - t0, flush=True)

out['grid'] = AE.grid_scan(ns=200, nu=200, seed=11)
out['grid']['junction_arg'] = out['grid']['junction_arg'].tolist()
out['grid']['mc_arg'] = out['grid']['mc_arg'].tolist()
print('grid done', out['grid']['junction_best'], time.time() - t0, flush=True)

# candidate / critical point spot values
pts = {
    'diag_pi3': [AE.PI / 3] * 3,
    'diag_pi2': [AE.PI / 2] * 3,
    'diag_2pi3': [2 * AE.PI / 3] * 3,
    'lead_cand': [0.9223829833, 1.1925065472, 1.1925065472],
    'crit_2pi3_2pi3_pi3': [2 * AE.PI / 3, 2 * AE.PI / 3, AE.PI / 3],
    'corner_pi_0_0': [AE.PI - 1e-9, 1e-9, 1e-9],
    'junction_2.186_0.478_0.478': [2.186276035465284, 0.477658309062254, 0.477658309062254],
    'first_branch_opt': [2.0, 0.5708, 0.5708],
}
out['spot'] = {}
for k, p in pts.items():
    A, x0, a, b, c = AE.envelope(p, return_extra=True)
    out['spot'][k] = dict(beta=p, sum=float(sum(p)), a=float(a), b=float(b), c=float(c),
                          x0=float(x0), A=float(A), H_at_x0=float(AE.H(p, float(x0))))

with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\audit_numbers.json", 'w') as f:
    json.dump(out, f, indent=1, default=float)

print(json.dumps(out['self_test'], indent=1, default=float))
print(json.dumps({k: v for k, v in out['diag'].items() if k != 'convexity_witnesses'},
                 indent=1, default=float))
print(json.dumps(out['diag']['convexity_witnesses'], indent=1, default=float))
print(json.dumps(out['direction_search'], indent=1, default=float))
print(json.dumps(out['grid'], indent=1, default=float))
print(json.dumps(out['spot'], indent=1, default=float))
print('total time', time.time() - t0)
