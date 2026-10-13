import json
import sys
import numpy as np
sys.path.insert(0, r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2")
import envelope_clean as EC

out = {}
out['self_test'] = EC.self_test()
print(json.dumps(out['self_test'], indent=1, default=float))

pts = {
    'lead_cand': [0.9223829833, 1.1925065472, 1.1925065472],
    'diag_pi3': [EC.PI / 3] * 3,
    'diag_pi2': [EC.PI / 2] * 3,
    'diag_1.2': [1.2] * 3,
    'diag_2pi3-': [2 * EC.PI / 3 - 1e-9] * 3,
    'crit_2pi3_2pi3_pi3': [2 * EC.PI / 3, 2 * EC.PI / 3, EC.PI / 3],
    'junction_opt_guess': [EC.PI / 2, EC.PI / 2, EC.PI / 2],
    'corner_pi_eps': [EC.PI - 1e-9, 1e-9, 1e-9],
    'first_br_opt': [2.0, 0.5708, 0.5708],
    'first_br_opt2': [2.186276035465284, 0.477658309062254, 0.477658309062254],
}
out['spot'] = {k: EC.spot(v) for k, v in pts.items()}
print(json.dumps(out['spot'], indent=1, default=float))

with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\clean_self_test.json", 'w') as f:
    json.dump(out, f, indent=1, default=float)
