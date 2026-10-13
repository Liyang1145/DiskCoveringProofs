"""Verify the lead's corrections on the analytic facts, then record them."""
import json
import sys
import numpy as np
sys.path.insert(0, r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2")
import direct_v2 as D2
PI = np.pi

out = {}

# --- (1) diagonal closed form, corrected sign; derivatives
# x0 = cos t + sin t/sqrt3 ; A = 3 sin t cos t + sqrt3 sin^2 t
def Acls(t):
    return 3 * np.sin(t) * np.cos(t) + np.sqrt(3) * np.sin(t) ** 2
def dA(t):
    return 3 * np.cos(2 * t) + np.sqrt(3) * np.sin(2 * t)
def d2A(t):
    return -6 * np.sin(2 * t) + 2 * np.sqrt(3) * np.cos(2 * t)

ts = np.linspace(PI / 3, 2 * PI / 3 - 1e-9, 200001)
Acode = np.array([D2.inner_max([t, t, t], nx=2001)['A'] for t in ts[::200]])
out['closedform_check'] = dict(
    max_abs_diff=float(np.max(np.abs(Acode - Acls(ts[::200])))))
out['x0_closedform'] = dict(
    formula='cos t + sin t/sqrt3',
    check_at_1p2=float(np.cos(1.2) + np.sin(1.2) / np.sqrt(3)),
    code_at_1p2=float(D2.x0_cross([1.2] * 3)))
out['derivs'] = dict(
    dA_at_pi3=float(dA(PI / 3)), d2A_at_pi3=float(d2A(PI / 3)),
    d2A_zero_t=float(np.arctan(1 / np.sqrt(3)) if False else 7 * PI / 12),
    d2A_at_7pi12=float(d2A(7 * PI / 12)),
    d2A_at_2pi3=float(d2A(2 * PI / 3)),
    d2A_at_1p2=float(d2A(1.2)),
    concavity_interval='A"<=0 on (pi/3, 7pi/12], A">0 on (7pi/12, 2pi/3)')

# --- (2) concavity: midpoint ABOVE the chord is consistent with concavity;
# the correct non-concavity witness is A" > 0 near 2pi/3
w = []
for (t1, t2) in [(1.9, 2.05), (1.85, 2.05), (2.0, 2.09), (0.3, 1.5)]:
    tm = 0.5 * (t1 + t2)
    a1, am, a2 = Acls(t1), Acls(tm), Acls(t2)
    w.append(dict(t1=t1, t2=t2, A1=float(a1), A_mid=float(am), A2=float(a2),
                  chord_mid=float(0.5 * (a1 + a2)), mid_minus_chord=float(am - 0.5 * (a1 + a2))))
out['witnesses'] = w

# --- (3) A <= min(3 sin(B/3), 3 sqrt3/2) : check over the domain, and where the
# min switches
rng = np.random.default_rng(5)
sw, mx = None, 0.0
tested = 0
for _ in range(4000):
    b = np.clip(rng.dirichlet(np.ones(3) * 1.5) * rng.uniform(0.1, 6.28), 1e-4, PI - 1e-4)
    if b.sum() >= 2 * PI - 1e-9:
        continue
    r = D2.inner_max(b, nx=801)
    B = float(b.sum())
    bound = min(3 * np.sin(B / 3), 3 * np.sqrt(3) / 2)
    tested += 1
    if r['A'] > bound + 1e-9:
        mx = max(mx, r['A'] - bound)
    if sw is None or abs(B - 3 * PI / 2) < abs(sw - 3 * PI / 2):
        sw = B
out['bound_check'] = dict(n_tested=tested, max_violation=float(mx),
                          nearest_B_to_3pi2=float(sw),
                          value_at_B=float(min(3 * np.sin(sw / 3), 3 * np.sqrt(3) / 2)),
                          note='min switches at B=3pi/2')

# --- (4) corrected tangent diagnostic: A - L (positive => tangent FAILS)
# tangent plane from the candidate (grad via central differences of the TRUE A)
b0 = np.array([0.9223829833, 1.1925065472, 1.1925065472])
A0 = D2.inner_max(b0, nx=4001)['A']
h = 1e-6
g = np.zeros(3)
for i in range(3):
    e = np.zeros(3); e[i] = h
    g[i] = (D2.inner_max(b0 + e, nx=4001)['A'] - D2.inner_max(b0 - e, nx=4001)['A']) / (2 * h)
worst = (-1e9, None)
for _ in range(3000):
    u = np.clip(rng.dirichlet(np.ones(3)) * rng.uniform(0.3, 6.2), 1e-4, PI - 1e-4)
    if u.sum() >= 2 * PI - 1e-9:
        continue
    Au = D2.inner_max(u, nx=801)['A']
    excess = Au - (A0 + float(g @ (u - b0)))
    if excess > worst[0]:
        worst = (excess, u)
out['tangent_diagnostic'] = dict(beta0=b0.tolist(), A0=float(A0), grad=g.tolist(),
                                 grad_sum=float(g.sum()),
                                 max_A_minus_L=float(worst[0]),
                                 argmax=worst[1].tolist(),
                                 verdict=('tangent is NOT a global majorant' if worst[0] > 0
                                          else 'no violation found'))
# and the constant majorant, which IS affine and valid
out['constant_majorant'] = dict(value=float(3 * np.sqrt(3) / 2),
                                A_at_b0=float(A0), slack=float(3 * np.sqrt(3) / 2 - A0))

# --- (5) global max with the corrected solver
best = D2.global_search(seed=11, n_restart=120, nx=401)
out['global_max'] = dict(A=float(best[0]), beta=np.asarray(best[1]).tolist(),
                         detail={k: (v if not isinstance(v, np.ndarray) else v.tolist())
                                 for k, v in best[2].items()})

print(json.dumps(out, indent=1, default=float))
with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\corrections_verified.json", 'w') as f:
    json.dump(out, f, indent=1, default=float)
