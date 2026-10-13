"""Bounded verification: sup of A over the domain (vectorized bisection), plus
targeted neighborhood scan around the reported candidate. Small, fast."""
import json
import sys
import numpy as np
sys.path.insert(0, r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2")
import envelope_clean as EC

PI = EC.PI
out = {}


def A_vec(beta):
    """A = x0*sum sin, x0 = largest root; branch-safe (c<0 -> quadratic root,
    c>=0 -> 1).  Vectorized; beta shape (3,N)."""
    beta = np.asarray(beta, float)
    return EC.A_of_beta(beta, 'theorem')[0]


# ---- coarse full-cube scan, sum < 2pi
n = 110
g = np.linspace(1e-6, PI - 1e-6, n)
B1, B2, B3 = np.meshgrid(g, g, g, indexing='ij')
beta = np.vstack([B1.ravel(), B2.ravel(), B3.ravel()])
beta = beta[:, beta.sum(axis=0) < 2 * PI - 1e-9]
vals = A_vec(beta)
i = int(np.argmax(vals))
out['coarse_max'] = dict(A=float(vals[i]), beta=beta[:, i].tolist(),
                         Bsum=float(beta[:, i].sum()), n_points=int(beta.shape[1]))

# ---- refine around the coarse best by local grid
b0 = beta[:, i]
for trial in range(3):
    span = 0.08 * (0.3 ** trial)
    axes = [np.linspace(max(b - span, 1e-6), min(b + span, PI - 1e-6), 21) for b in b0]
    C1, C2, C3 = np.meshgrid(*axes, indexing='ij')
    bb = np.vstack([C1.ravel(), C2.ravel(), C3.ravel()])
    bb = bb[:, bb.sum(axis=0) < 2 * PI - 1e-9]
    vv = A_vec(bb)
    j = int(np.argmax(vv))
    if vv[j] > vals[i]:
        vals_i = vv[j]
        b0 = bb[:, j]
out['refined_max'] = dict(A=float(A_vec(b0.reshape(3, 1))[0]), beta=b0.tolist(),
                          Bsum=float(b0.sum()), x0=float(EC.x0_theorem(b0)))
out['reference_3sqrt3_over_2'] = float(3 * np.sqrt(3) / 2)
out['gap'] = float(3 * np.sqrt(3) / 2 - float(A_vec(b0.reshape(3, 1))[0]))

# ---- targeted scan around the reported candidate beta*
bs = np.array([0.9223829833, 1.1925065472, 1.1925065472])
rad = 0.25
ax = [np.linspace(max(b - rad, 1e-6), min(b + rad, PI - 1e-6), 41) for b in bs]
D1, D2, D3 = np.meshgrid(*ax, indexing='ij')
bb = np.vstack([D1.ravel(), D2.ravel(), D3.ravel()])
bb = bb[:, bb.sum(axis=0) < 2 * PI - 1e-9]
vv = A_vec(bb)
j = int(np.argmax(vv))
out['candidate_neighbourhood'] = dict(A_max=float(vv[j]), beta=bb[:, j].tolist(),
                                      A_at_candidate=float(A_vec(bs.reshape(3, 1))[0]))

# ---- diagonal exact reference
ts = np.linspace(1e-6, 2 * PI / 3 - 1e-9, 200001)
dv = A_vec(np.vstack([ts, ts, ts]))
k = int(np.argmax(dv))
out['diagonal'] = dict(max=float(dv.max()), t_at=float(ts[k]),
                       value_at_pi3=float(A_vec(np.full((3, 1), PI / 3))[0]),
                       formula='3 sin t for t<=pi/3 (x0=1)')

print(json.dumps(out, indent=1))
with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\bounded_scan.json", 'w') as f:
    json.dump(out, f, indent=1)
