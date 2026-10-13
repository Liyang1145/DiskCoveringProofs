"""cline2-coupled-factors f2: exact consistency audit of the closure-dual architecture.

A dual bound of the form
    ub(z) = const.z + sum_f max_i [ vals_{f,i} + M_{f,i} . z ]
is valid only if its coefficient rows are consistent with the exact geometric identities
they adjoint.  Concretely: evaluate const.z + sum_f [vals_f + M_f.z] at a GENUINE
realization.  If the adjoint system is a correct dualization of the area identity
A(realization) = pi, that number must equal pi (the primal objective) exactly, and it can
never be below pi (each factor's max dominates its row value).

This audit is independent of any optimizer: it is a finite-precision check of the
assembly, and it pins down which variable block carries the inconsistency.
"""
import numpy as np, json, math, sys
from pathlib import Path

P = Path(__file__).parent
LEAD = P.parent / 'lead'
R = 19/50
pi = math.pi
sys.path.insert(0, str(P))
from f1_dual_probe import Prob, build, lead_spec, evaluate

pr, facs, sws, rngs = build(0, 4)
row = lead_spec(0, 4)
z7 = np.array(row['z'])
z = np.concatenate([z7, np.zeros(21)])
print('const.z =', float(pr.base @ z))
print('sum over factors of MAX (vals+M.z) =',
      sum(max_j_stub for max_j_stub in
          [max(v + (A @ z)) for (A, v) in facs + sws + rngs]))
print('=> ub(z0) =', float(pr.base @ z) +
      sum(max(v + (A @ z)) for (A, v) in facs + sws + rngs))
print('lead reported sample_upper/lp_value =', row['sample_upper'], row['lp_value'])

# --- Realized-point test: random genuine diagram, evaluate the ROW (not the max) ---
rng = np.random.default_rng(7)
n_acc = 0
worst = 1e18; arg = None
for _ in range(200000):
    al = rng.uniform(0.15, pi-0.15, 9)
    u = rng.uniform(0.05, 1.0, 9); v = rng.uniform(0.05, 1.0, 9)
    q = (u-v)**2 + 4*u*v*np.sin(al/2)**2
    if np.any(q < pr.qmin):
        continue
    w = 2*np.arcsin(np.minimum(1.0, R*np.sqrt(q)/2))
    L = np.arctan2(v*np.sin(al), u-v*np.cos(al))
    T = np.arctan2(u*np.sin(al), v-u*np.cos(al))
    b = (pi - T - np.roll(L, -1) - (w + np.roll(w, -1))/2)/2
    if np.any(b < 0) or np.any(b > pi/2):
        continue
    n_acc += 1
    tot = float(pr.base @ z)
    for i in range(9):
        qq = (u[i]-v[i])**2 + 4*u[i]*v[i]*math.sin(al[i]/2)**2
        ww = 2*math.asin(min(1.0, R*math.sqrt(qq)/2))
        kr = pr.ei[tuple(sorted((i, (i+1) % 9)))]
        kl = pr.ei[tuple(sorted(((i-1) % 9, i)))]
        val = R*R*u[i]*v[i]*math.sin(al[i])/2 + (ww-math.sin(ww))/2
        r = np.zeros(pr.nz)
        r[pr.lin_rad+2*i] = -u[i]; r[pr.lin_rad+2*i+1] = -v[i]
        r[pr.rr+2*i] = -u[i]**2; r[pr.rr+2*i+1] = -v[i]**2
        r[pr.lam] = ww; r[pr.pos+kr] = -u[i]; r[pr.pos+kl] = -v[i]
        tot += val + r @ z
    for bi in range(9):
        bb = b[bi]
        k = pr.ei[tuple(sorted((bi, (bi+1) % 9)))]
        val = R*R*math.sin(2*bb)/2
        r = np.zeros(pr.nz)
        r[bi] = bb; r[(bi+1) % 9] = bb; r[pr.kap+k] = -bb; r[pr.cl+bi] = 2*bb
        r[pr.side+k] = -math.sin(bb)**2; r[pr.lin_side+k] = -math.sin(bb)
        r[pr.pos+k] = -math.sin(bb)
        tot += val + r @ z
    if tot < worst:
        worst = tot; arg = (al.copy(), u.copy(), v.copy(), b.copy())
print(f'accepted realizations: {n_acc}')
print(f'min realized (const + sum rows) = {worst:.9f}   pi = {pi:.9f}   deficit = {worst-pi:+.3e}')
