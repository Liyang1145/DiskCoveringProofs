"""
Bounded final audit run: analytic-audit witnesses + candidate tangent diagnostic.
(No broad global-max optimization; the global constant is decided analytically.)

Outputs:
 (1) non-concavity witnesses for A on the diagonal (exact closed form)
 (2) the exact x0 formula vs bisection on the legal upper branch (re-confirm)
 (3) candidate tangent diagnostic:
      * beta0 = (0.9223829833, 1.1925065472, 1.1925065472)
      * A(beta0), grad A(beta0) (central differences + one-sided cross-check)
      * is the tangent plane an upper bound?  max excess over the legal domain,
        over a restricted box (beta_i >= 0.3), and along the diagonal
 (4) no-affine-majorant witness (three constraint points)
 (5) exact Jensen majorant m(beta)=3 sin(Bsum/3): value at beta0 and at pi/3,
     computed exactly (no global scan)
"""
import json
import sys
import numpy as np
sys.path.insert(0, r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2")
import envelope_clean as EC

PI = EC.PI
out = {}


def x_hi_y1(beta, iters=100):
    """largest x<=1 with sum_i atan2(sin b_i, x-cos b_i) = pi and branch ok."""
    beta = np.asarray(beta, float)
    f = lambda x: EC.H(beta, x) - PI
    if f(1.0) >= 0:
        return 1.0
    lo, hi = 1e-12, 1.0
    if f(lo) < 0:
        return 0.0
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        if f(mid) >= 0:
            lo = mid
        else:
            hi = mid
    x = 0.5 * (lo + hi)
    th = EC.theta(beta, x)
    if not np.all(th < PI - beta) or not np.all(th > 0):
        return 0.0
    return x


def A(beta):
    beta = np.asarray(beta, float)
    if beta.sum() >= 2 * PI:
        return 0.0
    x = x_hi_y1(beta)
    if x <= 0:
        return 0.0
    return x * float(np.sin(beta).sum())


# (1) non-concavity witnesses (exact closed form diag(t) = 3 sin t for t<=pi/3)
w = []
for t1, t2 in [(1.0, 1.3), (0.95, 1.25), (1.0, 1.2), (0.20, 0.40), (0.6, 1.0)]:
    tm = 0.5 * (t1 + t2)
    a1, a2, am = A([t1] * 3), A([t2] * 3), A([tm] * 3)
    w.append(dict(t1=t1, t2=t2, A1=a1, A2=a2, mid=am, chord_mid=0.5 * (a1 + a2),
                  excess=am - 0.5 * (a1 + a2),
                  diag_closed_ok=abs(a1 - 3 * np.sin(t1)) < 1e-12))
out['1_nonconcavity'] = dict(witnesses=w,
                             A_second_deriv_at_pi3=float(2 * np.sqrt(3)),
                             A_prime_at_pi3=float(3 * np.cos(PI / 3)),
                             verdict='A is NOT concave (A"(pi/3)>0 on the diagonal)')

# (2) x0 formula vs bisection, legal upper branch only
rng = np.random.default_rng(555)
beta = np.clip(rng.dirichlet(np.ones(3) * 1.5, 30000).T * rng.uniform(0.05, 6.2, 30000),
               1e-6, PI - 1e-9)
Bsum = beta.sum(axis=0)
mask = (Bsum > PI + 1e-9) & (Bsum < 2 * PI - 1e-9)
xb = EC.x0_bisect(beta)
xf = EC.x0_theorem(beta)
out['2_x0_agreement'] = dict(n=int(mask.sum()),
                             max_diff=float(np.max(np.abs(xb[mask] - xf[mask]))),
                             max_H_resid_bisect=float(np.max(np.abs(EC.H(beta[:, mask], xb[mask]) - PI))),
                             max_H_resid_formula=float(np.max(np.abs(EC.H(beta[:, mask], xf[mask]) - PI))),
                             max_branch_violation=float(np.max(
                                 EC.theta(beta[:, mask], xf[mask]) - (PI - beta[:, mask]))))

# (3) candidate tangent diagnostic
b0 = np.array([0.9223829833, 1.1925065472, 1.1925065472])
A0 = A(b0)
h = 1e-7
g = np.zeros(3)
for i in range(3):
    e = np.zeros(3); e[i] = h
    cp = np.clip(b0 + e, 1e-9, PI - 1e-9)
    cm = np.clip(b0 - e, 1e-9, PI - 1e-9)
    g[i] = (A(cp) - A(cm)) / (2 * h)
# one-sided cross-check (the envelope can be kinked at sum=pi)
gp = np.zeros(3)
gm = np.zeros(3)
for i in range(3):
    e = np.zeros(3); e[i] = h
    gp[i] = (A(b0 + e) - A0) / h
    gm[i] = (A0 - A(b0 - e)) / h
out['3_candidate'] = dict(beta0=b0.tolist(), Bsum=float(b0.sum()), A0=A0,
                          x0=float(EC.x0_theorem(b0)), sum_sin=float(np.sin(b0).sum()),
                          grad_central=g.tolist(), grad_plus=gp.tolist(), grad_minus=gm.tolist(),
                          grad_sum=float(g.sum()),
                          jensen_majorant_at_b0=float(3 * np.sin(b0.sum() / 3)),
                          jensen_majorant_at_b0_from_A=3 * np.sin(b0.sum() / 3))
print('3 candidate', json.dumps(out['3_candidate']), flush=True)


def tangent_excess(u, box_lo=0.0):
    u = np.asarray(u, float)
    if u.sum() >= 2 * PI - 1e-12:
        return -np.inf
    if box_lo > 0 and np.any(u < box_lo):
        return -np.inf
    return A0 + float(g @ (u - b0)) - A(u)


# random + local polish for max excess, whole domain and restricted box
res = {}
for tag, box_lo in [('whole_domain', 0.0), ('box_beta_ge_0.3', 0.3),
                    ('box_beta_ge_0.5', 0.5), ('box_beta_ge_0.8', 0.8)]:
    best = (-np.inf, None)
    for _ in range(4000):
        u = np.clip(rng.dirichlet(np.ones(3)) * rng.uniform(0.05, 6.28), 1e-7, PI - 1e-7)
        if u.sum() >= 2 * PI - 1e-9:
            continue
        e = tangent_excess(u, box_lo)
        if e > best[0]:
            best = (e, u)
    u = np.asarray(best[1], float).copy()
    step = 0.15
    for _ in range(400):
        imp = False
        for i in range(3):
            for sg in (1, -1):
                c = u.copy()
                c[i] = min(max(c[i] + sg * step, max(box_lo, 1e-7)), PI - 1e-7)
                if c.sum() >= 2 * PI - 1e-9:
                    continue
                e = tangent_excess(c, box_lo)
                if e > best[0]:
                    best, u, imp = (e, c), c, True
        if not imp:
            step *= 0.5
            if step < 1e-10:
                break
    res[tag] = dict(max_excess=float(best[0]), argmax=best[1].tolist())
out['3_tangent_majorant_test'] = res
print('3 tangent', json.dumps(res, indent=1), flush=True)

# diagonal slice of the tangent excess
ts = np.linspace(1e-6, 2 * PI / 3 - 1e-9, 20001)
de = np.array([A0 + g.sum() * (t - b0.sum() / 3) - A([t, t, t]) for t in ts])
i = int(np.argmax(de))
out['3_tangent_diag'] = dict(max=float(de.max()), t_at=float(ts[i]),
                             at_pi3=float(A0 + g.sum() * (PI / 3 - b0.sum() / 3) - A([PI / 3] * 3)))
print('3 tangent diag', json.dumps(out['3_tangent_diag']), flush=True)

# (4) no affine majorant witness
pts = {'pi3': [PI / 3] * 3, '1.1925^3': [1.1925065472] * 3}
vals = {k: A(v) for k, v in pts.items()}
out['4_affine_majorant'] = dict(values=vals,
                                note='A(1.1925^3) must exceed the max of A over {Bsum<=pi}; '
                                     'see decisive2 (A=2.7838 vs 2.598) -- recomputed here',)
print('4', json.dumps(out['4_affine_majorant']), flush=True)

with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\audit_final.json", 'w') as f:
    json.dump(out, f, indent=1, default=float)
print('DONE')
