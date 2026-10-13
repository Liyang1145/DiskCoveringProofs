"""Independent numerical verification of the finite-stress final combination (C919/C920).

Read-only: exec's the prefix of lead/interval_network_envelope.py (stops before its JSON write),
so no lead file is touched.  Each check re-derives one step of
ADAPTIVE-STRESS-FINITE-REMAINDER / ANISOTROPIC-STRESS-REMAINDER / RELATIVE-STRESS-BASIS.
Results -> r20-stress/out/finite_stress_check.json
"""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp
W = Path(__file__).parent; LEAD = W.parent / 'lead'; OUT = W / 'out'
ns = {'__file__': str(LEAD / 'interval_network_envelope.py')}
exec((LEAD / 'interval_network_envelope.py').read_text(encoding='utf-8').split("out={'quantitative_local_patch'")[0], ns)
alpha, N, G, edges, X, U, Lam, H = [ns[k] for k in ['alpha', 'N', 'G', 'edges', 'X', 'U', 'Lam', 'H']]
Bmat, lo, hi, mid = ns['B'], ns['lo'], ns['hi'], ns['mid']

def midM(M):
    return np.array([[float(mid(M[i, j])) for j in range(M.cols)] for i in range(M.rows)])
AL = midM(alpha)[:, 0]                 # (45,)
Nf = midM(N)                           # (45,4)
Gf = midM(G)                           # (9,4)
G8 = Gf[:8]                            # (8,4) raw8 chart
L0 = midM(Lam)                         # (9,9)
Hf = midM(H)                           # (9,9)
Xf = [(float(mid(x)), float(mid(y))) for (x, y) in X]
Uf = [(float(mid(x)), float(mid(y))) for (x, y) in U]
Rstar = float(mid(ns['u'][6]))
Bf = midM(Bmat)                        # (41,45)
out = {'scope': 'independent re-derivation/check of the finite-stress combination; numeric, shares lead model interface',
       'Rstar': Rstar, 'n_edges': len(edges), 'N_shape': list(Nf.shape), 'G_shape': list(Gf.shape)}

# C1 equilibrium / normalisation / positivity  (rows 0..39 = free-node equilibrium, row 40 = all ones)
out['C1'] = dict(max_abs_Balpha_free_rows=float(np.abs((Bf @ AL)[:40]).max()),
                 normalized_row_value=float((Bf @ AL)[40]), sum_alpha=float(AL.sum()),
                 alpha_min_lo=float(min(lo(alpha[j]) for j in range(45))),
                 alpha_max_hi=float(max(hi(alpha[j]) for j in range(45))))

# C2 carrying lengths and energy
lens = np.array([math.hypot(Xf[v][0] - Xf[w][0], Xf[v][1] - Xf[w][1]) for (v, w) in edges])
out['C2'] = dict(min_len=float(lens.min()), max_len=float(lens.max()),
                 max_dev_from_Rstar=float(np.abs(lens - Rstar).max()),
                 energy=float((AL * lens ** 2).sum()), Rstar2=Rstar ** 2)

# C3 anchor loads: all nine, radial positive, tangential residual
load = np.zeros((9, 2))
for e, (v, w) in enumerate(edges):
    d = np.array([Xf[v][0] - Xf[w][0], Xf[v][1] - Xf[w][1]])
    for node, sgn in [(v, 1), (w, -1)]:
        if node < 9:
            load[node] += sgn * AL[e] * d
rad = np.array([load[j] @ np.array(Uf[j]) for j in range(9)])
tang = np.array([load[j] @ np.array([-Uf[j][1], Uf[j][0]]) for j in range(9)])
resid = np.array([np.abs(load[j] - rad[j] * np.array(Uf[j])).max() for j in range(9)])
# interval version: does the tangential load interval contain 0, given the alpha intervals?
iv = mp.iv
load_iv = [[iv.mpf(0), iv.mpf(0)] for _ in range(9)]
for e, (v, w) in enumerate(edges):
    d = (X[v][0] - X[w][0], X[v][1] - X[w][1])
    for node, sgn in [(v, 1), (w, -1)]:
        if node < 9:
            load_iv[node][0] += sgn * alpha[e] * d[0]
            load_iv[node][1] += sgn * alpha[e] * d[1]
tang_iv = [load_iv[j][0] * (-U[j][1]) + load_iv[j][1] * U[j][0] for j in range(9)]
rad_iv = [load_iv[j][0] * U[j][0] + load_iv[j][1] * U[j][1] for j in range(9)]
out['C3'] = dict(radial_a=rad.tolist(), tangential=tang.tolist(), max_abs_tangential=float(np.abs(tang).max()),
                 min_radial=float(rad.min()), max_radial_residual=float(resid.max()),
                 tang_interval_contains_zero=[bool(lo(t) <= 0 <= hi(t)) for t in tang_iv],
                 tang_interval_width_max=float(max(hi(t) - lo(t) for t in tang_iv)),
                 radial_interval_lo_min=float(min(lo(r) for r in rad_iv)))

# C4/C5 identities and Taylor bounds
rng = np.random.default_rng(11); tau = 1468.0
Amat = np.zeros((18, 4))
for j in range(4):
    for e, (v, w) in enumerate(edges):
        d = np.array([Xf[v][0] - Xf[w][0], Xf[v][1] - Xf[w][1]])
        for node, sgn in [(v, 1), (w, -1)]:
            if node < 9:
                Amat[2 * node:2 * node + 2, j] += sgn * Nf[e, j] * d
def Mx_and_Qx(x):
    Qx = tau * Nf @ (G8.T @ x)
    Mx = np.zeros(18)
    for e, (v, w) in enumerate(edges):
        d = np.array([Xf[v][0] - Xf[w][0], Xf[v][1] - Xf[w][1]])
        for node, sgn in [(v, 1), (w, -1)]:
            if node < 9:
                Mx[2 * node:2 * node + 2] += sgn * Qx[e] * d
    return Mx, Qx
id_err, ratio, tb = [], [], []
for _ in range(300):
    x = rng.normal(size=8); x *= rng.uniform(1e-4, 1e-2) / np.linalg.norm(x)
    q = np.linalg.norm(x); Mx, Qx = Mx_and_Qx(x)
    v8 = np.array([[x[j] * -Uf[j][1], x[j] * Uf[j][0]] for j in range(8)]).reshape(16)
    p = np.linalg.norm(G8.T @ x)
    id_err.append(abs(2 * (Mx[:16] @ v8) - tau * p ** 2))
    ratio.append(np.linalg.norm(Mx) / (tau * np.linalg.norm(Amat) * p))
    delta = np.array([complex(math.cos(xi), math.sin(xi)) - 1 for xi in x])
    vv = np.array([complex(0, xi) for xi in x])
    ww = delta - vv
    tb.append((np.linalg.norm(delta) / q, np.linalg.norm(vv) / q, np.linalg.norm(ww) / q ** 2))
tb = np.array(tb)
out['C4'] = dict(max_abs_identity_error=float(max(id_err)), max_normMx_over_tauAnormp=float(max(ratio)))
out['C5'] = dict(max_delta_over_q=float(tb[:, 0].max()), max_v_over_q=float(tb[:, 1].max()),
                 max_w_over_q2=float(tb[:, 2].max()), Anorm_F=float(np.linalg.norm(Amat)))

# C6 alpha-dependent minimised-energy comparison
def harmonic_form(weights):
    n = 29; L = np.zeros((n, n))
    for e, (v, w) in enumerate(edges):
        a = weights[e]; L[v, v] += a; L[w, w] += a; L[v, w] -= a; L[w, v] -= a
    Lff, Lfa, Laa = L[9:, 9:], L[9:, :9], L[:9, :9]
    Y = np.linalg.solve(Lff, Lfa)
    return Laa - Lfa.T @ Y, L
Bc = float(np.max(np.linalg.norm(Nf, axis=1) / AL))
G8F = float(np.linalg.norm(G8))
cert = json.loads((LEAD / 'relative_stress_ball_certificate.json').read_text())
Rb = np.array([[float.fromhex(h) for h in row] for row in cert['constants']['basis_R_floathex']])
# two registered charts: C919 (identity basis, tau=1/10, ball 191/25000) and C920 (dyadic basis, tau=1468, ball 729/50000)
charts = [('identity_C919', np.eye(4), 0.1, 191 / 25000), ('dyadic_C920', Rb, 1468.0, 729 / 50000)]
rowsC6 = []
for cname, Rbas, tau_c, ball in charts:
    Gc = G8 @ Rbas
    Bc_chart = float(np.max(np.linalg.norm(Nf @ Rbas, axis=1) / AL))   # chart-independent? no: N'=NR
    for _ in range(60):
        x = rng.normal(size=8); x *= ball * rng.uniform(0.2, 1.0) / np.linalg.norm(x)
        Qx = tau_c * (Nf @ Rbas) @ ((G8 @ Rbas).T @ x); beta0 = float(np.max(np.abs(Qx) / AL))
        p = float(np.linalg.norm(Gc.T @ x))
        if beta0 >= 1.0:
            rowsC6.append(dict(chart=cname, beta0=beta0, skipped=True)); continue
        Lam_x, _ = harmonic_form(AL + Qx)
        z = rng.normal(size=9)
        low, val, up = (1 - beta0) * (z @ L0 @ z), z @ Lam_x @ z, (1 + beta0) * (z @ L0 @ z)
        rowsC6.append(dict(chart=cname, beta0=beta0, tauBp=tau_c * Bc_chart * p, Bc=Bc_chart,
                           ok=bool(low - 1e-12 <= val <= up + 1e-12)))
tested = [r for r in rowsC6 if not r.get('skipped')]
out['C6'] = dict(B_identity=max(np.linalg.norm(Nf, axis=1) / AL).tolist() if False else float(np.max(np.linalg.norm(Nf, axis=1) / AL)),
                 G8_fro=G8F,
                 n_tested=len(tested), n_skipped_beta_ge_1=len(rowsC6) - len(tested),
                 n_ok=int(sum(r['ok'] for r in tested)),
                 by_chart={c: dict(n=sum(1 for r in tested if r['chart'] == c),
                                   ok=sum(1 for r in tested if r['chart'] == c and r['ok']),
                                   B_chart=([r['Bc'] for r in tested if r['chart'] == c] or [None])[0],
                                   max_beta0=max([r['beta0'] for r in tested if r['chart'] == c], default=None),
                                   max_beta0_over_tauBp=max([r['beta0'] / max(r['tauBp'], 1e-300)
                                                             for r in tested if r['chart'] == c], default=None))
                           for c, _, _, _ in charts})

# C7 mixed-cubic identity and bounds  (displacement in the rotated basis (U_i, JU_i))
Cross = np.array([[L0[i, j] * (Uf[i][0] * Uf[j][1] - Uf[i][1] * Uf[j][0]) for j in range(9)] for i in range(9)])
L8 = L0[:8, :8]; K8 = np.kron(L8, np.eye(2)); C8 = Cross[:8, :8]
def anch(xj, Uj, kind):
    ux, uy = Uj; dx, dy = -uy, ux
    if kind == 'delta':
        c, s = math.cos(xj) - 1, math.sin(xj)
    elif kind == 'v':
        c, s = 0.0, xj
    elif kind == 'w':
        c, s = math.cos(xj) - 1, math.sin(xj) - xj
    else:  # R = delta - v + x^2 U/2
        c, s = math.cos(xj) - 1 + xj ** 2 / 2, math.sin(xj) - xj
    return [ux * c + dx * s, uy * c + dy * s]
c7 = []
for _ in range(100):
    x = rng.normal(size=8); x *= 1e-3 / np.linalg.norm(x); q = np.linalg.norm(x)
    v8 = np.array([anch(x[j], Uf[j], 'v') for j in range(8)]).reshape(16)
    w8 = np.array([anch(x[j], Uf[j], 'w') for j in range(8)]).reshape(16)
    R8 = np.array([anch(x[j], Uf[j], 'R') for j in range(8)]).reshape(16)
    lhs = 2 * v8 @ K8 @ w8
    cubic = -x @ C8 @ (x ** 2)
    rem = 2 * v8 @ K8 @ R8
    c7.append(dict(q=q, identity_err=float(abs(lhs - (cubic + rem))),
                   cubic_over_bound=float(abs(cubic) / (float(np.linalg.norm(C8)) * q ** 3)),
                   rem_over_q4=float(abs(rem) / q ** 4),
                   w_over_q2=float(np.linalg.norm(w8) / q ** 2)))
out['C7'] = dict(Cross_F=float(np.linalg.norm(C8)), max_identity_err=float(max(c['identity_err'] for c in c7)),
                 max_cubic_over_bound=float(max(c['cubic_over_bound'] for c in c7)),
                 max_rem_over_q4=float(max(c['rem_over_q4'] for c in c7)),
                 max_w_over_q2=float(max(c['w_over_q2'] for c in c7)))

# C8 Hessian hypothesis and basis dependence (two registered charts + degenerate controls)
tau0, mu0 = 734.0, 0.0018          # C920 chart
def hmin(Rbasis, t0):
    Gp = G8 @ Rbasis
    M = Hf[:8, :8] + 2 * t0 * Gp @ Gp.T
    return float(np.linalg.eigvalsh((M + M.T) / 2).min())
out['C8'] = dict(C920_emitted_R_eigmin=hmin(Rb, 734.0), C920_mu0=mu0,
                 C920_emitted_R_passes=bool(hmin(Rb, 734.0) >= mu0),
                 C919_identity_R_eigmin=hmin(np.eye(4), 0.05), C919_mu0=0.0022,
                 C919_identity_R_passes=bool(hmin(np.eye(4), 0.05) >= 0.0022),
                 degenerate_zero_R_eigmin_C920=hmin(np.zeros((4, 4)), 734.0),
                 scale_only_R_eigmin_C920=hmin(0.0045 * np.eye(4), 734.0))

# C9 final arithmetic with certified constants
def frac(s):
    s = s.strip()
    if s.startswith('('):
        a, b = s[1:-1].split(','); return int(a) / int(b)
    if '/' in s:
        a, b = s.split('/'); return int(a) / int(b)
    return float(s)
cc = cert['constants']
BB, AA, CC = frac(cc['B']), frac(cc['A']), frac(cc['Ccross'])
GG, dd, rho = frac(cc['G']), frac(cc['d']), frac(cc['rho'])
tau_c, tau0_c, mu_c = frac(cc['tau']), frac(cc['tau0']), frac(cc['mu'])
quartic = dd / 3 + tau_c ** 2 * (BB * dd + AA) ** 2 / (4 * (tau_c - tau0_c))
coef = mu_c / 2 - CC * rho - quartic * rho ** 2
out['C9'] = dict(tau=tau_c, tau0=tau0_c, tau_eq_2tau0=bool(abs(tau_c - 2 * tau0_c) < 1e-12),
                 quartic=quartic, coefficient=coef, positivity_product=tau_c * BB * GG * rho,
                 coef_gt_1em5=bool(coef > 1e-5), pos_lt1=bool(tau_c * BB * GG * rho < 1))

# C10 identification H0 = 2[J_U^T (Lam0 (x) I2) J_U - diag(a)]  (needs radial flux)
c10 = []
for _ in range(100):
    x = rng.normal(size=8)
    v8 = np.array([[x[j] * -Uf[j][1], x[j] * Uf[j][0]] for j in range(8)]).reshape(16)
    L8f = np.kron(L0[:8, :8], np.eye(2))
    lhs = 0.5 * x @ Hf[:8, :8] @ x
    rhs = v8 @ L8f @ v8 - float(np.sum(rad[:8] * x ** 2))
    c10.append(abs(lhs - rhs) / max(abs(rhs), 1e-30))
out['C10'] = dict(max_rel_err_H0_identification=float(max(c10)))
# C10b the underlying entrywise identity sum_j Lam0[i,j]<U_i,U_j> = a_i  (needed for H0 = certified H)
resid_a = [abs(sum(L0[i, j] * float(np.dot(Uf[i], Uf[j])) for j in range(9)) - rad[i]) for i in range(9)]
out['C10b'] = dict(max_abs_residual=float(max(resid_a)), a_scale=float(np.mean(np.abs(rad))),
                   rel=float(max(resid_a) / np.mean(np.abs(rad))))
(OUT / 'finite_stress_check.json').write_text(json.dumps(out, indent=2, default=str))
for k in ['C1', 'C2', 'C3', 'C4', 'C5', 'C6', 'C7', 'C8', 'C9', 'C10']:
    print(k, json.dumps(out[k], default=str))
