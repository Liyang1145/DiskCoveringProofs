from pathlib import Path

p = Path(__file__).with_name('fixed_oracle_force_proposal.py')
s = p.read_text(encoding='utf-8')

# (3) residual over ALL constraints
s = s.replace("'min_edge_residual': float(min(cc['fun'](res.x) for cc in cons[18:]))}",
              "'min_edge_residual_all69': float(min(cc['fun'](res.x) for cc in cons))}", 1)

# (1)+(2) rewrite propose_forces: unit-gradient G with signed incidence, slack masking,
#         primal forces p = 2*lambda*d, work = sum anchor load . U
i = s.index('def propose_forces(sol):')
j = s.index('def propose_from_widths(')
new = '''def propose_forces(sol, mask_tol=1e-7):
    """NNLS on the ACTIVE (tight) edges only; G rows use unit(d) with the SIGNED incidence;
    the r-stationarity is enforced by the normalisation row sum(alpha) = 1.
    primal forces use p = 2*lambda*d (squared-constraint convention)."""
    c, z, U = sol['c'], sol['z'], sol['U']
    r = sol['r']
    res51 = sol['edge_residuals']
    active = [k for k in range(51) if res51[k] <= mask_tol]
    G = np.zeros((45, 51))
    for k in active:
        kind, site, other = FORCE_ORDER[k]
        g = np.zeros(45)
        d = (c[site] - U[other]) if kind == 'endpoint' else (c[site] - z[other])
        u = unit(d)
        g[2 * site:2 * site + 2] += u
        if kind == 'face':
            g[22 + 2 * other:24 + 2 * other] -= u
        g[44] = 1.0
        G[:, k] = g
    b = np.zeros(45)
    b[44] = 1.0
    alpha = np.zeros(51)
    if active:
        a_act, resid = nnls(G[:, active], b, maxiter=5000)
        for pos, k in enumerate(active):
            alpha[k] = a_act[pos]
        nnls_resid = float(np.linalg.norm(G[:, active] @ a_act - b))
    else:
        nnls_resid = float(np.linalg.norm(b))
    p = np.zeros((51, 2))
    for k in range(51):
        kind, site, other = FORCE_ORDER[k]
        d = (c[site] - U[other]) if kind == 'endpoint' else (c[site] - z[other])
        p[k] = alpha[k] * unit(d)
    bal = np.zeros((22, 2))
    for k in range(51):
        kind, site, other = FORCE_ORDER[k]
        if kind == 'endpoint':
            bal[site] += p[k]
        else:
            bal[site] += p[k]
            bal[11 + other] -= p[k]
    # matrix-side balance (from G, unit rows) must equal the direct scatter
    mat_bal = np.zeros(45)
    for k in active:
        mat_bal += alpha[k] * G[:, k]
    mat_max = float(np.max(np.abs(mat_bal[:44])))
    lam = sol['lam_51']
    primal_p = None
    work = None
    if lam is not None:
        primal_p = np.zeros((51, 2))
        for k in range(51):
            kind, site, other = FORCE_ORDER[k]
            d = (c[site] - U[other]) if kind == 'endpoint' else (c[site] - z[other])
            primal_p[k] = 2 * lam[k] * d                    # squared-constraint convention
        # anchor load: only endpoint edges carry into the anchors (F = -p at that anchor)
        load = np.zeros((9, 2))
        for k in range(51):
            kind, site, other = FORCE_ORDER[k]
            if kind == 'endpoint':
                load[other] -= primal_p[k]
        work = float(sum(load[i] @ U[i] for i in range(9)))
    return {'n_active_edges': len(active), 'n_masked_edges': 51 - len(active),
            'alpha_51': alpha.tolist(),
            'force_vectors_51': p.tolist(),
            'proposal_norm_sum_euclidean': float(np.sum(np.linalg.norm(p, axis=1))),
            'nnls_residual_norm': nnls_resid,
            'sum_alpha': float(alpha.sum()),
            'matrix_balance_max_abs_44': mat_max,
            'direct_free_balance_max_abs': float(np.max(np.abs(bal))),
            'balance_matrix_vs_scatter_gap': float(np.max(np.abs(mat_bal[:44]
                                                                   - bal.reshape(-1)[:44]))),
            'n_alpha_gt_1e-10': int(np.sum(alpha > 1e-10)),
            'primal_force_norm_sum_euclidean':
                (None if primal_p is None else float(np.sum(np.linalg.norm(primal_p, axis=1)))),
            'work_sum_anchor_load_dot_U': work,
            'primal_r': r, 'work_minus_primal_r': (None if work is None else work - r)}


'''
s = s[:i] + new + s[j:]

# record edge residuals in the solution
s = s.replace("""    return {'U': U, 'c': c, 'z': z, 'r': float(r), 'success': bool(res.success),""",
              """    eds = np.array([cc['fun'](res.x) for cc in cons[18:]])
    return {'U': U, 'c': c, 'z': z, 'r': float(r), 'success': bool(res.success),
            'edge_residuals': eds,""", 1)
p.write_text(s, encoding='utf-8')
print('patched: unit-G with masking, p=2(lambda)d, work, residuals over all constraints')
