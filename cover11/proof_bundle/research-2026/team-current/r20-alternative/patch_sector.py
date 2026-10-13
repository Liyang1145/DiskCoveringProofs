from pathlib import Path

p = Path(__file__).with_name('socp_sector_pilot.py')
s = p.read_text(encoding='utf-8')

old1 = """    entry = {'h': h, 'success': bool(res.success), 'nit': int(res.nit),
             'V': float(res.fun), 'V_minus_R_star': float(res.fun) - R_STAR,
             'min_ineq_residual_51edges': float(ineq_vals[16:].min()),
             'sector_margins_min': float(ineq_vals[:8].min()),"""
new1 = """    off = 16 if h > 0 else 0                     # sector constraints exist only for h > 0
    entry = {'h': h, 'success': bool(res.success), 'nit': int(res.nit),
             'V': float(res.fun), 'V_minus_R_star': float(res.fun) - R_STAR,
             'min_ineq_residual_51edges': float(ineq_vals[off:].min()),
             'n_edges_checked': int(len(ineq_vals[off:])),
             'disk_margins_min': float(min(ineq_vals[0:16:2])) if h > 0 else None,
             'chord_margins_min': float(min(ineq_vals[1:16:2])) if h > 0 else None,"""
assert old1 in s
s = s.replace(old1, new1, 1)

old2 = """    mv = getattr(res, 'multipliers', None)
    if mv is not None:
        mv = np.atleast_1d(mv)
        lam = mv[-len(cons):] if mv.size >= len(cons) else None
        if lam is not None:
            alpha = 2 * float(r) * np.array([abs(v) for v in lam])
            entry['sum_abs_norm_multipliers'] = float(np.sum(alpha))
            entry['n_multipliers_gt_1e-10'] = int(np.sum(np.abs(lam) > 1e-10))"""
new2 = """    mv = getattr(res, 'multipliers', None)
    if mv is not None:
        mv = np.atleast_1d(mv)
        lam_all = mv[-len(cons):] if mv.size >= len(cons) else None
        if lam_all is not None:
            edge_lam = np.array([abs(v) for v in lam_all[-51:]])       # 51 EDGE multipliers only
            entry['sum_abs_edge_lambda'] = float(np.sum(edge_lam))
            entry['n_edge_lambda_gt_1e-10'] = int(np.sum(edge_lam > 1e-10))
            # forces p_e = 2 lambda_e (C - U) resp. 2 lambda_e (C - Z), and the direct free balances
            p = []
            for k in range(18):
                i, anc = k // 2, (k // 2 if k % 2 == 0 else (k // 2 - 1) % 9)
                p.append(2 * lam_all[-51 + k] * (c[i] - U[anc]))
            for k in range(33):
                fi = 5 + k // 3 if k // 3 >= 5 else k // 3
                fi = [f for f in range(11)][k // 3]
                s_ = FACES[fi][k % 3]
                p.append(2 * lam_all[-51 + 18 + k] * (c[s_] - z[fi]))
            p = np.array(p)
            bal = np.zeros((22, 2))
            for k in range(18):
                i, anc = k // 2, (k // 2 if k % 2 == 0 else (k // 2 - 1) % 9)
                bal[i] += p[k]
            for k in range(33):
                fi = k // 3
                s_ = FACES[fi][k % 3]
                bal[s_] += p[18 + k]
                bal[11 + fi] -= p[18 + k]
            entry['direct_free_balance_max_abs'] = float(np.max(np.abs(bal)))
            entry['sum_abs_p'] = float(np.sum(np.abs(p)))
            exports[h] = {'U': U.tolist(), 'C': c.tolist(), 'Z': z.tolist(),
                          'edge_lambda_51': [float(v) for v in lam_all[-51:]],
                          'p_51': p.tolist(),
                          'free_node_balances': bal.tolist(),
                          'sum_abs_edge_lambda': float(np.sum(edge_lam)),
                          'direct_free_balance_max_abs': float(np.max(np.abs(bal))),
                          'sum_abs_p': float(np.sum(np.abs(p)))}"""
assert old2 in s
s = s.replace(old2, new2, 1)

s = s.replace("out = {'scope': 'numeric joint-sector pilot (no certificate, no B&B, no scaling)',",
              "out = {'scope': 'numeric joint-sector pilot (no certificate, no B&B, no scaling)',\n"
              "       'R_STAR_label': 'C529 rational value (NOT C891)',\n"
              "       'r_star_value': R_STAR,", 1)
s = s.replace("exports = {}", "")
s = s.replace("def build(h):", "exports = {}\n\n\ndef build(h):", 1)
s = s.replace("(OUT / 'socp_sector_pilot.json').write_text(json.dumps(out, indent=2), encoding='utf-8')",
              "(OUT / 'socp_sector_pilot.json').write_text(json.dumps(out, indent=2), encoding='utf-8')\n"
              "(OUT / 'socp_sector_export.json').write_text(\n"
              "    json.dumps({'R_STAR_label': 'C529 rational (NOT C891)', 'R_star': R_STAR,\n"
              "                'note': 'edge lambda are the 51 distance-edge multipliers only (sector '\n"
              "                        'multipliers excluded); p_e = 2 lambda_e (C-U / C-Z); free-node '\n"
              "                        'balances are DIRECT sums of p', 'runs': exports}, indent=2),\n"
              "    encoding='utf-8')", 1)
s = s.replace("* unit disk:            |U_i| = 1                       (8 equalities)",
              "* unit disk (CONVEX):   1 - |U_i|^2 >= 0                (8 inequalities; early drafts had"
              " the non-convex circle |U_i| = 1)", 1)
p.write_text(s, encoding='utf-8')
print('patched: offsets, edge-lambda-only dual, p-vectors, export, labels')
