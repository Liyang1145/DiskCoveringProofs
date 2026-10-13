from pathlib import Path

p = Path(__file__).with_name('fixed_oracle_v2.py')
s = p.read_text(encoding='utf-8')

# (1) generic SOC entry, calibrated elsewhere; no optimisation at import time
old = "def main():"
new = '''def propose_from_widths(w, maxiter=400):
    """GENERIC SOC entry (v2 instrument).

    input : w = 9 widths with sum = 2*pi and each <= L_cap = 2*arcsin(0.38)
    output: r, 51 force vectors p in CANONICAL order (18 endpoints then 33 face cones, faces in
            the C911 literal order), proposal work, all-51 residuals, initializer diagnostics.
    Values are numeric proposals for the lead's independent rational repair; NOT certified.
    """
    w = np.asarray(w, dtype=float)
    if abs(float(w.sum()) - 2 * np.pi) > 1e-9 or float(w.max()) > L_CAP + 1e-9 or float(w.min()) < 0:
        raise ValueError('illegal widths (need sum 2*pi, each in [0, L_cap])')
    sol = solve_v2(w, maxiter=maxiter)
    out = {'widths': [float(v) for v in w], 'r': sol['r'], 'r_minus_R_star': sol['r'] - R_STAR,
           'success': sol['success'], 'nit': sol['nit'],
           'min_residual_all51': sol['min_residual_all51'],
           'init_diagnostics': sol['init_diagnostics'],
           'sites': sol['c'].tolist(), 'aux': sol['z'].tolist(),
           'force_order': [[k, int(s_), int(o_)] for (k, s_, o_) in FORCE_ORDER],
           'LABEL': 'numeric SOC force PROPOSAL (v2 instrument); NOT certified'}
    if sol['success'] and sol['min_residual_all51'] > -1e-9:
        pr = propose_forces(sol)
        out.update({'n_active_edges': pr['n_active_edges'], 'n_masked_edges': pr['n_masked_edges'],
                    'alpha_51': pr['alpha_51'], 'p_51': pr['force_vectors_51'],
                    'proposal_work': pr['proposal_work_sum_anchor_load_dot_U'],
                    'proposal_work_minus_r': pr['proposal_work_sum_anchor_load_dot_U'] - sol['r'],
                    'nnls_residual_norm': pr['nnls_residual_norm'],
                    'balance_matrix_vs_scatter_gap': pr['balance_matrix_vs_scatter_gap'],
                    'proposal_norm_sum_euclidean': pr['proposal_norm_sum_euclidean']})
    else:
        out['failed'] = True
    return out


def main():'''
assert old in s
s = s.replace(old, new, 1)

# (2) main: keep corner history, add the two calibrations (candidate / uniform)
old2 = "    (OUT / 'fixed_oracle_v2.json').write_text(json.dumps(out, indent=2), encoding='utf-8')\n    print('written fixed_oracle_v2.json')"
new2 = '''    # calibrations: candidate and uniform, ONE run each (v1 constants and canonical labels)
    cand = switches_from_centres(load_centres())
    th = np.array([np.arctan2(q[1], q[0]) for q in cand])
    wc = np.mod(np.diff(np.concatenate([th, [th[0] + 2 * np.pi]])), 2 * np.pi)
    out['calibrations'] = []
    for nm, w in (('candidate', wc), ('uniform', np.full(9, 2 * np.pi / 9))):
        try:
            e = propose_from_widths(w, maxiter=400)
        except Exception as exc:                              # noqa: BLE001
            e = {'name': nm, 'error': '%s: %s' % (type(exc).__name__, exc), 'failed': True}
        e['name'] = nm
        out['calibrations'].append(e)
        print('calib %-10s r-R*=%.6e success=%s min51=%s work-r=%s'
              % (nm, e.get('r_minus_R_star', float('nan')), e.get('success'),
                 e.get('min_residual_all51'), e.get('proposal_work_minus_r')))
    (OUT / 'fixed_oracle_v2.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
    print('written fixed_oracle_v2.json (corners history kept + calibrations added)')'''
assert old2 in s
s = s.replace(old2, new2, 1)
p.write_text(s, encoding='utf-8')
print('patched: generic propose_from_widths + calibrations in main')
