from pathlib import Path

p = Path(__file__).with_name('fixed_oracle_force_proposal.py')
s = p.read_text(encoding='utf-8')

# (1) rename the misnamed key
s = s.replace("'min_edge_residual_all69'", "'min_residual_all51'")

# (2) proposal_work from the PROPOSAL p (keep the primal work separate, no mixing)
old = "    lam = sol['lam_51']\n    primal_p = None\n    work = None"
new = """    # proposal work: anchor loads from the PROPOSAL forces p (not from primal_p)
    load_p = np.zeros((9, 2))
    for k in range(51):
        kind, site, other = FORCE_ORDER[k]
        if kind == 'endpoint':
            load_p[other] -= p[k]
    proposal_work = float(sum(load_p[i] @ U[i] for i in range(9)))
    lam = sol['lam_51']
    primal_p = None
    work = None"""
assert old in s
s = s.replace(old, new, 1)
s = s.replace("""            'work_sum_anchor_load_dot_U': work,""",
              """            'proposal_work_sum_anchor_load_dot_U': proposal_work,
            'primal_work_sum_anchor_load_dot_U': work,""", 1)

# (3) corners mode: 9 simplex vertices, compact output, failures preserved
old2 = "if __name__ == '__main__':"
new2 = """def corners_report(path=None):
    C = load_centres()
    m_small = 2 * np.pi - 8 * L_CAP
    out = {'R_STAR_label': 'C529 rational (NOT C891)', 'R_star': R_STAR, 'L_cap': L_CAP,
           'note': 'fixed-angle oracle at the nine capped-simplex vertices; NUMERIC proposal only, '
                   'NOT certified; failures kept explicitly', 'corners': []}
    for k in range(9):
        w = np.full(9, L_CAP)
        w[k] = m_small
        try:
            e = propose_from_widths(w, maxiter=400)
            rec = {'corner': k, 'widths': [float(v) for v in w], 'r': e['r'],
                   'r_minus_R_star': e['r_minus_R_star'], 'r_gt_0p38': bool(e['r'] > 0.38),
                   'success': e['success'], 'nit': e['nit'],
                   'all51_residual_min': e['min_residual_all51'],
                   'proposal_work': e['proposal_work_sum_anchor_load_dot_U'],
                   'nnls_residual_norm': e['nnls_residual_norm'],
                   'n_active_edges': e['n_active_edges'], 'n_masked_edges': e['n_masked_edges'],
                   'alpha_51': e['alpha_51'], 'p_51': e['force_vectors_51'],
                   'sites': e['sites'], 'aux': e['aux']}
        except Exception as exc:                      # noqa: BLE001
            rec = {'corner': k, 'widths': [float(v) for v in w],
                   'error': '%s: %s' % (type(exc).__name__, exc), 'failed': True}
        out['corners'].append(rec)
        print('corner%d r=%.9f r-R*=%s success=%s all51min=%s work=%s'
              % (k, rec.get('r', float('nan')), rec.get('r_minus_R_star'), rec.get('success'),
                 rec.get('all51_residual_min'), rec.get('proposal_work')))
    tgt = Path(path) if path else (OUT / 'corner_force_proposals.json')
    tgt.write_text(json.dumps(out, indent=2), encoding='utf-8')
    print('written', tgt.name, '| n_gt_0p38 =',
          sum(1 for c in out['corners'] if c.get('r_gt_0p38')), '| n_failed =',
          sum(1 for c in out['corners'] if c.get('failed')))
    return out


if __name__ == '__main__':"""
assert old2 in s
s = s.replace(old2, new2, 1)
s = s.replace("    C = load_centres()\n    sw = switches_from_centres(C)",
              "    import sys\n    if '--corners' in sys.argv:\n        corners_report()\n        raise SystemExit(0)\n"
              "    C = load_centres()\n    sw = switches_from_centres(C)", 1)
p.write_text(s, encoding='utf-8')
print('patched: key rename, proposal_work, --corners mode')
