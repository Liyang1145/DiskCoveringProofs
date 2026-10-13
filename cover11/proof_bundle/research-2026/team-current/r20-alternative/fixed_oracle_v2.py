"""fixed_oracle_v2.py  (r20-alternative; sole write, no child)

Separate instrument fixing the shared-initialiser bug of the v1 oracle (do NOT touch the history
of fixed_oracle_force_proposal.py).  Changes:
  * aux z init = simple 3-site CENTROID (the oracle does not require circumcentres);
  * r seed = max edge length + 0.01 (bounds kept loose: [0.05, 1.0], no 0.6 cap);
  * centre init = convex combinations of the U's (finite, <= 2);
  * constraints in the CONVEX SOC form  r - norm(d) >= 0  (jac: dr = 1, dx = -d/norm(d));
  * initial-coordinate diagnostics (max |coord|, max norm) reported.
Only the two divergent corners (3 and 8) are solved here; the other corners' exported p are
unchanged.  Numeric only; nothing certified.
"""
import json
import numpy as np
from pathlib import Path
from scipy.optimize import minimize

from fixed_oracle_force_proposal import (FACES, FORCE_ORDER, R_STAR, L_CAP, load_centres,
                                         switches_from_centres, angles_from_widths, unit,
                                         propose_forces)

OUT = Path(__file__).resolve().parent


def solve_v2(w, maxiter=400):
    th = angles_from_widths(w)
    U = np.stack([np.cos(th), np.sin(th)], axis=1)
    NV = 45

    def unpack(x):
        return x[:22].reshape(11, 2), x[22:44].reshape(11, 2), x[44]
    cons = []

    def mk(site_idx, target, aux_idx=None):
        """SOC form  r - |c_site - target| >= 0 ; aux target is z[aux_idx]"""
        def f(x):
            c, z, r = unpack(x)
            t = z[aux_idx] if aux_idx is not None else target
            return r - float(np.linalg.norm(c[site_idx] - t))

        def jac(x):
            c, z, r = unpack(x)
            t = z[aux_idx] if aux_idx is not None else target
            d = c[site_idx] - t
            n = np.linalg.norm(d)
            g = np.zeros(NV)
            g[44] = 1.0
            if n > 1e-14:
                u = d / n
                g[2 * site_idx:2 * site_idx + 2] = -u
                if aux_idx is not None:
                    g[22 + 2 * aux_idx:24 + 2 * aux_idx] = u
            return g
        return {'type': 'ineq', 'fun': f, 'jac': jac}
    for i in range(9):
        cons.append(mk(i, U[i]))
        cons.append(mk(i, U[(i - 1) % 9]))
    for fi, face in enumerate(FACES):
        for s in face:
            cons.append(mk(s, None, aux_idx=fi))
    # ---- initialisation: centroids of U (finite, <= 2), aux = 3-site centroid, r seed loose ----
    sites = np.zeros((11, 2))
    for i in range(9):
        sites[i] = 0.5 * (U[i] + U[(i - 1) % 9])
    sites[9] = U[:9].mean(axis=0) * 0.5
    sites[10] = U[:9].mean(axis=0) * 0.35
    zz = np.zeros((11, 2))
    for fi, face in enumerate(FACES):
        zz[fi] = sites[face].mean(axis=0)
    seed_edges = [np.linalg.norm(sites[i] - U[i]) for i in range(9)]
    seed_edges += [np.linalg.norm(sites[i] - U[(i - 1) % 9]) for i in range(9)]
    seed_edges += [np.linalg.norm(sites[s] - zz[fi]) for (k, s, fi) in
                   [(k, s, o) for (k, s, o) in FORCE_ORDER if k == 'face']]
    r0 = float(max(seed_edges)) + 0.01
    x0 = np.zeros(NV)
    x0[:22] = sites.reshape(-1)
    x0[22:44] = zz.reshape(-1)
    x0[44] = r0
    diag = {'init_max_abs_coord': float(np.max(np.abs(x0[:44]))),
            'init_max_norm_site_or_aux': float(max(np.max(np.linalg.norm(sites, axis=1)),
                                                   np.max(np.linalg.norm(zz, axis=1)))),
            'init_r_seed': r0}
    res = minimize(lambda x: x[44], x0, jac=lambda x: np.r_[np.zeros(44), 1.0], method='SLSQP',
                   bounds=[(None, None)] * 44 + [(0.05, 1.0)], constraints=cons,
                   options={'maxiter': maxiter, 'ftol': 1e-13})
    c, z, r = unpack(res.x)
    vals = np.array([cc['fun'](res.x) for cc in cons])       # all 51 edges (r - norm form)
    mv = getattr(res, 'multipliers', None)
    lam = np.atleast_1d(mv)[-len(cons):] if mv is not None else None
    return {'U': U, 'c': c, 'z': z, 'r': float(r), 'success': bool(res.success),
            'nit': int(res.nit), 'edge_residuals': vals,
            'lam_51': (None if lam is None else np.array(lam[-51:], dtype=float)),
            'init_diagnostics': diag,
            'min_residual_all51': float(vals.min())}


def propose_from_widths(w, maxiter=400):
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


def main():
    from fixed_oracle_force_proposal import L_CAP as LC
    m_small = 2 * np.pi - 8 * LC
    out = {'R_STAR_label': 'C529 rational (NOT C891)', 'R_star': R_STAR, 'L_cap': LC,
           'note': 'v2 instrument (centroid aux init, SOC constraint r-|d|>=0, loose r seed); '
                   'ONLY corners 3 and 8; numeric, nothing certified',
           'corners': []}
    for k in (3, 8):
        w = np.full(9, LC)
        w[k] = m_small
        sol = solve_v2(w, maxiter=400)
        entry = {'corner': k, 'widths': [float(v) for v in w], 'r': sol['r'],
                 'r_minus_R_star': sol['r'] - R_STAR, 'success': sol['success'],
                 'nit': sol['nit'], 'min_residual_all51': sol['min_residual_all51'],
                 'init_diagnostics': sol['init_diagnostics'],
                 'sites': sol['c'].tolist(), 'aux': sol['z'].tolist()}
        if sol['success'] and sol['min_residual_all51'] > -1e-9:
            pr = propose_forces(sol)
            entry.update({'n_active_edges': pr['n_active_edges'],
                          'n_masked_edges': pr['n_masked_edges'],
                          'proposal_work': pr['proposal_work_sum_anchor_load_dot_U'],
                          'nnls_residual_norm': pr['nnls_residual_norm'],
                          'alpha_51': pr['alpha_51'], 'p_51': pr['force_vectors_51'],
                          'proposal_work_minus_r': pr['proposal_work_sum_anchor_load_dot_U'] - sol['r']})
        else:
            entry['failed'] = True
        out['corners'].append(entry)
        print('corner%d r=%.9f r-R*=%.6e success=%s nit=%d min51=%.2e init_r=%.4f maxcoord=%.3f'
              % (k, entry['r'], entry['r_minus_R_star'], entry['success'], entry['nit'],
                 entry['min_residual_all51'], sol['init_diagnostics']['init_r_seed'],
                 sol['init_diagnostics']['init_max_abs_coord']))
        if 'proposal_work' in entry:
            print('        work=%.9f (work-r=%.2e) active=%d masked=%d nnls=%.2e'
                  % (entry['proposal_work'], entry['proposal_work_minus_r'],
                     entry['n_active_edges'], entry['n_masked_edges'],
                     entry['nnls_residual_norm']))
    # calibrations: candidate and uniform, ONE run each (v1 constants and canonical labels)
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
    print('written fixed_oracle_v2.json (corners history kept + calibrations added)')


if __name__ == '__main__':
    main()
