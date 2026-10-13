from pathlib import Path

p = Path(__file__).with_name('joint_outer_attack.py')
s = p.read_text(encoding='utf-8')

# (1) feasibility gate on the target flag + divergence classification
old = """             'below_target': bool(res.fun < R_STAR - 1e-7),"""
new = """             'below_target_raw': bool(res.fun < R_STAR - 1e-7),
             'below_target': bool(res.fun < R_STAR - 1e-7
                                  and ivals.min() >= -1e-9
                                  and widths_out.min() >= EPS_MIN - 1e-9
                                  and widths_out.max() <= L_CAP + 1e-9),
             'diverged_or_infeasible': bool(ivals.min() < -1e-3
                                            or not (widths_out.min() >= EPS_MIN - 1e-9
                                                    and widths_out.max() <= L_CAP + 1e-9)),"""
assert old in s
s = s.replace(old, new, 1)

# (2) candidate seed: warm-start the sites at the saved centres
old2 = """def seed_x0(w):
    th = angles_from_widths(w)
    U = U_from_angles(th)
    x0 = np.zeros(NTOT)
    x0[:8] = th[1:]
    sites = np.zeros((11, 2))
    for i in range(9):
        mid = (U[i] + U[(i - 1) % 9]) / 2
        nrm = np.linalg.norm(mid)
        sites[i] = mid * (0.97 * min(1.0, 1.0 / max(nrm, 1e-9)))
    centroid = sites[:9].mean(axis=0)
    sites[9] = centroid * 0.5
    sites[10] = centroid * 0.35"""
new2 = """def seed_x0(w, warm_sites=None):
    th = angles_from_widths(w)
    U = U_from_angles(th)
    x0 = np.zeros(NTOT)
    x0[:8] = th[1:]
    if warm_sites is not None:
        sites = np.array(warm_sites, dtype=float).copy()
    else:
        sites = np.zeros((11, 2))
        for i in range(9):
            mid = (U[i] + U[(i - 1) % 9]) / 2
            nrm = np.linalg.norm(mid)
            sites[i] = mid * (0.97 * min(1.0, 1.0 / max(nrm, 1e-9)))
        centroid = sites[:9].mean(axis=0)
        sites[9] = centroid * 0.5
        sites[10] = centroid * 0.35"""
assert old2 in s
s = s.replace(old2, new2, 1)

old3 = """    x0, th = seed_x0(w)"""
new3 = """    x0, th = seed_x0(w, warm_sites=(C0 if name == 'candidate_widths' else None))"""
assert old3 in s
s = s.replace(old3, new3, 1)

old4 = """    log('seed=%-16s V-R*=%.9e nit=%d secs=%.1f min51=%.2e widthsOK=%s target=%s'
        % (name, entry['V_minus_R_star'], entry['nit'], entry['secs'],
           entry['min_51_edge_residual'], entry['widths_legal'], entry['below_target']))"""
new4 = """    log('seed=%-16s V-R*=%.9e nit=%d secs=%.1f min51=%.2e widthsOK=%s target=%s diverged=%s'
        % (name, entry['V_minus_R_star'], entry['nit'], entry['secs'],
           entry['min_51_edge_residual'], entry['widths_legal'], entry['below_target'],
           entry['diverged_or_infeasible']))"""
assert old4 in s
s = s.replace(old4, new4, 1)

old5 = """print(json.dumps({k: v for k, v in res_out.items() if k != 'seeds'}, indent=1))
for e in res_out['seeds']:
    print('%-16s V-R*=%.9e nit=%3d min51=%.2e legal=%s target=%s'
          % (e['seed'], e['V_minus_R_star'], e['nit'], e['min_51_edge_residual'],
             e['widths_legal'], e['below_target']))"""
new5 = """res_out['n_target_hits'] = int(sum(1 for e in res_out['seeds'] if e['below_target']))
res_out['n_diverged'] = int(sum(1 for e in res_out['seeds'] if e['diverged_or_infeasible']))
(OUT / 'joint_outer_attack.json').write_text(json.dumps(res_out, indent=2), encoding='utf-8')
print(json.dumps({k: v for k, v in res_out.items() if k != 'seeds'}, indent=1))
for e in res_out['seeds']:
    print('%-16s V-R*=%.9e nit=%3d min51=%.2e legal=%s target=%s diverged=%s'
          % (e['seed'], e['V_minus_R_star'], e['nit'], e['min_51_edge_residual'],
             e['widths_legal'], e['below_target'], e['diverged_or_infeasible']))"""
assert old5 in s
s = s.replace(old5, new5, 1)
p.write_text(s, encoding='utf-8')
print('patched: feasibility gate, warm start, divergence flags')
