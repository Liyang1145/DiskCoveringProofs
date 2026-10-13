from pathlib import Path

p = Path(__file__).with_name('joint_outer_attack.py')
s = p.read_text(encoding='utf-8')

# (1) SIGN FIX: df/dtheta = +2(c-U).U' = 2(-d_x sin t + d_y cos t)
old = """                th_a = x[anchor - 1]
                g[anchor - 1] = 2 * float(d[0] * np.sin(th_a) - d[1] * np.cos(th_a))"""
new = """                th_a = x[anchor - 1]
                # f = r^2 - |c - U|^2 ;  df/dtheta = -2 d . U'(theta) = 2(-d_x sin t + d_y cos t)
                g[anchor - 1] = 2 * float(-d[0] * np.sin(th_a) + d[1] * np.cos(th_a))"""
assert old in s, 'theta jac line not found'
s = s.replace(old, new, 1)

# (2) candidate warm start: ROTATE C0 by -phi_0 so that site angles match the anchor angles
old2 = """    x0, th = seed_x0(w, warm_sites=(C0 if name == 'candidate_widths' else None))"""
new2 = """    if name == 'candidate_widths':
        # rotate the saved centres by -phi_0 (phi_0 = angle of the candidate's first switch)
        phi0 = float(np.arctan2(sw0[1], sw0[0]))
        Rm = np.array([[np.cos(-phi0), -np.sin(-phi0)], [np.sin(-phi0), np.cos(-phi0)]])
        warm = (Rm @ C0.T).T
        x0, th = seed_x0(w, warm_sites=warm)
    else:
        x0, th = seed_x0(w)"""
assert old2 in s, 'warm start line not found'
s = s.replace(old2, new2, 1)

# (3) candidate switches + theta-scaling + jacobian CS check + calibration-only mode
old3 = """def build():"""
new3 = """def candidate_switches():
    S = []
    for i in range(9):
        a_, b_ = C0[i], C0[(i + 1) % 9]
        m_ = (a_ + b_) / 2
        d_ = np.linalg.norm(b_ - a_)
        n_ = np.array([-(b_[1] - a_[1]) / d_, (b_[0] - a_[0]) / d_])
        mn = float(m_ @ n_)
        disc = np.sqrt(mn * mn + 1 - float(m_ @ m_))
        cand = [m_ + (-mn + disc) * n_, m_ - (-mn - disc) * n_]
        cand = [m_ + (-mn + disc) * n_, m_ + (-mn - disc) * n_]
        cand.sort(key=lambda P: max(np.linalg.norm(P - a_), np.linalg.norm(P - b_)))
        S.append(cand[0])
    return np.array(S)


sw0 = candidate_switches()[0]


def build():"""
assert old3 in s
s = s.replace(old3, new3, 1)

old4 = """wc = cand_widths()"""
new4 = """def jac_cs_check(seed=7, h=1e-7):
    \"\"\"central-difference check of the analytic jacobians of ALL 69 constraints x 53 vars\"\"\"
    rng = np.random.default_rng(seed)
    w = 0.5 * cand_widths() + 0.5 * np.full(9, 2 * np.pi / 9)
    x0, th = seed_x0(w)
    xr = x0 + 1e-3 * rng.standard_normal(NTOT)
    xr[0:8] = np.sort(np.abs(xr[0:8])) + 0.05        # keep angles increasing-ish & non-degenerate
    unpack, cons = build()
    worst = 0.0
    worst_tag = None
    for ci, cc in enumerate(cons):
        ga = np.asarray(cc['jac'](xr), dtype=float)
        gc = np.zeros(NTOT)
        for k in range(NTOT):
            xp, xm = xr.copy(), xr.copy()
            xp[k] += h
            xm[k] -= h
            gc[k] = (cc['fun'](xp) - cc['fun'](xm)) / (2 * h)
        err = float(np.max(np.abs(ga - gc)))
        if err > worst:
            worst, worst_tag = err, 'constraint %d (type=%s)' % (ci, cc.get('type'))
    return {'n_constraints_checked': len(cons), 'n_variables': NTOT, 'max_jac_error': worst,
            'worst_constraint': worst_tag, 'step': h}


wc = cand_widths()"""
assert old4 in s
s = s.replace(old4, new4, 1)

# (4) calibration-only mode
old5 = """log('=== joint outer attack start;"""
new5 = """import sys
CAL_ONLY = '--calib' in sys.argv
sw_all = candidate_switches()
phi0 = float(np.arctan2(sw_all[0][1], sw_all[0][0]))
if CAL_ONLY:
    chk = jac_cs_check()
    Rm = np.array([[np.cos(-phi0), -np.sin(-phi0)], [np.sin(-phi0), np.cos(-phi0)]])
    warm = (Rm @ C0.T).T
    x0c, thc = seed_x0(cand_widths(), warm_sites=warm)
    unpack, cons = build()
    direct = np.array([cc['fun'](x0c) for cc in cons[18:]])
    cal = {'R_STAR_label': 'C529 rational (NOT C891)', 'R_star': R_STAR,
           'phi0_of_first_switch': phi0, 'jacobian_check': chk,
           'direct_51_distances_at_saved_candidate': {
               'min': float(direct.min()), 'max': float(direct.max()),
               'n_negative_lt_-1e-12': int(np.sum(direct < -1e-12))},
           'widths_at_candidate': [float(v) for v in cand_widths()],
           'widths_legal': bool(cand_widths().max() <= L_CAP + 1e-12)}
    res = minimize(lambda x: x[-1], x0c, jac=lambda x: np.r_[np.zeros(NTOT - 1), 1.0],
                   method='SLSQP', bounds=[(None, None)] * (NTOT - 1) + [(0.05, 0.6)],
                   constraints=cons, options={'maxiter': 600, 'ftol': 1e-12})
    ivals = np.array([cc['fun'](res.x) for cc in cons[18:]])
    cal['calibration_run'] = {'V': float(res.fun), 'V_minus_R_star': float(res.fun) - R_STAR,
                              'success': bool(res.success), 'nit': int(res.nit),
                              'min_51_edge_residual': float(ivals.min())}
    cal['PASS'] = bool(chk['max_jac_error'] < 1e-6 and abs(res.fun - R_STAR) < 1e-5
                       and ivals.min() > -1e-9)
    (OUT / 'joint_outer_calibration.json').write_text(json.dumps(cal, indent=2), encoding='utf-8')
    print(json.dumps(cal, indent=1))
    raise SystemExit(0)


log('=== joint outer attack start;"""
assert old5 in s
s = s.replace(old5, new5, 1)
p.write_text(s, encoding='utf-8')
print('patched: sign fixed, rotation warm start, jac CS check + --calib mode')
