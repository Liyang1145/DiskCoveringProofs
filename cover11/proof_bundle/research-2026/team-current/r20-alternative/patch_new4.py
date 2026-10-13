from pathlib import Path
import json

# (A) add a finite-difference check of ALL 51 constraint Jacobians incl. the 8 y-coordinates,
#     on a GENERIC (non-candidate) y, to joint_oracle_attack_new4.py
p = Path(__file__).with_name('joint_oracle_attack_new4.py')
s = p.read_text(encoding='utf-8')
old = "if __name__ == '__main__':"
new = '''def jac_cs_check(y8=None, h=1e-7, seed=11):
    """central-difference audit of the analytic Jacobians: all 51 constraints x 53 variables,
    x-all-8 y-coordinates included, at a GENERIC (non-candidate) y."""
    rng = np.random.default_rng(seed)
    if y8 is None:
        y8 = rng.dirichlet(np.ones(9))[:8] * 0.9            # generic interior point
    cons = None
    # rebuild the constraint list without solving
    dummy = solve(np.asarray(y8, dtype=float), maxiter=1)     # obtains a consistent x0 via unpack
    # construct cons by calling solve's inner builder through a tiny trick: re-run one SLSQP step
    import types
    # the constraint list is built inside solve(); recreate it here identical to solve()
    def unpack(x):
        w = widths_from_y(x[:8])
        th = np.concatenate([[0.0], np.cumsum(w)])[:9]
        U = np.stack([np.cos(th), np.sin(th)], axis=1)
        return U, th, x[IC:IC + 22].reshape(11, 2), x[IZ:IZ + 22].reshape(11, 2), x[-1], w
    cons = []

    def mk(site, other, is_face):
        def f(x):
            U, th, c, z, r, w = unpack(x)
            t = z[other] if is_face else U[other]
            return r - float(np.linalg.norm(c[site] - t))

        def jac(x):
            U, th, c, z, r, w = unpack(x)
            t = z[other] if is_face else U[other]
            d = c[site] - t
            n = np.linalg.norm(d)
            g = np.zeros(NV)
            g[-1] = 1.0
            if n > 1e-14:
                u = d / n
                g[IC + 2 * site:IC + 2 * site + 2] = -u
                if is_face:
                    g[IZ + 2 * other:IZ + 2 * other + 2] = u
                else:
                    ta = th[other]
                    dUdth = np.array([-np.sin(ta), np.cos(ta)])
                    for k in range(8):
                        if k < other:
                            g[k] += float(u @ dUdth) * (-D_CAP)
            return g
        return {'type': 'ineq', 'fun': f, 'jac': jac}
    for i in range(9):
        cons.append(mk(i, i, False))
        cons.append(mk(i, (i - 1) % 9, False))
    for fi, face in enumerate(FACES):
        for s in face:
            cons.append(mk(s, fi, True))
    xr = np.zeros(NV)
    xr[:8] = y8
    sites = np.zeros((11, 2))
    for i in range(9):
        sites[i] = np.array([0.3 * np.cos(2 * np.pi * i / 9 + 0.2), 0.3 * np.sin(2 * np.pi * i / 9 + 0.2)])
    sites[9] = np.array([0.05, 0.10]); sites[10] = np.array([-0.05, -0.08])
    xr[IC:IC + 22] = sites.reshape(-1)
    zz = np.zeros((11, 2))
    for fi, face in enumerate(FACES):
        zz[fi] = sites[face].mean(axis=0) + np.array([0.01, -0.01])
    xr[IZ:IZ + 22] = zz.reshape(-1)
    xr[-1] = 0.5
    worst, tag, worst_k = 0.0, None, None
    for ci, cc in enumerate(cons[:51]):
        ga = np.asarray(cc['jac'](xr), dtype=float)
        for k in range(NV):
            xp, xm = xr.copy(), xr.copy()
            xp[k] += h; xm[k] -= h
            gc = (cc['fun'](xp) - cc['fun'](xm)) / (2 * h)
            err = abs(ga[k] - gc)
            if err > worst:
                worst, tag, worst_k = err, 'constraint %d' % ci, k
    return {'y_used': [float(v) for v in y8], 'n_constraints': 51, 'n_variables': NV,
            'max_jac_error': worst, 'worst': tag, 'worst_variable': worst_k, 'step': h,
            'PASS_lt_1e-6': bool(worst < 1e-6)}


if __name__ == '__main__':'''
assert old in s
s = s.replace(old, new, 1)
s = s.replace("""    t0 = time.time()
    cand, bary378, facet = get_node_y()""",
              """    t0 = time.time()
    chk = jac_cs_check()
    print('jacobian CS check:', json.dumps(chk))
    if not chk['PASS_lt_1e-6']:
        print('JACOBIAN CHECK FAILED -> not running the four starts')
        raise SystemExit(1)
    cand, bary378, facet = get_node_y()""", 1)
s = s.replace("""    rep = {'R_STAR_label': 'C529 rational (NOT C891)', 'R_star': R_STAR, 'L_cap': L_CAP,""",
              """    rep = {'R_STAR_label': 'C529 rational (NOT C891)', 'R_star': R_STAR, 'L_cap': L_CAP,
           'jacobian_cs_check': chk,""", 1)
p.write_text(s, encoding='utf-8')

# (B) mark the old twelve-start joint run invalid (keep the log)
oldj = Path(__file__).with_name('joint_oracle_attack.json')
inv = Path(__file__).with_name('joint_oracle_attack_INVALID.json')
if oldj.exists():
    d = json.loads(oldj.read_text(encoding='utf-8'))
    d['implementation_invalid'] = True
    d['invalid_reason'] = ('y-angular Jacobian entries were all zero in joint_oracle_attack.py '
                           '(lines ~64-76): the run degenerated to fixed-width optimisation; the '
                           'candidate control cannot detect a missing Jacobian; conclusion '
                           'withdrawn (kept as log)')
    inv.write_text(json.dumps(d, indent=2), encoding='utf-8')
print('new4 patched with jac CS gate; old 12-start run marked invalid ->',
      inv.name if inv.exists() else 'no old json found')
