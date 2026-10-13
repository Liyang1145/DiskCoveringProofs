from pathlib import Path

p = Path(__file__).with_name('joint_outer_attack.py')
s = p.read_text(encoding='utf-8')

old = """    cons = []
    for k in range(9):                                    # widths: eps <= L_k <= L_CAP
        lo = 0.0 if k == 0 else None
        cons.append({'type': 'ineq',
                     'fun': lambda x, k=k: (x[k] - (0.0 if k == 0 else x[k - 1])) - EPS_MIN
                     if k < 8 else (2 * np.pi - x[7]) - EPS_MIN,
                     'jac': (lambda x, k=k: np.r_[np.zeros(k), 1.0, np.zeros(NTH - k - 1)]
                             if k < 8 else np.r_[np.zeros(7), -1.0])})
        cons.append({'type': 'ineq',
                     'fun': lambda x, k=k: L_CAP - ((x[k] - (0.0 if k == 0 else x[k - 1]))
                                                    if k < 8 else (2 * np.pi - x[7])),
                     'jac': (lambda x, k=k: np.r_[np.zeros(k), -1.0, np.zeros(NTH - k - 1)]
                             if k < 8 else np.r_[np.zeros(7), 1.0])})"""
new = """    def width_val(x, k):
        return (x[k] - (0.0 if k == 0 else x[k - 1])) if k < 8 else (2 * np.pi - x[7])

    def width_grad(k):
        g = np.zeros(NTOT)
        if k < 8:
            g[k] = 1.0
        if k >= 1:
            g[k - 1] -= 1.0
        return g

    cons = []
    for k in range(9):                                    # widths: eps <= L_k <= L_CAP
        cons.append({'type': 'ineq',
                     'fun': lambda x, k=k: width_val(x, k) - EPS_MIN,
                     'jac': lambda x, k=k: width_grad(k)})
        cons.append({'type': 'ineq',
                     'fun': lambda x, k=k: L_CAP - width_val(x, k),
                     'jac': lambda x, k=k: -width_grad(k)})"""
assert old in s, 'width block not found'
s = s.replace(old, new, 1)

old2 = """            if anchor >= 1:
                g[anchor - 1] = 2 * float(d @ np.array([-np.sin(np.arctan2(U[anchor][1], U[anchor][0])),
                                                        np.cos(np.arctan2(U[anchor][1], U[anchor][0]))]))"""
new2 = """            if anchor >= 1:
                # d/dtheta of  r^2 - |c - U|^2  =  -2 (c-U) . U'(theta) = 2 (c-U) . (sin, -cos)
                th_a = x[anchor - 1]
                g[anchor - 1] = 2 * float(d[0] * np.sin(th_a) - d[1] * np.cos(th_a))"""
assert old2 in s, 'theta jac not found'
s = s.replace(old2, new2, 1)
p.write_text(s, encoding='utf-8')
print('patched width + theta jacobians')
