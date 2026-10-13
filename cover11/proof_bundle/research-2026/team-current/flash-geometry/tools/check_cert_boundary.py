import numpy as np, io, json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

def load_cert():
    d = json.load(io.open('n11/upper/certified_object.json', encoding='utf-8'))
    return np.array([[int(a)/1e17, int(b)/1e17] for a, b in d['centers_scaled_1e17']])

def load_active12():
    import re
    txt = io.open('n11/active/certificate.md', encoding='utf-8').read()
    blk = re.findall(r'c\s*\d+\s*=\s*\(\s*(-?[\d.]+),\s*(-?[\d.]+)\)', txt)
    return np.array([[float(a), float(b)] for a, b in blk])

def boundary_min(C, th):
    P = np.stack([np.cos(th), np.sin(th)], 1)
    dd = np.sqrt(((P[:, None, :] - C[None, :, :])**2).sum(-1))
    return dd.min(1), dd

def report(name, C):
    print("=" * 78); print(name, " 11 centres")
    rho = np.hypot(C[:, 0], C[:, 1])
    print(" |c| =", np.round(rho, 6))
    print(" n with |c| < 1-r :", int((rho < 1 - 0.3799838531198387090).sum()),
          "-> these CANNOT cover any boundary point")
    # arc coverage using alpha = arcsin(r/rho) about direction of c
    R = 0.3799838531198387090
    tot = 0.0; ivals = []
    for c in C:
        r = np.hypot(*c)
        if r <= R or r >= 1 / 1:
            continue
        a = np.arcsin(R / r)
        phi = np.arctan2(c[1], c[0])
        ivals.append((phi - a, phi + a))
        tot += 2 * a
    print(" sum of arc widths of disks that meet the circle = %.6f  (need 2pi=%.6f)" % (tot, 2*np.pi))
    # exact boundary check on fine grid
    th = np.linspace(0, 2 * np.pi, 2000001)
    mn, _ = boundary_min(C, th)
    k = int(np.argmax(mn))
    print(" max_{|x|=1} min_i |x-c_i| = %.12f at angle %.9f  (angle/pi=%.9f)" % (mn[k], th[k], th[k] / np.pi))
    print("   point =", np.round(np.array([np.cos(th[k]), np.sin(th[k])]), 9))
    print("   R_cert = 0.3799838531198387090 : boundary COVERED?" , mn[k] <= R)
    # local refine near the argmax
    lo, hi = th[k] - 2e-6, th[k] + 2e-6
    for _ in range(200):
        m1 = lo + (hi - lo) / 3; m2 = hi - (hi - lo) / 3
        if boundary_min(C, np.array([m1]))[0][0] > boundary_min(C, np.array([m2]))[0][0]:
            hi = m2
        else:
            lo = m1
    tbest = 0.5 * (lo + hi)
    v, _ = boundary_min(C, np.array([tbest]))
    print("   refined argmax: angle %.12f  value %.14f" % (tbest, v[0]))
    # distances of the two whose minimum is best
    return th[k], mn[k]

C1 = load_cert()
th1, v1 = report("n11/upper/certified_object.json (the '唯一认证对象')", C1)

try:
    C2 = load_active12()
    print()
    th2, v2 = report("n11/active 12-decimal object", C2)
except Exception as e:
    print("active parse failed:", e)
