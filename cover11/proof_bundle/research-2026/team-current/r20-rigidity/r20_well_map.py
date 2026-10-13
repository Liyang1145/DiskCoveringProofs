"""r20-rigidity step 7: the flat well and the two registered 1e-60 objects.

G1  exact-rational values of the 18 active functions at x* (spread + argmax)
G2  fine map of gamma(x* - t v18) for t in [1e-10, 1e-8] -> well depth/radius
G3  n11/kkt2/frozen.json  and  research-2026/session2/n11alg/cert_sym60.json:
    gamma, mirror mismatch, relation to the saved candidate.
"""
import json, math, itertools
from pathlib import Path
import numpy as np
import mpmath as mp

P = Path(__file__).parent
ROOT = P.parents[2]
mp.mp.dps = 60
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
C64 = np.array([[int(v) / 1e17 for v in a] for a in raw['centers_scaled_1e17']])
LO = mp.mpf(raw['certified_interval']['lo'])
T_CERT = mp.mpf('0.379983853119838689722261606136093214308718957')
cal = json.loads((P / 'r20_calibration.json').read_text(encoding='utf-8'))
tight = cal['B']['tight_points']
J = np.load(P / 'r20_J60.npy')
U, S, Vt = np.linalg.svd(J)
v18 = Vt[17]
n = 11


def mpm_exact(rawjson, scale=10 ** 17):
    return [mp.matrix([mp.mpf(int(v)) / mp.mpf(scale) for v in a])
            for a in rawjson['centers_scaled_1e17']]


def circumcentre_mp(C, tri):
    a, b, c = tri
    A = mp.matrix([[C[b][0] - C[a][0], C[b][1] - C[a][1]],
                   [C[c][0] - C[a][0], C[c][1] - C[a][1]]])
    rhs = mp.matrix([(sum(C[b][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2,
                     (sum(C[c][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2])
    return mp.lu_solve(A, rhs)


def boundary_point(C, i, j, sgn):
    dv = C[i] - C[j]
    dd = sum(dv[t] ** 2 for t in range(2))
    A0 = mp.matrix([(sum(C[i][t] ** 2 for t in range(2)) - sum(C[j][t] ** 2 for t in range(2))) / 2
                    / dd * dv[t] for t in range(2)])
    nv = mp.matrix([-dv[1] / mp.sqrt(dd), dv[0] / mp.sqrt(dd)])
    s = mp.sqrt(1 - sum(A0[t] ** 2 for t in range(2)))
    return mp.matrix([A0[t] + sgn * s * nv[t] for t in range(2)])


acts = []
for p in tight:
    if p['kind'] == 'V3':
        acts.append(('V3', tuple(p['sites']), None))
    else:
        i, j = p['sites']
        dv = C64[i] - C64[j]
        dd = float(dv @ dv)
        A0 = (0.5 * (C64[i] @ C64[i] - C64[j] @ C64[j]) / dd) * dv
        nv = np.array([-dv[1], dv[0]]) / math.sqrt(dd)
        acts.append(('V2b', (i, j), 1 if ((np.array(p['point']) - A0) @ nv) > 0 else -1))


def f_act(kind, sites, sgn, C):
    if kind == 'V3':
        u = circumcentre_mp(C, sites)
        return mp.sqrt(sum((u[t] - C[sites[0]][t]) ** 2 for t in range(2)))
    p = boundary_point(C, sites[0], sites[1], sgn)
    return mp.sqrt(sum((p[t] - C[sites[0]][t]) ** 2 for t in range(2)))


def shifted(Cbase, delta_flat):
    return [mp.matrix([Cbase[i][0] + mp.mpf(float(delta_flat[2 * i])),
                       Cbase[i][1] + mp.mpf(float(delta_flat[2 * i + 1]))]) for i in range(n)]


CM = mpm_exact(raw)
vals = [f_act(k, s, g, CM) for (k, s, g) in acts]
print('G1  18 active values at x* (exact rationals, 60 dps), deviation from max:')
mx = max(vals)
for (k, s, g), v in zip(acts, vals):
    print('    %-4s %-9s  f - max = %s' % (k, str(s), mp.nstr(v - mx, 4)))
print('    spread (max-min) = %s' % mp.nstr(mx - min(vals), 4))
print('    gamma(x*) - certified lo = %s' % mp.nstr(mx - LO, 4))

print('\nG2  well map  gamma(x* - t v18) - gamma* :')
g0 = mx
for t in ('1e-10', '2e-10', '3e-10', '5e-10', '7e-10', '1e-9', '1.4e-9', '2e-9', '3e-9', '5e-9', '8e-9', '1.2e-8'):
    tt = mp.mpf(t)
    dv = shifted(CM, -float(tt) * v18)
    d = max(f_act(k, s, g, dv) for (k, s, g) in acts) - g0
    print('    t=%-7s  delta = %+.6e    delta/t = %+.4e' % (t, d, d / tt))

# alternative descent direction from the SVD-based multiplier residual (test the
# second-best candidate direction for a deeper well)
print('\nG2b same map along +v18 (the uphill side), coarse:')
for t in ('1e-9', '1e-8', '1e-7'):
    tt = mp.mpf(t)
    dv = shifted(CM, float(tt) * v18)
    d = max(f_act(k, s, g, dv) for (k, s, g) in acts) - g0
    print('    t=%-7s  delta = %+.6e' % (t, d))


# ---------- G3 other objects ----------------------------------------------
def load_obj(path):
    p = ROOT / path
    if not p.exists():
        return None
    d = json.loads(p.read_text(encoding='utf-8-sig'))
    for key, sc in (('centers_scaled_1e17', 10 ** 17), ('centers_scaled_1e60', 10 ** 60),
                    ('centers', 1.0)):
        if key in d:
            try:
                Cx = np.array([[float(mp.mpf(int(v)) / mp.mpf(10) ** int(math.log10(sc)))
                                if isinstance(v, str) else float(v) for v in a] for a in d[key]])
                return path, Cx, key, d
            except Exception as e:
                print('    (%s: cannot parse %s: %s)' % (path, key, e))
    return path, None, None, d


def mirror_mismatch(Cx, a):
    Rm = np.array([[math.cos(2 * a), math.sin(2 * a)], [math.sin(2 * a), -math.cos(2 * a)]])
    Y = Cx @ Rm
    return max(float(np.linalg.norm(Y - Cx[i], axis=1).min()) for i in range(len(Cx)))


print('\nG3  registered objects:')
for path in ('n11/upper/certified_object.json', 'n11/kkt2/frozen.json',
             'research-2026/session2/n11alg/cert_sym60.json'):
    p = ROOT / path
    if not p.exists():
        print('    %s : MISSING' % path)
        continue
    d = json.loads(p.read_text(encoding='utf-8-sig'))
    keys = [k for k in d.keys() if 'cent' in k.lower() or 'scale' in k.lower()]
    print('    %-52s keys=%s' % (path, keys[:8]))
