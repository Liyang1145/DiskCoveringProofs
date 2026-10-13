# -*- coding: utf-8 -*-
"""C862b follow-up: minimize lambda_max(Hess) over WIDTH-LEGAL points (b_j >= bmin(r)).
Reuses the definitions of check_p41_points.py; 2 seeds x 80 DE iterations; own scope."""
import json, math
from pathlib import Path
import numpy as np
from scipy.optimize import differential_evolution

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
z = json.loads((LEAD / 'joint_nested_frozen.json').read_text(encoding='utf-8-sig'))['z']
R0 = 19/50
a1, a2 = z[1]-z[9], z[3]-z[9]
be1, be2 = -z[16]/(4*R0*R0), z[20]/(4*R0*R0)
g1, g2 = -z[78]/(2*R0), z[82]/(2*R0)
c1, c2 = abs(g1), abs(g2)
SUMB = 2*(be1+be2)
G = 2*math.pi - 16*math.asin(R0)

def bmin(r):
    eta = G/2
    return (math.acos(r) + math.asin(math.sin(eta)/r) - eta)/2

def geo(r, b1, b2, delta):
    s = math.sqrt(1-r*r)
    if not (delta > -b2 and delta < b1): return None
    A, B = b1-delta, b2+delta
    if min(A, B) <= 0: return None
    D1, D2 = 2*r*math.sin(b1), 2*r*math.sin(b2)
    return s, A, B, (D1*math.cos(b1), D1*math.sin(b1)), (D2*math.cos(b2), -D2*math.sin(b2))

def fiber(r, b1, b2, delta):
    g = geo(r, b1, b2, delta)
    if g is None: return None
    s, A, B, Q1, Q2 = g
    disc = s*s*math.cos(delta)**2 - 2*r*(1-r)
    if disc < 0: return None
    lo = max(2*r*abs(math.sin(delta)), s*math.cos(delta)-math.sqrt(disc))
    hi = min(2*r*math.sin(b1+A), 2*r*math.sin(b2+B), s*math.cos(delta)+math.sqrt(disc))
    return (lo, hi) if lo <= hi else None

def hess(v, t, r, b1, b2):
    g = geo(r, b1, b2, math.atan2(t, v)); s, A, B, Q1, Q2 = g
    H = np.array([[SUMB, 0.0], [0.0, SUMB]])
    for Q, c, a in ((Q1, c1, a1), (Q2, c2, a2)):
        L = math.hypot(v-Q[0], t-Q[1]); n = np.array([(v-Q[0])/L, (t-Q[1])/L])
        H -= (c/L)*(np.eye(2) - np.outer(n, n))
        th = -math.pi/4
        w = np.array([math.cos(th)*n[0]-math.sin(th)*n[1], math.sin(th)*n[0]+math.cos(th)*n[1]])
        H += (a/(L*L))*(2*np.outer(w, w) - np.eye(2))
    return H

def lam_max(v, t, r, b1, b2):
    return float(np.linalg.eigvalsh(hess(v, t, r, b1, b2))[1])

def obj(y):
    r, b1, b2, delta, fh = y
    r = min(max(r, 0.375), 0.38); bc = math.acos(r); bm = bmin(r)
    if not (bm <= b1 <= bc and bm <= b2 <= bc): return 1e3
    fb = fiber(r, b1, b2, delta)
    if fb is None or not (0 <= fh <= 1): return 1e3
    H = fb[0] + fh*(fb[1]-fb[0])
    return np.sign(1)*lam_max(H*math.cos(delta), H*math.sin(delta), r, b1, b2)

rows = []
for seed in (86250, 86251):
    sol = differential_evolution(obj, [(0.375, 0.38), (0.60, 1.19), (0.60, 1.19), (-1.19, 1.19), (0, 1)],
                                 seed=seed, popsize=12, maxiter=80, tol=1e-12, polish=True, init='sobol')
    r, b1, b2, delta, fh = sol.x
    r = min(max(r, 0.375), 0.38)
    fb = fiber(r, b1, b2, delta) or (float('nan'), float('nan'))
    H = fb[0] + fh*(fb[1]-fb[0])
    v, t = H*math.cos(delta), H*math.sin(delta)
    ev = np.linalg.eigvalsh(hess(v, t, r, b1, b2))
    rec = dict(seed=seed, value=float(ev[1]), lam_min=float(ev[0]), r=r, b1=b1, b2=b2, delta=delta,
               H=H, bmin=bmin(r), width_legal=bool(b1 >= bmin(r) and b2 >= bmin(r)),
               H_interior=bool(fb[0] < H < fb[1]), nfev=int(sol.nfev))
    rows.append(rec)
    print('seed %d: min lambda_max = %.6f (lam_min %.6f) at r=%.5f b1=%.5f b2=%.5f delta=%+.5f H=%.5f'
          % (seed, rec['value'], rec['lam_min'], r, b1, b2, delta, H))
    print('        width-legal: %s (bmin=%.5f) ; H interior: %s (fiber [%.5f, %.5f])'
          % (rec['width_legal'], rec['bmin'], rec['H_interior'], fb[0], fb[1]))
print('VERDICT INPUT: best width-legal lambda_max = %.6f  => %s'
      % (min(x['value'] for x in rows),
         'ND point EXISTS inside the width-legal domain' if min(x['value'] for x in rows) < 0
         else 'no ND point found inside the width-legal domain'))
Path('out/p42_widthlegal_nd.json').write_text(json.dumps(rows, indent=1, default=float))
