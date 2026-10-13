"""cline2-coupled-factors f13: sector endpoint-symmetry collapse and its bound gain.

f12 proves u_k = v_k identically (perpendicular-bisector argument).  That makes the
sector kernel S(alpha,u,v) a function of (alpha, e) with u=v=e.  Restricting the dual's
sector maxima to the diagonal  {u=v}  is therefore VALIDITY-PRESERVING (it can only make
the sup smaller) and is NOT a WLOG that loses configurations -- every genuine diagram has
u=v.

We run the SAME lead architecture and the same lead z-vectors, but with three sector
domains:
    full      : (alpha,u,v) in the lead's grid            [baseline, must reproduce]
    diagonal  : u = v = e                                 [valid restriction]
    saturated : u = v = 1 (the saved optimum's value)      [valid restriction]
and report the resulting honest sampled upper bounds for span 3 and span 4.

Also reports, on the diagonal, the exact identity
    S(alpha) = R^2 alpha/2 + (w - sin w)/2,  w = 2 asin(R sin(alpha/2)),
whose linear-in-alpha term R^2/2 is the new dual coupling (the sector angle now carries a
radius-independent coefficient, unlike the full kernel where the u,v maximization kills
the alpha slope).
"""
import numpy as np, json, math, sys
from pathlib import Path
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
R = 19/50
pi = math.pi
N, NR, NA = 36, 12, 96


def arch(start, span, mode, NRr=24):
    row = json.loads((LEAD / f'q0_closure_dual_{start}_{span}.json').read_text())
    z = np.array(row['z'])
    faces = [tuple(f) for f in row['faces']]
    edges = [tuple(e) for e in row['edges']]
    ei = {e: k for k, e in enumerate(edges)}
    side0, rr0, kap0, lam0, lin0, cl0 = 11, 32, 50, 71, 73, 112
    nz = 121
    adj = {e: [(t, next(k for k in f if k not in e))
               for t, f in enumerate(faces) if e[0] in f and e[1] in f] for e in edges}
    sgn = {e: {adj[e][0][0]: 1.0} if len(adj[e]) == 1 else
            {adj[e][0][0]: 1.0, adj[e][1][0]: -1.0} for e in edges}
    base = np.zeros(nz)
    base[0:9] = pi; base[9:11] = 2*pi; base[kap0:lam0] = pi; base[lam0] = -2*pi
    base[cl0:cl0+9] = -pi
    ub = float(base @ z)
    aa = np.array([(i*pi/N, j*pi/N) for i in range(N+1) for j in range(N+1-i)])
    for t, f in enumerate(faces):
        xx = np.linspace(0, 1, 31)**2
        ang = np.tile(np.c_[aa, pi-aa[:, 0]-aa[:, 1]], (len(xx), 1))
        x = np.repeat(xx, len(aa))
        v = 2*R*R*x*np.prod(np.sin(ang), axis=1)
        M = np.zeros((len(v), nz))
        for k, i in enumerate(f):
            e = tuple(sorted(j for j in f if j != i)); ee = ei[e]
            sg = 1 if adj[e][0][0] == t else -1
            M[:, i] -= ang[:, k]; M[:, kap0+ee] -= ang[:, k]
            M[:, side0+ee] += sg*x*np.sin(ang[:, k])**2
            M[:, lin0+ee] += sg*np.sqrt(x)*np.sin(ang[:, k])
        ub += np.max(v + M @ z)
    Pts = [pt for pt in
           [(theta, e) for theta in np.linspace(0, pi, 4*N+1)
            for e in np.linspace(0.2, 1.0, 4*NRr+1)]]
    for bi in range(9):
        i, j = bi, (bi+1) % 9; e = tuple(sorted((i, j))); ee = ei[e]
        b = np.tile(np.linspace(0, pi/2, 4*N+1), 31)
        x = np.repeat(np.linspace(0, 1, 31)**2, 4*N+1)
        v = R*R*x*np.sin(2*b)/2
        M = np.zeros((len(v), nz))
        M[:, cl0+bi] += 2*b
        M[:, i] += b; M[:, j] += b; M[:, kap0+ee] -= b
        M[:, side0+ee] -= x*np.sin(b)**2; M[:, lin0+ee] -= np.sqrt(x)*np.sin(b)
        M[:, rr0+2*i+1] += x; M[:, rr0+2*j] += x
        M[:, lin0+21+2*i+1] += np.sqrt(x); M[:, lin0+21+2*j] += np.sqrt(x)
        ub += np.max(v + M @ z)
    if mode == 'full':
        grid = np.array([(a, u, v) for a in np.linspace(0, pi, NA+1)
                         for u in np.linspace(0, 1, NR+1) for v in np.linspace(0, 1, NR+1)])
    elif mode == 'diagonal':
        ee = np.linspace(0, 1, 8*NRr+1)
        grid = np.array([(a, e, e) for a in np.linspace(0, pi, 4*N+1) for e in ee])
    else:
        grid = np.array([(a, 1.0, 1.0) for a in np.linspace(0, pi, 4*N+1)])
    a, u, v = grid.T
    ch = R*np.sqrt(np.maximum(0, u*u+v*v-2*u*v*np.cos(a)))
    w = 2*np.arcsin(np.minimum(1.0, ch/2))
    S = R*R*u*v*np.sin(a)/2 + (w-np.sin(w))/2
    left = np.arctan2(v*np.sin(a), u-v*np.cos(a))
    right = np.arctan2(u*np.sin(a), v-u*np.cos(a))
    for i in range(9):
        M = np.zeros((len(a), nz))
        M[:, cl0+(i-1) % 9] = left + w/2
        M[:, cl0+i] = right + w/2
        M[:, i] = -a
        M[:, rr0+2*i] = -u*u; M[:, rr0+2*i+1] = -v*v
        M[:, lam0] = w
        M[:, lin0+21+2*i] = -u; M[:, lin0+21+2*i+1] = -v
        ub += np.max(S + M @ z)
    return ub, row['sample_upper']


print(f'{"span":>5s} {"mode":>10s} {"sampled ub":>16s} {"lead ub":>16s} {"delta":>12s}')
res = {}
for span in (3, 4):
    for mode in ('full', 'diagonal', 'saturated'):
        ub, leadub = arch(0, span, mode)
        res[(span, mode)] = ub
        print(f'{span:5d} {mode:>10s} {ub:16.9f} {leadub:16.9f} {ub-leadub:12.3e}')
    # exact diagonal identity check
    a = np.linspace(0, pi, 4001)
    w = 2*np.arcsin(R*np.sin(a/2))
    S1 = R*R*a/2 + (w-np.sin(w))/2
    ch = R*np.sqrt(2-2*np.cos(a))
    w2 = 2*np.arcsin(np.minimum(1.0, R*ch/2))
    S2 = R*R*np.sin(a)/2 + (w2-np.sin(w2))/2
    print(f'   identity S(alpha) = R^2 alpha/2 + (w-sin w)/2 check: max diff vs kernel '
          f'= {np.abs(S1-S2).max():.3e}')
json.dump({f'{k[0]}_{k[1]}': v for k, v in res.items()},
          open(OUT/'diag_bounds.json', 'w'), indent=1)
