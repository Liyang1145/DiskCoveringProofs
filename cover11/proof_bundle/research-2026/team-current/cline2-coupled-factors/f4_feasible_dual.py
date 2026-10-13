"""cline2-coupled-factors f4: first-moment (linear-in-half-side) coupling, honest bound.

ASSEMBLY: identical to lead/q0_closure_dual.py, verified in f3_lead_repro.py (reproduces
sample_upper = 3.175702557547944 on the saved z).  On top of it we open the first-moment
adjoint rows that the lead leaves empty:

    rho_f sin A = rho_g sin B   (exact, C816)   ==>   sqrt(x_f) sin A = sqrt(x_g) sin B

so a free multiplier L[e] per shared edge contributes +sgn_f(e) sin A_f * L[e] in each
face factor and -sin b * L[e] in the boundary switch factor; the 18 radius-copy
multipliers lin[94:112] get their matching sqrt(x) counterparts too.

BOUND ARCHITECTURE: for each factor we keep the full sample set and minimize
    const.z + sum_f t_f     s.t.   t_f + M_f z  >=  -vals_f     for every sample,
by column generation on the sampled domains.  At any z, the pricing value
max_f(vals_f + M_f z) is an honest upper bound for the factor's true domain supremum
(samples <= full domain), and the final reported ub is the LP optimum.  Numeric only.
"""
import numpy as np, json, math, sys, time
from pathlib import Path
from scipy.optimize import linprog

P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
OUT.mkdir(exist_ok=True)
R = 19/50
pi = math.pi
N, NR, NA = 36, 12, 96
START, SPAN = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (0, 4)
OPEN_L = (len(sys.argv) < 4) or (sys.argv[3] != 'closed')


def build(open_L=True, N=N, NR=NR, NA=NA):
    row = json.loads((LEAD / f'q0_closure_dual_{START}_{SPAN}.json').read_text())
    z0 = np.array(row['z'])
    faces = [tuple(f) for f in row['faces']]
    edges = [tuple(e) for e in row['edges']]
    assert all(a < b for a, b in edges)
    ei = {e: k for k, e in enumerate(edges)}
    ne, nf = len(edges), len(faces)
    side0, rr0, kap0, lam0, eta0, lin0, cl0 = 11, 32, 50, 71, 72, 73, 112
    nz0 = 121
    nl = ne if open_L else 0
    nz = nz0 + nl
    adj = {e: [(t, next(k for k in f if k not in e))
               for t, f in enumerate(faces) if e[0] in f and e[1] in f] for e in edges}
    sgn = {e: {adj[e][0][0]: 1.0} if len(adj[e]) == 1 else
            {adj[e][0][0]: 1.0, adj[e][1][0]: -1.0} for e in edges}
    base = np.zeros(nz)
    base[0:9] = pi
    base[9:11] = 2*pi
    base[kap0:lam0] = pi
    base[lam0] = -2*pi
    base[cl0:cl0+9] = -pi
    factors = []                                # (name, vals, M)
    aa = np.array([(i*pi/N, j*pi/N, (N-i-j)*pi/N) for i in range(N+1) for j in range(N+1-i)])
    for t, f in enumerate(faces):
        xx = np.linspace(0, 1, 31)**2
        ang = np.tile(aa, (len(xx), 1)); x = np.repeat(xx, len(aa))
        v = 2*R*R*x*np.prod(np.sin(ang), axis=1)
        M = np.zeros((len(v), nz))
        for k, i in enumerate(f):
            e = tuple(sorted(j for j in f if j != i)); ee = ei[e]
            sg = 1 if adj[e][0][0] == t else -1
            M[:, i] -= ang[:, k]; M[:, kap0+ee] -= ang[:, k]
            M[:, side0+ee] += sg*x*np.sin(ang[:, k])**2
            M[:, lin0+ee] += sg*np.sqrt(x)*np.sin(ang[:, k])
            if open_L:
                M[:, nz0+ee] += sg*np.sin(ang[:, k])
        factors.append((f'face{t}', v, M))
    for bi in range(9):
        i, j = bi, (bi+1) % 9; e = tuple(sorted((i, j))); ee = ei[e]
        b = np.tile(np.linspace(0, pi/2, 4*N+1), 31)
        x = np.repeat(np.linspace(0, 1, 31)**2, 4*N+1)
        v = R*R*x*np.sin(2*b)/2
        M = np.zeros((len(v), nz))
        M[:, cl0+bi] += 2*b
        M[:, i] += b; M[:, j] += b; M[:, kap0+ee] -= b
        M[:, side0+ee] -= x*np.sin(b)**2
        M[:, lin0+ee] -= np.sqrt(x)*np.sin(b)
        M[:, rr0+2*i+1] += x; M[:, rr0+2*j] += x
        M[:, lin0+21+2*i+1] += np.sqrt(x); M[:, lin0+21+2*j] += np.sqrt(x)
        if open_L:
            M[:, nz0+ee] -= np.sin(b)
        factors.append((f'switch{bi}', v, M))
    grid = np.array([(a, u, v) for a in np.linspace(0, pi, NA+1)
                     for u in np.linspace(0, 1, NR+1) for v in np.linspace(0, 1, NR+1)])
    a, u, v = grid.T
    ch = R*np.sqrt(np.maximum(0, u*u+v*v-2*u*v*np.cos(a)))
    w = 2*np.arcsin(ch/2)
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
        if open_L:
            kr = ei[tuple(sorted((i, (i+1) % 9)))]
            kl = ei[tuple(sorted(((i-1) % 9, i)))]
            M[:, nz0+kr] = -u
            M[:, nz0+kl] = -v
        factors.append((f'ring{i}', S, M))
    return dict(row=row, z0=z0, nz=nz, nl=nl, nz0=nz0, base=base, factors=factors,
                edges=edges, faces=faces, ei=ei, adj=adj)


def bootstrap_bound(pr):
    ub = float(pr['base'] @ np.concatenate([pr['z0'], np.zeros(pr['nl'])]))
    z = np.concatenate([pr['z0'], np.zeros(pr['nl'])])
    detail = []
    for name, v, M in pr['factors']:
        vals = v + M @ z
        j = int(np.argmax(vals)); ub += vals[j]
        detail.append((name, float(vals[j]), j))
    return ub, detail


def var_bounds(nz0, nl, bounds_l=(-3, 3)):
    """Exactly the lead's declaration: bounds[eta]=(0,0); kappa/side/lin free in [-3,3];
    the 76 nonnegative angle slacks in [0,3] are bounds[kap:lin] and bounds[112:121]."""
    b = [(-3, 3)]*11                       # mu
    b += [(-3, 3)]*(32-11)                 # side
    b += [(-3, 3)]*(50-32)                 # rr
    b += [(0, 3)]*(71-50)                  # kappa >= 0
    b += [(-3, 3)]                         # lambda
    b += [(0, 0)]                          # eta == 0 (q0)
    b += [(-3, 3)]*(94-73)                 # lin_side
    b += [(-3, 3)]*(112-94)                # lin_rad
    b += [(-3, 3)]*(121-112)               # closure h
    assert len(b) == nz0, (len(b), nz0)
    return b + [bounds_l]*nl


def solve(pr, maxiter=200, tol=1e-11, verbose=True, bounds_l=(-3, 3)):
    nz, nl = pr['nz'], pr['nl']
    z0 = pr['z0']
    nb = len(pr['factors'])
    base = pr['base']
    bnds = var_bounds(pr['nz0'], nl, bounds_l)
    if nl == 0 and not np.allclose(z0, z0):
        pass
    rows, rhs, pick = [], [], {}
    for k, (name, v, M) in enumerate(pr['factors']):
        j = int(np.argmax(v)); pick[k] = j
        rows.append(np.concatenate([M[j], -np.eye(nb)[k]]))
        rhs.append(-float(v[j]))
    c = np.concatenate([base, np.ones(nb)])
    A_ub = np.array(rows)
    best, bestz, hist = np.inf, None, []
    for it in range(maxiter):
        sol = linprog(c, A_ub=A_ub, b_ub=np.array(rhs), bounds=bnds + [(None, None)]*nb,
                      method='highs')
        if not sol.success:
            print('LP FAIL', sol.message); break
        z = sol.x[:nz]
        ub = float(base @ z); nnew = 0
        for k, (name, v, M) in enumerate(pr['factors']):
            vals = v + M @ z
            j = int(np.argmax(vals)); ub += float(vals[j])
            if j != pick[k]:
                pick[k] = j
                rows.append(np.concatenate([M[j], -np.eye(nb)[k]]))
                rhs.append(-float(v[j])); nnew += 1
        A_ub = np.array(rows)
        hist.append((it, float(sol.fun), float(ub), len(rows)))
        if ub < best:
            best, bestz = ub, z.copy()
        if verbose:
            print(f'  it{it:3d} lp={sol.fun:.9f} ub={ub:.9f} cuts={len(rows)}', flush=True)
        if abs(ub - sol.fun) < tol:
            break
    return best, bestz, hist, pick


if __name__ == '__main__':
    t0 = time.time()
    pr = build(open_L=OPEN_L)
    print(f'built ({START},{SPAN}) open_L={OPEN_L} nz={pr["nz"]} '
          f'factors={len(pr["factors"])} t={time.time()-t0:.1f}s', flush=True)
    ub, det = bootstrap_bound(pr)
    print(f'lead z0 bound (bootstrap) = {ub:.9f}   lead sample_upper = '
          f'{pr["row"]["sample_upper"]:.9f}')
    for name, v, j in det:
        print(f'   {name:10s} {v: .9f} #{j}')
    print(f'elapsed {time.time()-t0:.1f}s')
