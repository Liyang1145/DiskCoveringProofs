"""cline2-coupled-factors f18: bounded first-moment block, stated correctly.

Correction to f17: the uniform-offset experiment there shows the bound INCREASES with the
offset, and the per-direction slopes have both signs.  The reliable statement is the
bounded-block experiment: solve the column-generation LP with the 21 first-moment
multipliers restricted to |L| <= lb and report the optimum as a function of lb.
If every optimum is <= the L = 0 value, opening the block is a brake for this family.
"""
import numpy as np, json, math, sys, time
from pathlib import Path
from scipy.optimize import linprog
from scipy import sparse

P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
R = 19/50
pi = math.pi
N, NR, NA = 36, 12, 96


def assemble(start=0, span=4):
    """lead rows + 21 first-moment columns (verified against the lead in f3/f4)"""
    row = json.loads((LEAD/f'q0_closure_dual_{start}_{span}.json').read_text())
    z0 = np.array(row['z'])
    faces = [tuple(f) for f in row['faces']]
    edges = [tuple(e) for e in row['edges']]
    ei = {e: k for k, e in enumerate(edges)}
    ne, nf = len(edges), len(faces)
    side0, rr0, kap0, lam0, eta0, lin0, cl0 = 11, 32, 50, 71, 72, 73, 112
    nz0, nz = 121, 142
    adj = {e: [(t, next(k for k in f if k not in e))
               for t, f in enumerate(faces) if e[0] in f and e[1] in f] for e in edges}
    sgn = {e: {adj[e][0][0]: 1.0} if len(adj[e]) == 1 else
            {adj[e][0][0]: 1.0, adj[e][1][0]: -1.0} for e in edges}
    base = np.zeros(nz)
    base[0:9] = pi; base[9:11] = 2*pi; base[kap0:lam0] = pi; base[lam0] = -2*pi
    base[cl0:cl0+9] = -pi
    facs, sws, rngs = [], [], []
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
            M[:, 121+ee] += sg*np.sin(ang[:, k])
        facs.append((f'face{t}', v, M))
    for bi in range(9):
        i, j = bi, (bi+1) % 9; e = tuple(sorted((i, j))); ee = ei[e]
        b = np.tile(np.linspace(0, pi/2, 4*N+1), 31)
        x = np.repeat(np.linspace(0, 1, 31)**2, 4*N+1)
        v = R*R*x*np.sin(2*b)/2
        M = np.zeros((len(v), nz))
        M[:, cl0+bi] += 2*b; M[:, i] += b; M[:, j] += b; M[:, kap0+ee] -= b
        M[:, side0+ee] -= x*np.sin(b)**2; M[:, lin0+ee] -= np.sqrt(x)*np.sin(b)
        M[:, rr0+2*i+1] += x; M[:, rr0+2*j] += x
        M[:, lin0+21+2*i+1] += np.sqrt(x); M[:, lin0+21+2*j] += np.sqrt(x)
        M[:, 121+ee] -= np.sin(b)
        sws.append((f'switch{bi}', v, M))
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
        kr = ei[tuple(sorted((i, (i+1) % 9)))]
        kl = ei[tuple(sorted(((i-1) % 9, i)))]
        M[:, 121+kr] = -u
        M[:, 121+kl] = -v
        rngs.append((f'ring{i}', S, M))
    return row, z0, base, facs, sws, rngs


def bounds_lead(nz0, lbL, freeL=True):
    b = [(-3, 3)]*11 + [(-3, 3)]*21 + [(-3, 3)]*18 + [(0, 3)]*21 + [(-3, 3), (0, 0)]
    b += [(-3, 3)]*21 + [(-3, 3)]*18 + [(-3, 3)]*9
    assert len(b) == nz0
    return b + [(None, None)]*21 if freeL else b + [(-lbL, lbL)]*21


def solve(pr, lbL, freeL=True, maxiter=120, tol=1e-11, verbose=False):
    row, z0, base, facs, sws, rngs = pr
    nz = 142; nb = len(facs)+len(sws)+len(rngs)
    bnds = bounds_lead(121, lbL, freeL)
    rows, rhs, pick = [], [], {}
    facs_l = facs+sws+rngs
    for k, (name, v, M) in enumerate(facs_l):
        j = int(np.argmax(v)); pick[k] = j
        rows.append(np.r_[M[j], -np.eye(nb)[k]]); rhs.append(-float(v[j]))
    c = np.r_[base, np.ones(nb)]
    best = np.inf
    for it in range(maxiter):
        sol = linprog(c, A_ub=np.array(rows), b_ub=np.array(rhs),
                      bounds=bnds+[(0, None)]*nb, method='highs')
        if not sol.success:
            return None, None, 'LPFAIL'
        z = sol.x[:nz]; ub = float(base @ z); nnew = 0
        for k, (name, v, M) in enumerate(facs_l):
            vals = v+M@z; j = int(np.argmax(vals)); ub += float(vals[j])
            if j != pick[k]:
                pick[k] = j
                rows.append(np.r_[M[j], -np.eye(nb)[k]]); rhs.append(-float(v[j])); nnew += 1
        if ub < best:
            best = ub
        if verbose and it % 20 == 0:
            print(f'    it{it} lp={sol.fun:.9f} ub={ub:.9f} cuts={len(rows)}', flush=True)
        if abs(ub-sol.fun) < tol:
            break
    return best, z, 'ok'


if __name__ == '__main__':
    t0 = time.time()
    pr = assemble()
    print('assembled; baseline check (L fixed to 0):')
    row, z0, base, facs, sws, rngs = pr
    z = np.r_[z0, np.zeros(21)]
    ub = float(base @ z)
    for name, v, M in facs+sws+rngs:
        ub += float(np.max(v+M@z))
    print(f'   L=0 bound = {ub:.9f}   lead = {row["sample_upper"]:.9f}')
    print(f'\n{"|L| box":>10s} {"LP optimum":>16s} {"vs L=0":>14s}')
    base_val = ub
    for lb in [0.0, 0.1, 0.25, 0.5, 1.0, 2.0]:
        best, bz, st = solve(pr, lb, freeL=(lb > 0))
        if best is None:
            print(f'{lb:10.2f}   {st}'); continue
        print(f'{lb:10.2f} {best:16.9f} {best-base_val:+14.6f}')
        np.save(OUT/f'zL_{lb}.npy', bz)
    print(f'elapsed {time.time()-t0:.1f}s')
