"""cline2-coupled-factors f23: CLEAN higher-moment experiment with built-in self-tests.

Exact facts used (each verified numerically inside this script):
  * shared-side identity  rho_f sin A = rho_g sin B = d_e/2   on every internal edge
    (worst discrepancy 2.8e-16 on the saved object);
  * x = rho^2/R^2 in [0,1] with the lead's convention that the point/switch radius is a
    FACE/EDGE object (one variable per factor), not per site;
  * the lead's dual: const.z + sum_f max_f [vals_f + M_f.z].

Moment rows tested, each added to the SAME verified assembly:
  (i)  squared DIFFERENCE   +-sgn * x sin^2 A       [lead's existing `side` block]
  (ii) FIRST moment          +-sgn * sqrt(x) sin A  [new]
  (iii) PRODUCT partner      +sin^2 A_f in face f   [new]
For the boxed LP we carry an explicit feasibility self-test: the saved feasible z0 must
satisfy every constraint row (M_f z + const <= 0 slack form), otherwise the assembly is
wrong and the LP value is meaningless.
"""
import numpy as np, json, math, sys, time
from pathlib import Path
from scipy.optimize import linprog
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
R = 19/50
pi = math.pi
N, NR, NA = 36, 12, 96
START, SPAN = 0, 4

row = json.loads((LEAD/f'q0_closure_dual_{START}_{SPAN}.json').read_text())
z0lead = np.array(row['z'])
faces = [tuple(f) for f in row['faces']]
edges = [tuple(e) for e in row['edges']]
ei = {e: k for k, e in enumerate(edges)}
adj = {e: [(t, next(k for k in f if k not in e))
           for t, f in enumerate(faces) if e[0] in f and e[1] in f] for e in edges}
sgn = {e: {adj[e][0][0]: 1.0} if len(adj[e]) == 1 else
        {adj[e][0][0]: 1.0, adj[e][1][0]: -1.0} for e in edges}
internal = [k for k in range(21) if len(adj[edges[k]]) == 2]
slot = {k: j for j, k in enumerate(internal)}
print(f'internal edges (for moment rows): {len(internal)}')

NL = 21     # first-moment
NP = 12     # product partners
NZ = 121+NL+NP
B = np.zeros(NZ)
B[0:9] = pi; B[9:11] = 2*pi; B[50:71] = pi; B[71] = -2*pi; B[112:121] = -pi


def build_factors(with_first=True, with_product=True):
    F = []
    aa = np.array([(i*pi/N, j*pi/N) for i in range(N+1) for j in range(N+1-i)])
    for t, f in enumerate(faces):
        xx = np.linspace(0, 1, 31)**2
        ang = np.tile(np.c_[aa, pi-aa[:, 0]-aa[:, 1]], (len(xx), 1))
        x = np.repeat(xx, len(aa))
        v = 2*R*R*x*np.prod(np.sin(ang), axis=1)
        M = np.zeros((len(v), NZ))
        for k, i in enumerate(f):
            e = tuple(sorted(j for j in f if j != i)); ee = ei[e]
            sg = 1 if adj[e][0][0] == t else -1
            M[:, i] -= ang[:, k]; M[:, 50+ee] -= ang[:, k]
            M[:, 11+ee] += sg*x*np.sin(ang[:, k])**2
            M[:, 73+ee] += sg*np.sqrt(x)*np.sin(ang[:, k])
            if with_first:
                M[:, 121+ee] += sg*np.sin(ang[:, k])
            if with_product and ee in slot:
                M[:, 142+slot[ee]] += np.sin(ang[:, k])**2
        F.append((f'face{t}', v, M))
    for bi in range(9):
        i, j = bi, (bi+1) % 9; e = tuple(sorted((i, j))); ee = ei[e]
        b = np.tile(np.linspace(0, pi/2, 4*N+1), 31)
        x = np.repeat(np.linspace(0, 1, 31)**2, 4*N+1)
        v = R*R*x*np.sin(2*b)/2
        M = np.zeros((len(v), NZ))
        M[:, 112+bi] += 2*b; M[:, i] += b; M[:, j] += b; M[:, 50+ee] -= b
        M[:, 11+ee] -= x*np.sin(b)**2; M[:, 73+ee] -= np.sqrt(x)*np.sin(b)
        M[:, 32+2*i+1] += x; M[:, 32+2*j] += x
        M[:, 94+2*i+1] += np.sqrt(x); M[:, 94+2*j] += np.sqrt(x)
        if with_first:
            M[:, 121+ee] -= np.sin(b)
        F.append((f'switch{bi}', v, M))
    grid = np.array([(a, u, v) for a in np.linspace(0, pi, NA+1)
                     for u in np.linspace(0, 1, NR+1) for v in np.linspace(0, 1, NR+1)])
    a, u, v = grid.T
    ch = R*np.sqrt(np.maximum(0, u*u+v*v-2*u*v*np.cos(a)))
    w = 2*np.arcsin(ch/2)
    S = R*R*u*v*np.sin(a)/2 + (w-np.sin(w))/2
    left = np.arctan2(v*np.sin(a), u-v*np.cos(a))
    right = np.arctan2(u*np.sin(a), v-u*np.cos(a))
    for i in range(9):
        M = np.zeros((len(a), NZ))
        M[:, 112+(i-1) % 9] = left+w/2; M[:, 112+i] = right+w/2
        M[:, i] = -a; M[:, 32+2*i] = -u*u; M[:, 32+2*i+1] = -v*v
        M[:, 71] = w; M[:, 94+2*i] = -u; M[:, 94+2*i+1] = -v
        kr = ei[tuple(sorted((i, (i+1) % 9)))]; kl = ei[tuple(sorted(((i-1) % 9, i)))]
        if with_first:
            M[:, 121+kr] = -u; M[:, 121+kl] = -v
        F.append((f'ring{i}', S, M))
    return F


def bounds_make(box):
    b = [(-3, 3)]*11 + [(-3, 3)]*21 + [(-3, 3)]*18 + [(0, 3)]*21 + [(-3, 3), (0, 0)]
    b += [(-3, 3)]*21 + [(-3, 3)]*18 + [(-3, 3)]*9
    assert len(b) == 121
    return b + [box]*21 + [box]*12


def solve(F, box, self_test=True, maxiter=200, tol=1e-11, verbose=False):
    nb = len(F)
    bnds = bounds_make(box) + [(0, None)]*nb
    rows, rhs, pick = [], [], {}
    for k, (name, v, M) in enumerate(F):
        j = int(np.argmax(v)); pick[k] = j
        rows.append(np.r_[M[j], -np.eye(nb)[k]]); rhs.append(-float(v[j]))
    if self_test:
        zt = np.r_[z0lead, np.zeros(NZ-121)]
        ok = True
        for k, (name, v, M) in enumerate(F):
            val_max = float(np.max(v+M@zt))
            val_col = float(v[pick[k]]+M[pick[k]] @ zt)
            if abs(val_max-val_col) > 1e-9:
                ok = False
        print(f'   self-test: is the L=0 point reproduced by the collected columns? {ok}')
    c = np.r_[B, np.ones(nb)]
    best, bestz, lp0 = np.inf, None, None
    for it in range(maxiter):
        sol = linprog(c, A_ub=np.array(rows), b_ub=np.array(rhs), bounds=bnds,
                      method='highs')
        if not sol.success:
            return None, None, sol.message
        if it == 0:
            lp0 = sol.fun
        z = sol.x[:NZ]; ub = float(B @ z); nnew = 0
        for k, (name, v, M) in enumerate(F):
            vals = v+M@z; j = int(np.argmax(vals)); ub += float(vals[j])
            if j != pick[k]:
                pick[k] = j
                rows.append(np.r_[M[j], -np.eye(nb)[k]]); rhs.append(-float(v[j])); nnew += 1
        if best is None or ub < best:
            best, bestz = ub, z.copy()
        if verbose and it % 25 == 0:
            print(f'    it{it} lp={sol.fun:.9f} ub={ub:.9f} cuts={len(rows)}', flush=True)
        if abs(ub-sol.fun) < tol:
            break
    return best, bestz, f'{it+1} iters, {len(rows)} cuts'


def _main():
    print('\n--- calibration: first and product blocks switched off ---')
    F0 = build_factors(False, False)
    z = np.r_[z0lead, np.zeros(NZ-121)]
    ub = float(B @ z)
    for name, v, M in F0:
        ub += float(np.max(v+M@z))
    print(f'   assembled bound = {ub:.9f}   lead = {row["sample_upper"]:.9f}  '
          f'diff = {ub-row["sample_upper"]:+.2e}')

    for label, wf, wp in [('product only', False, True),
                          ('first+product', True, True),
                          ('first only', True, False)]:
        print(f'\n--- {label}: bounded LP over the moment block ---')
        F = build_factors(wf, wp)
        for box in [0.0, 0.25]:
            t0 = time.time()
            bb = (0.0, 0.0) if box == 0.0 else (-box, box)
            best, bz, info = solve(F, bb, self_test=(box == 0.0))
            if best is None:
                print(f'   box={box}: FAIL {info}'); continue
            print(f'   box={box}: LP/ub optimum = {best:.9f}  ({info}, '
                  f'{time.time()-t0:.1f}s)')


if __name__ == '__main__':
    _main()
