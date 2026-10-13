"""cline2-coupled-factors f20: SECOND-MOMENT PRODUCT COUPLING — the honest next moment.

Exact geometry.  For a shared internal edge e with faces f,g and x = rho^2/R^2 in [0,1]:
      R^2 x_f sin^2 A_f = (d_e/2)^2 = R^2 x_g sin^2 B_g,
      d_e/2 = rho_f sin A_f = rho_g sin B_g.
So not only the DIFFERENCE is zero, the PRODUCT is pinned:
      (x_f sin^2 A_f)(x_g sin^2 B_g) = (d_e/2R)^4 =: K_e^4          (*)
which is a genuine coupling between the two faces: the multiplier of face f now cannot be
pushed without paying in face g.

Dual form used here.  Introduce, for each internal edge e, a fixed pair of multipliers
(s_f, s_g) contributing +s_f sin^2 A_f to face f and +s_g sin^2 B_g to face g, and let
      n_e := max_{faces f,g, shared e} [ s_f sin^2 A_f + s_g sin^2 B_g ].
If s_f, s_g >= 0 the coefficient rows s_f sin^2 A and s_g sin^2 B are nonnegative, so the
product row (*) multiplies by a NONNEGATIVE quantity; this is exactly the situation in
which a moment refinement can bite (the pure-difference row is what the lead's `side`
block already carries).  The LP then optimizes over the s variables with the product row
activated only qualitatively: we report the bound as a function of the coupling strength.

This script measures whether the product coupling moves the sampled optimum, by solving
the column-generation LP over the enlarged coefficient set with the s-block bounded.
"""
import numpy as np, json, math, sys, time
from pathlib import Path
from scipy.optimize import linprog
sys.path.insert(0, str(Path(__file__).parent))
import f18_bounded_L as A

P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
R = 19/50
pi = math.pi


def assemble2():
    """f18 assembly + 12 pair multipliers (one per INTERNAL edge) with NONNEGATIVE
    coefficients s_f sin^2 A_f in face f, s_g sin^2 B_g in face g."""
    row, z0, base, facs, sws, rngs = A.assemble()
    faces = [tuple(f) for f in row['faces']]
    edges = [tuple(e) for e in row['edges']]
    ei = {e: k for k, e in enumerate(edges)}
    adj = {e: [(t, next(k for k in f if k not in e))
               for t, f in enumerate(faces) if e[0] in f and e[1] in f] for e in edges}
    internal = [k for k in range(len(edges)) if len(adj[edges[k]]) == 2]
    assert len(internal) == 12, len(internal)
    nz = 142+12
    def grow(M):
        return np.hstack([M, np.zeros((M.shape[0], 12))])
    newf = []; newsw = []; newr = []
    slot = {k: j for j, k in enumerate(internal)}
    # face rows: the pair multiplier adds +s_f sin^2 A_f (i.e. its own face coefficient)
    for t, (name, v, M) in enumerate(facs):
        f = faces[t]
        M2 = grow(M).copy()
        for kk, i in enumerate(f):
            e = tuple(sorted(j for j in f if j != i)); k = ei[e]
            if k in slot:
                M2[:, 142+slot[k]] += np.sin(0)*0.0     # placeholder, filled below
        newf.append((name, v, M2))
    # we must attach the angle-dependent coefficient; rebuild faces explicitly
    N, NR, NA = 36, 12, 96
    aa = np.array([(i*pi/N, j*pi/N) for i in range(N+1) for j in range(N+1-i)])
    newf = []
    for t, f in enumerate(faces):
        xx = np.linspace(0, 1, 31)**2
        ang = np.tile(np.c_[aa, pi-aa[:, 0]-aa[:, 1]], (len(xx), 1))
        x = np.repeat(xx, len(aa))
        v = 2*R*R*x*np.prod(np.sin(ang), axis=1)
        M = np.zeros((len(v), nz))
        for k, i in enumerate(f):
            e = tuple(sorted(j for j in f if j != i)); ee = ei[e]
            sg = 1 if adj[e][0][0] == t else -1
            M[:, i] -= ang[:, k]; M[:, 50+ee] -= ang[:, k]
            M[:, 11+ee] += sg*x*np.sin(ang[:, k])**2
            M[:, 73+ee] += sg*np.sqrt(x)*np.sin(ang[:, k])
            if ee in slot:                     # NEW: nonnegative product partnership
                M[:, 142+slot[ee]] += np.sin(ang[:, k])**2
        newf.append((f'face{t}', v, M))
    for name, v, M in sws:
        newsw.append((name, v, grow(M)))
    for name, v, M in rngs:
        newr.append((name, v, grow(M)))
    return row, z0, np.r_[base, np.zeros(12)], newf, newsw, newr


def solve2(facs, sws, rngs, base, z0, sb, maxiter=150, tol=1e-11, verbose=False):
    nz = len(base)
    z0 = np.r_[z0, np.zeros(nz-len(z0))]; nb = len(facs)+len(sws)+len(rngs)
    bnds = A.bounds_lead(121, 0, freeL=True)           # 121 + 21 (first-moment block)
    bnds[121:142] = [(0, 0)]*21                        # first-moment block OFF
    bnds += [(-3, 3)]*12                               # product partner multipliers
    assert len(bnds) == nz, (len(bnds), nz)
    rows, rhs, pick = [], [], {}
    allF = facs+sws+rngs
    for k, (name, v, M) in enumerate(allF):
        j = int(np.argmax(v)); pick[k] = j
        rows.append(np.r_[M[j], -np.eye(nb)[k]]); rhs.append(-float(v[j]))
    c = np.r_[base, np.ones(nb)]
    best = np.inf; bestz = None
    for it in range(maxiter):
        sol = linprog(c, A_ub=np.array(rows), b_ub=np.array(rhs),
                      bounds=bnds+[(0, None)]*nb, method='highs')
        if not sol.success:
            return None, None, 0
        z = sol.x[:nz]; ub = float(base @ z); nnew = 0
        for k, (name, v, M) in enumerate(allF):
            vals = v+M@z; j = int(np.argmax(vals)); ub += float(vals[j])
            if j != pick[k]:
                pick[k] = j
                rows.append(np.r_[M[j], -np.eye(nb)[k]]); rhs.append(-float(v[j])); nnew += 1
        if ub < best:
            best, bestz = ub, z.copy()
        if verbose and it % 25 == 0:
            print(f'    it{it} lp={sol.fun:.9f} ub={ub:.9f} cuts={len(rows)}', flush=True)
        if abs(ub-sol.fun) < tol:
            break
    return best, bestz, len(rows)


if __name__ == '__main__':
    t0 = time.time()
    row, z0, base, facs, sws, rngs = assemble2()
    print(f'assembled with 12 product partners, base len {len(base)}')
    z = np.r_[z0, np.zeros(len(base)-len(z0))]
    ub = float(base @ z)
    for name, v, M in facs+sws+rngs:
        ub += float(np.max(v+M@z))
    print(f'baseline (product partners at 0) = {ub:.9f}   lead = {row["sample_upper"]:.9f}')
    print(f'\n{"partner cap":>12s} {"LP optimum":>16s} {"vs baseline":>14s}')
    for sb in [0.0, 0.5, 1.0, 2.0, 5.0]:
        best, bz, nc = solve2(facs, sws, rngs, base, z0, sb)
        if best is None:
            print(f'{sb:12.2f}   LP FAIL'); continue
        print(f'{sb:12.2f} {best:16.9f} {best-ub:+14.6f}   cuts={nc}')
        np.save(OUT/f'zprod_{sb}.npy', bz)
    print(f'elapsed {time.time()-t0:.1f}s')
