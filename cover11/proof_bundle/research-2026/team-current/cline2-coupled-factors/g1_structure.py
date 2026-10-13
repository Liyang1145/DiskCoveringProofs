"""cline2-coupled-factors g1: structural readout of the C839 angle-only model.

Purpose: obtain the exact quantities needed for a GLOBAL analytic lower bound on
    log R_shape = max_{f=0..19} log gamma_f + log(q_0/ell_0),
without any grid/sampling.  Computes at the candidate:
  * the 42 angles and their admissibility margins,
  * the 20 branch values gamma_f, the max branch and the spread log(max/min),
  * the product identity  sum_{faces} log sin(angles)  (Cagnoli-type structure),
  * the log-sine window bounds over [1/37999, 1] (C840) for the 21 sine-law ratios,
  * the six circle ratios q_i/ell_i and their spread,
  * the derived identity  R_shape = M * q_0/ell_0 = M * sin(b_0)/sin(alpha_0/2)-type form,
so that a subsequent analytic step has exact constants to work with.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np, math, json
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
OUT.mkdir(exist_ok=True)
pi = math.pi

ns = {'__file__': str(LEAD/'q0_exact_closure_radius.py')}
exec((LEAD/'q0_exact_closure_radius.py').read_text().split('res=ceq(x0)')[0], ns)
A, B, U, V = [ns[k] for k in ['A', 'B', 'U', 'V']]
alpha, ac = ns['alpha'], ns['ac']
x0 = ns['x0']

# ---- rebuild the check_angle_only machinery (incidence + shape) ----
import collections
edge = []
adj = collections.defaultdict(list)
for k in range(21):
    f = int(np.argmax(U[k, 42:62])); g = int(np.argmax(V[k, 42:62]))
    edge.append((f, g)); adj[f].append((g, k, 1)); adj[g].append((f, k, -1))
assert len(edge) == 21 and len(adj) == 20
Alt = np.array([[(-1)**((j-i) % 9) for j in range(9)] for i in range(9)])


def radii(a, root=0):
    ls = np.log(np.sin(A[:, :42]@a))-np.log(np.sin(B[:, :42]@a))
    logg = np.zeros(20); seen = {root}; todo = [root]; tree = []
    for f in todo:
        for g, k, d in adj[f]:
            if g not in seen:
                seen.add(g); todo.append(g); tree.append(k); logg[g] = logg[f]+d*ls[k]
    other = sorted(set(range(21))-set(tree))
    cy = np.array([logg[f]-logg[g]+ls[k] for k, (f, g) in enumerate(edge)])[other]
    return logg, cy, tree, other


def shape(a, root=0):
    logg, cy, tree, other = radii(a, root)
    g = np.exp(logg)
    al = ac+alpha[:, :42]@a
    u = np.roll(g[11:], 1); v = g[11:]
    ell = np.sqrt((u-v)**2+4*u*v*np.sin(al/2)**2)
    L = np.arctan2(v*np.sin(al), u-v*np.cos(al)); T = pi-al-L
    tau = pi-T-np.roll(L, -1)-2*a[33:42]
    w = Alt@tau
    rat = 2*np.sin(w/2)/ell
    return max(g)*rat[0], np.r_[ns['eq'][:, :42]@a-ns['rhs'], cy, rat[1:7]/rat[0]-1], \
        {'logg': logg, 'cycle': cy, 'w': w, 'rat': rat, 'ell': ell, 'alpha': al,
         'tree': tree, 'other': other}


def _main():
    a0 = x0[:42]
    R, con, d = shape(a0)
    print(f'target: R_shape(candidate) = {R:.16f}')
    print(f'constraint residual max = {max(abs(con)):.3e}   (15 constraints: 13 lin + 2 cycle; '
          f'6 ratios are identifications)')
    logg = d['logg']; g = np.exp(logg)
    order = np.argsort(-logg)
    print(f'\nbranch values gamma_f (sorted):')
    for i in order[:21]:
        print(f'   f={i:2d} gamma={g[i]:.10f}  log(gamma/M)={logg[i]-logg.max():+.6f}')
    M = g.max(); fmax = int(np.argmax(logg))
    print(f'M = gamma_{fmax} = {M:.10f};  count within 1e-7 of M: '
          f'{int(sum(abs(logg-logg.max())<1e-7))}')
    print(f'log spread max-min = {logg.max()-logg.min():.6f}  '
          f'(ratio max/min = {math.exp(logg.max()-logg.min()):.6f})')

    # ---- angles and C840 window ----
    ang33 = a0[:33].reshape(11, 3)
    sw = a0[33:42]
    print(f'\nangles: min site angle = {ang33.min():.10f} (sin = {np.sin(ang33.min()):.8f}), '
          f'max = {ang33.max():.10f}')
    print(f'switch half-angles: min {sw.min():.8f}, max {sw.max():.8f}, pi/2 = {pi/2:.8f}')
    print(f'sine bounds over the site angles: min {np.sin(ang33.ravel()).min():.8f}, '
          f'max {np.sin(ang33.ravel()).max():.8f}')

    # ---- Cagnoli-type face product ----
    prod_terms = np.prod(np.sin(ang33), axis=1)
    print(f'\nper-face product of sines (sinA sinB sinC):')
    for t in range(11):
        print(f'   face{t}: {prod_terms[t]:.10f}   sum angles = {ang33[t].sum():.12f}')
    print(f'sum over faces of log(sinA sinB sinC) = {np.log(prod_terms).sum():.10f}')
    print(f'for comparison 11*log(3*sqrt(3)/8) (equilateral max) = '
          f'{11*math.log(3*math.sqrt(3)/8):.10f}')

    # ---- sector quantities ----
    al = d['alpha']; ell = d['ell']; w = d['w']; rat = d['rat']
    print(f'\nsectors: alpha_i, ell_i, w_i, q_i/ell_i')
    for i in range(9):
        print(f'   i={i}: alpha={al[i]:.8f}  ell={ell[i]:.10f}  w={w[i]:.8f}  '
              f'2sin(w/2)/ell={rat[i]:.10f}')
    print(f'ratio spread max/min over i = {rat.max()/rat.min():.10f}')
    print(f'R_shape = M * rat[0] = {M*rat[0]:.16f}')
    print(f'M**2 * q0/ell0 = {M*M*rat[0]:.16f}  (compare 1/38142-ish constants)')

    # ---- window bounds for the log-sine ratios (C840: sin >= 1/37999) ----
    lo = 1/37999
    print(f'\nlog-sine window bound: for sin x in [{lo:.3e}, 1], log sin x in '
          f'[{math.log(lo):.6f}, 0]')
    ls = np.log(np.sin(A[:, :42]@a0))-np.log(np.sin(B[:, :42]@a0))
    print(f'actual 21 window values: min {ls.min():.6f}, max {ls.max():.6f}')
    worst = max(abs(ls.min()), abs(ls.max()))
    print(f'worst |log-sine ratio| = {worst:.6f}; if all windows bounded by W, then along any '
          f'path of k tree edges |log(gamma ratio)| <= k*W')
    # tree depth
    logg_path = logg-logg[0]
    print(f'max |log(gamma_f/gamma_0)| over tree = {np.abs(logg_path).max():.6f} '
          f'(= {np.abs(logg_path).max()/worst:.3f} x W)')

    # ---- product identity for max: forced spread ----
    print(f'\nKEY identity: prod over the 21 sine-law ratios around the two cycle basis '
          f'= prod sin(a)/sin(b) over each cycle')
    for k in d['other']:
        f, gg = edge[k]
        print(f'   non-tree edge {k}: faces ({f},{gg}); its cycle product must be 1')
    print(f'cycle residuals at candidate = {d["cycle"]}')
    json.dump({'R_shape': R, 'M': M, 'fmax': fmax, 'logg': logg.tolist(),
               'alpha': al.tolist(), 'ell': ell.tolist(), 'w': w.tolist(),
               'rat': rat.tolist(), 'cycle': d['cycle'].tolist(),
               'logsin_min': float(ls.min()), 'logsin_max': float(ls.max()),
               'window_lo': lo}, open(OUT/'g1_structure.json', 'w'), indent=1)
    print('\nsaved out/g1_structure.json')


if __name__ == '__main__':
    _main()
