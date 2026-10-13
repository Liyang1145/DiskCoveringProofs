"""cline2-coupled-factors g4: which nonlinear quantity carries the constraint?

Established so far (all NUMERIC: every array below originates from the float numpy arrays
of q0_exact_closure_radius.py, themselves derived from the 1e17 integer source; nothing here
is exact arithmetic):
  * all NINE ratios q_i/ell_i coincide (the six circle equations), and R = M q_i/ell_i for
    every i, with M = max_f gamma_f >= 1.  Hence, multiplying the nine identities,
        R = M * (prod_i q_i / prod_i ell_i)^{1/9}  >=  (prod_i q_i / prod_i ell_i)^{1/9},
    and likewise R = (1/9) sum_i M q_i/ell_i, so a weighted-sum (arithmetic) form is
    equally meaningful -- both follow from the same matching of q_i/ell_i with max gamma.
  * a WEAK particular consequence of the arithmetic form is
        R >= (1/9) sum_i q_i / max_i ell_i  >=  0.343057030948
    using sum_i w_i = 2pi and 2 sin(x/2) >= (2/pi) x.  This does NOT exhaust the arithmetic
    route: any refined additive bound on the q_i or a better control of max_i ell_i is
    untouched by this number, and no exhaustion claim is made.
  * sum_i ell_i = 16.189129609, max_i ell_i = 1.992415025.

What is genuinely still open analytically is the two non-tree cycle products.  They are the
only exact nonlinear equations left after the radius elimination, so this script reports the
exact ratio of the two sides of each cycle product (plus the relation between M and the
per-edge log-sine deviations), which is where any global mechanism has to live.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np, math, json, sys, collections, importlib.util
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
pi = math.pi
ns = {'__file__': str(LEAD/'q0_exact_closure_radius.py')}
exec((LEAD/'q0_exact_closure_radius.py').read_text().split('res=ceq(x0)')[0], ns)
spec = importlib.util.spec_from_file_location('gmod', P/'g1_structure.py')
gm = importlib.util.module_from_spec(spec); spec.loader.exec_module(gm)

A = ns['A']; B = ns['B']; U = ns['U']; V = ns['V']
edge = []; adj = collections.defaultdict(list)
for k in range(21):
    f = int(np.argmax(U[k, 42:62])); g = int(np.argmax(V[k, 42:62]))
    edge.append((f, g)); adj[f].append((g, k, 1)); adj[g].append((f, k, -1))
a0 = ns['x0'][:42]
logg, cy, tree, other = gm.radii(a0, 0)
g = np.exp(logg)
print(f'tree edges: {len(tree)+1} (19 + root), non-tree: {other}')
print(f'non-tree edge slots: {[ (k, edge[k]) for k in other ]}')

# --- which physical angle is the shared side for each edge slot? ---
# A[k]: coefficients of the "a_fg" angle (face f), B[k]: coefficients of the "a_gf" angle.
print('\n--- the two non-tree cycles: their face sequences and the sine law products ---')
for k in other:
    f, gg = edge[k]
    print(f'non-tree edge slot {k}: faces ({f},{gg})')
    print(f'   A[{k}] nonzero angle-support: {np.round(A[k,:42][A[k,:42]!=0], 6)}, '
          f'B[{k}] nonzero: {np.round(B[k,:42][B[k,:42]!=0], 6)}')
    # find the fundamental cycle by walking the tree
    import collections as C

# --- build the tree paths to identify the fundamental cycles ---
parent = {}
order = [0]
seen = {0}
while order:
    nxt = []
    for f in order:
        for gg, k, d in adj[f]:
            if gg not in seen:
                seen.add(gg); parent[gg] = (f, k, d); nxt.append(gg)
    order = nxt
def path_to(v):
    out = []
    while v != 0:
        f, k, d = parent[v]
        out.append((v, f, k, d))
        v = f
    return list(reversed(out))
print('\nfundamental cycles (tree path + non-tree edge):')
for k in other:
    f, gg = edge[k]
    pf = [x[0] for x in path_to(f)]; pg = [x[0] for x in path_to(gg)]
    # common prefix
    i = 0
    while i < min(len(pf), len(pg)) and pf[i] == pg[i]:
        i += 1
    cyc = pf[i-1:][::-1]+pg[i:]
    if pf[i-1] != pf[i-1]:
        pass
    seq = [pf[i-1]]+list(reversed(pg[i:]))+list(reversed(pf[i:]))
    # simpler: reconstruct via paths
    d1 = path_to(f); d2 = path_to(gg)
    up = [x for x in d1 if x[0] not in [y[0] for y in d2]]
    down = [x for x in d2 if x[0] not in [y[0] for y in d1]]
    cyc_faces = [0]+[x[0] for x in d1 if x not in up and x[0] not in []]
    print(f'   edge {k}: faces ({f},{gg}); tree-path face lists '
          f'{pf} and {pg}; LCA at depth {i}')
    # product of sine-law ratios along the cycle must be 1
    prod_terms = []
    v = f
    for (child, par, kk, dd) in path_to(f):
        prod_terms.append((kk, dd))
    for (child, par, kk, dd) in reversed(path_to(gg)):
        prod_terms.append((kk, -dd))
    prod_terms.append((k, 1))
    tot = 0.0
    for (kk, dd) in prod_terms:
        ls = math.log(math.sin(A[kk, :42]@a0))-math.log(math.sin(B[kk, :42]@a0))
        tot += dd*ls
    print(f'   sum of signed log-sine ratios along the cycle = {tot:.3e} '
          f'(must be 0; {len(prod_terms)} edges in the cycle)')

# --- the two cycle products are the ONLY exact nonlinear equations left ---
print('\n--- exact nonlinear content: the two cycle products ---')
print('For a cross-side shared edge the sine-law ratio is sin(a)/sin(b) with a, b the two')
print('opposite angles.  Every such ratio equals gamma_g/gamma_f, so the product around a')
print('cycle is the cycle constraint   prod (sin a / sin b) = 1.')
allr = []
for k in range(21):
    aa = float(A[k, :42]@a0); bb = float(B[k, :42]@a0)
    r = math.sin(aa)/math.sin(bb)
    allr.append(r)
    kind = 'tree' if k not in other else 'NONTREE'
    flag = '' if abs(math.log(r)) < 1e-9 else '   <-- deviates from 1'
    print(f'   slot {k:2d} [{kind:7s}] faces {str(edge[k]):10s} ratio = {r:.12f}'
          f'  log = {math.log(r):+.3e}{flag}')
print(f'\nproduct of ALL 21 ratios = {math.prod(allr):.12f}  '
      f'(= product of the two cycle products, must be 1)')
for k in other:
    f, gg = edge[k]
    prod = 1.0
    for (par, kk, dd) in path_to(f):
        prod *= (math.sin(A[kk, :42]@a0)/math.sin(B[kk, :42]@a0))**dd
    for (par, kk, dd) in reversed(path_to(gg)):
        prod *= (math.sin(A[kk, :42]@a0)/math.sin(B[kk, :42]@a0))**(-dd)
    prod *= math.sin(A[k, :42]@a0)/math.sin(B[k, :42]@a0)
    print(f'cycle through non-tree slot {k}: product = {prod:.15f}  '
          f'(deviation {prod-1:+.3e})')

# --- angular support of A, B: which of the 42 angles appear ---
print('\n--- structure of the sine-law coefficients ---')
nzA = [sorted(set(np.where(A[k, :42] != 0)[0].tolist())) for k in range(21)]
nzB = [sorted(set(np.where(B[k, :42] != 0)[0].tolist())) for k in range(21)]
sizes = collections.Counter([len(nzA[k])+len(nzB[k]) for k in range(21)])
print(f'number of nonzero angle entries per edge slot (A+B): {dict(sizes)}')
print(f'A row sums (should be 0: angle coefficients sum to 0 because a+b+c=pi): '
      f'{sorted(set(np.round(A[:, :42].sum(1), 12)))}')
print(f'B row sums: {sorted(set(np.round(B[:, :42].sum(1), 12)))}')

# --- the exact form: which angle windows appear ---
print('\nangle-window type: for a face-to-face edge, log sin(a_fg) - log sin(a_gf) where')
print('a_fg, a_gf are the two opposite angles.  Check the (face,face) pairs:')
for k in range(21):
    f, gg = edge[k]
    if f < 11 and gg < 11:
        print(f'   slot {k}: faces ({f},{gg}) | A support {nzA[k]} | B support {nzB[k]} | '
              f'a={float(A[k, :42]@a0):.8f}, b={float(B[k, :42]@a0):.8f}, '
              f'sin ratio={math.sin(float(A[k,:42]@a0))/math.sin(float(B[k,:42]@a0)):.10f}')
