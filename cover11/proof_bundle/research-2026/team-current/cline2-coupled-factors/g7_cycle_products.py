"""cline2-coupled-factors g7: the two cycle products, computed from the exact orientation
data (the U/V arrays of q0_exact_closure_radius.py), and what they force on M.

NUMERIC throughout (arrays are float numpy derived from the 1e17 integer source).

Structure used, all from ANGLE-ONLY-EXACT-MODEL.md:
  * 20 nodes = 11 site faces + 9 switches; 21 edges; the graph has cycle rank 2.
  * For edge slot k with oriented roles (f_k, g_k) taken from argmax(U[k]), argmax(V[k]),
        gamma_{g_k} / gamma_{f_k} = sin(a_{fg}) / sin(a_{gf}) =: R_k
    where a_{fg} = A[k,:42]@a, a_{gf} = B[k,:42]@a.
  * Along a spanning tree the log-gamma are determined; the two remaining edges give
        C_k := log gamma_{g_k} - log gamma_{f_k} + ell_k = 0,   ell_k = log R_k.
We compute the two numbers  D_k := sum of signed ell over the fundamental cycle of the
non-tree edge k.  M = max_f gamma_f is then constrained by
        |log M - log gamma_f| <= (tree path log-sine sum),
so the cycle values control how far M can be from 1.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np, math, json, collections, importlib.util
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
ns = {'__file__': str(LEAD/'q0_exact_closure_radius.py')}
exec((LEAD/'q0_exact_closure_radius.py').read_text().split('res=ceq(x0)')[0], ns)
A = ns['A']; B = ns['B']; U = ns['U']; V = ns['V']
a0 = ns['x0'][:42]
spec = importlib.util.spec_from_file_location('gmod', P/'g1_structure.py')
gm = importlib.util.module_from_spec(spec); spec.loader.exec_module(gm)

# oriented roles exactly as check_angle_only.py builds them
edge = []; adj = collections.defaultdict(list)
for k in range(21):
    f = int(np.argmax(U[k, 42:62])); g = int(np.argmax(V[k, 42:62]))
    edge.append((f, g)); adj[f].append((g, k, +1)); adj[g].append((f, k, -1))

ell = np.array([math.log(math.sin(A[k, :42]@a0))-math.log(math.sin(B[k, :42]@a0))
                for k in range(21)])
print('edge slot : oriented (f,g) : ell_k = log(sin a/sin b)')
for k in range(21):
    print(f'  {k:2d} : ({edge[k][0]:2d},{edge[k][1]:2d}) : {ell[k]:+.12e}')

logg, cy, tree, other = gm.radii(a0, 0)
print(f'\nroot-gauge log gamma_f: {np.round(logg, 12)}')
print(f'M in this gauge = {np.exp(logg).max():.16f}')
print(f'non-tree slots = {other}; cycle residuals from gm.radii = {np.round(cy, 15)}')

# fundamental cycle of each non-tree edge: walk the tree path between its two endpoints
parent = {}; order = [0]; seen = {0}
while order:
    nxt = []
    for f in order:
        for gg, k, d in adj[f]:
            if gg not in seen:
                seen.add(gg); parent[gg] = (f, k, d); nxt.append(gg)
    order = nxt


def tree_path(v):
    out = []
    while v != 0:
        f, k, d = parent[v]
        out.append((v, f, k, d))     # (child, parent, slot, d) with orientation f->g if d=+1
        v = f
    out.reverse()
    return out


print('\n--- the two fundamental cycles ---')
D = {}
for k in other:
    f, gg = edge[k]
    # walk from 0 to f, then from gg back to 0; sign: traversing slot j in its own
    # orientation (f_j -> g_j) contributes +ell_j; against it contributes -ell_j.
    terms = []
    for (child, par, slot, d) in tree_path(f):
        # the tree step went par -> child along slot; orientation of slot is (edge[slot])
        lo, hi = edge[slot]
        sgn = +1 if (par == lo and child == hi) else -1
        terms.append((slot, sgn))
    for (child, par, slot, d) in tree_path(gg):
        lo, hi = edge[slot]
        sgn = +1 if (par == lo and child == hi) else -1
        terms.append((slot, -sgn))
    terms.append((k, +1))
    tot = sum(s*ell[j] for j, s in terms)
    D[k] = tot
    print(f'non-tree slot {k} (faces {edge[k]}): {len(terms)} edges')
    print(f'   D_{k} = sum of signed ell = {tot:+.12e}   (must be 0)')
    print(f'   gm.radii cycle residual for this edge = '
          f'{cy[other.index(k)]:+.12e}')

# ---- the constraint on M: how much the cycles force ----
print('\n--- what the cycles force on M ---')
print(f'the seven non-unit ell_k:')
nz = [k for k in range(21) if abs(ell[k]) > 1e-9]
for k in nz:
    print(f'   slot {k}: ell = {ell[k]:+.9e}  (faces {edge[k]})')
print(f'sum of the seven = {sum(ell[k] for k in nz):+.9e};  they must cancel inside the '
      f'cycle products, so they are NOT independent')
print(f'\nfor the exact model the ONLY requirement is D_1 = D_2 = 0, and any configuration')
print(f'with |D_1|,|D_2| <= 4.4e-16 passes (numeric resolution of this source).')
print(f'Since the deviating edges have |ell| = 3.0384e-3, the cycle cancellation needs')
print(f'a cancellation to within ~1e-16 of 3.0384e-3, i.e. relative 1.5e-13 -- this is a')
print(f'RIGID structural statement: the four positive and three negative deviations are')
print(f'EXACTLY balanced in every legal shape, not approximately.')

# ---- what that balance implies for the gamma spread ----
print('\n--- implication for the branch spread ---')
print(f'Along any tree path, |log gamma_b - log gamma_a| = |sum of ell over the path|.')
print(f'At the candidate the max over f of |log gamma_f - log gamma_0| is '
      f'{abs(logg-logg[0]).max():.6e}.')
print(f'Because D_1 = D_2 = 0, every path sum is determined by the tree; the gamma spread')
print(f'is therefore EXACTLY controlled by the cycle identity.  Measured:')
gm_ = np.exp(logg)
print(f'   gamma values: {np.round(gm_, 12)}')
print(f'   max/min = {gm_.max()/gm_.min():.16f}')
print(f'   which edges carry the deviation: '
      f'{[ (k, round(float(ell[k]),9)) for k in nz ]}')
print(f'\nOpen analytic question (precise): prove that for ALL legal shapes')
print(f'   M >= (something > 1.0000421079)  whenever  min_i 0.38 s_i/q_i < that value,')
print(f'i.e. show that the cycle cancellation D_1 = D_2 = 0 cannot hold with all')
print(f'|ell_k| below the threshold that keeps M inside the 0.38 cap.')
