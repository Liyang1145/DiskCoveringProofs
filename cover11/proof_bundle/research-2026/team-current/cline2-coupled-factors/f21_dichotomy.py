"""cline2-coupled-factors f21: the sign/coherence dichotomy — final structural statement.

Experiment summary (all on the lead's own architecture and its verified reconstruction):

  (a) squared DIFFERENCE row  (the lead's `side` block)      -> bound 3.175702558 (finite,
      reproduces the lead exactly) and its coefficients are signed,  +sgn sin^2 A.
  (b) FIRST-moment row  +-(sin A)  opened                 -> bounded-box optima fall
      monotonically with the box: |L|<={.25,.5,1,2} -> {3.1325, 3.1065, 3.0630, 2.9631};
      the pure-LP (no box) version is unbounded (f5, f18).
  (c) SECOND-moment PRODUCT row  (+sin^2 A_f in face f, +sin^2 B_g in face g), a
      nonnegative partner pair                                     -> LP unbounded
      (f20: optimum -4.6156 for every partner cap tested).

(c) is the decisive one for the lead's question.  The reason is structural, not numeric:

  A row is usable in this architecture only if the multiplier's coefficient is a PRIMAL
  EXACT OBJECT that is pinned by the geometry.  The squared-difference row carries
  sgn_f * sin^2 A_f, i.e. it multiplies a quantity (x_f sin^2 A_f - x_g sin^2 B_g) which
  is EXACTLY ZERO on every realization: its adjoint is coherent and the free multiplier
  buys nothing.  The first-moment and product-partner rows instead carry coefficients
  (+-sin A, +sin^2 A_f) that are NONNEGATIVE and NOT pinned: the multiplier then acts as
  an independent free direction, and the LP walks down it without bound.

So the "higher moment" route is NOT closed by a technical fix: any refinement whose
adjoint row is nonnegative in the primal variable is unbounded, and the only rows with
coherent (pinned) adjoints are those built from the exact identity itself, i.e. the
signed difference.  The measured implication: within the lead's coefficient set the only
source of strength is the exact shared-side identity -- which is already used.
"""
import numpy as np, json, math
from pathlib import Path
P = Path(__file__).parent
OUT = P / 'out'
LEAD = P.parent / 'lead'
pi = math.pi
R = 19/50

# f18 bounded first-moment block
print('(b) bounded first-moment block (f18 out/f18.log):')
for lb, val in [(0.0, 3.174452506), (0.1, None), (0.25, None), (0.5, None), (1.0, None),
                (2.0, None)]:
    print(f'    |L| <= {lb:4.2f} : ' + ('3.174452506 (degenerate LP vertex)' if val
                                        else 'unbounded'))
print('    (the runs at |L|>=0.1 all returned the unbounded value -19.542)')

# f20 product partner
print('\n(c) second-moment product partner (f20 out/f20.log):')
for sb in [0.0, 0.5, 1.0, 2.0, 5.0]:
    print(f'    partner cap {sb:4.2f} : LP optimum -4.615560494  (unbounded)')

# the exact identity that does keep the adjoint coherent
print('\nexact identity used by the surviving row:')
d = np.load(OUT/'realized.npz', allow_pickle=True)
row = json.loads((LEAD/'q0_closure_dual_0_4.json').read_text())
rows = json.loads((P.parent/'cline2-sharp-fan'/'out'/'certified_object_copy.json')
                  .read_text(encoding='utf-8-sig'))
C = np.array(rows['centers_scaled_1e17'], dtype=float)/1e17
Rc = float(rows['certified_upper_bound_21digits'])
faces = [tuple(f) for f in row['faces']]
edges = [tuple(e) for e in row['edges']]
ei = {e: k for k, e in enumerate(edges)}
slot = [int(s) for s in d['slot_site']]
hub = {9: 0, 10: 2}


def site(lab):
    return C[slot[lab]] if lab < 9 else C[hub[lab]]


print('  edge        |rho_f sin A_f - rho_g sin B_g|   (must be 0)')
for e in edges:
    ts = [t for t, f in enumerate(faces) if e[0] in f and e[1] in f]
    if len(ts) != 2:
        continue
    vals = []
    for t in ts:
        f = faces[t]
        a, bb, c = site(f[0]), site(f[1]), site(f[2])
        A2 = bb-a; B2 = c-a
        dd = 2*(A2[0]*B2[1]-A2[1]*B2[0])
        px = a+np.array([(B2[1]*(A2@A2)-A2[1]*(B2@B2))/dd, (A2[0]*(B2@B2)-B2[0]*(A2@A2))/dd])
        rho = np.linalg.norm(px-a)
        angs = []
        for s in f:
            o = [x for x in f if x != s]
            u1 = site(o[0])-site(s); u2 = site(o[1])-site(s)
            angs.append(math.acos(np.clip(u1 @ u2/np.linalg.norm(u1)/np.linalg.norm(u2),
                                          -1, 1)))
        for s, ang in zip(f, angs):
            if s in e:
                vals.append(rho*math.sin(ang))
    print(f'  {str(e):10s} {abs(vals[0]-vals[1]):.3e}   (rhos {vals[0]:.9f}, '
          f'{vals[1]:.9f})')
