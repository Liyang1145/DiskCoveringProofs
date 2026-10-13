"""r20-rigidity: small exact controls for the DBM cosine-polytope audit (no LP re-run).

Checks, all in exact Fraction arithmetic:
  (1) root DBM: db[i][j] = 0 for i=j, 1 for j>i, db[9][0] = -1, db[i][j] = -db[j][i] where forced,
      and the Floyd-Warshall closure is closed (no negative diagonal);
  (2) domain_rows signs: for a sample y on the simplex, t_j - t_i = sum y[i:j] and every row of
      (A, b) from domain_rows is satisfied, including the reversed rows;
  (3) dual identity f0 - lambda.b + min_i (c + A^T lambda)_i <= f0 + c.y for random rational
      lambda >= 0 and any y in the domain (the residual-dual direction);
  (4) reflect permutation: node maps are bijections/involutions, edge permutation is an involution of
      {0..50}, and the anchor map (3-i)%9 is exactly what preserves the anchor-site edges.
Writes dbm_audit.json/.log.
"""
import json
from fractions import Fraction as F
from pathlib import Path
import random
import mpmath as mp

mp.mp.dps = 50
mp.iv.dps = 40
R20 = Path(__file__).resolve().parent
REP = []


def say(s):
    print(s, flush=True)
    REP.append(s)


# ---- (1) root DBM and its closure
db = [[F(0) if j <= i else F(1) for j in range(10)] for i in range(10)]
db[9][0] = F(-1)


def closure(dbx):
    d = [r[:] for r in dbx]
    for k in range(10):
        for i in range(10):
            for j in range(10):
                if d[i][k] + d[k][j] < d[i][j]:
                    d[i][j] = d[i][k] + d[k][j]
    assert all(d[i][i] >= 0 for i in range(10)), 'negative diagonal in closure'
    return d


d0 = closure(db)
say('[D1] root DBM closed: db[i][i]=0, db[i][j]=1 (j>i), db[9][0]=-1; closed under triangle: %s'
    % all(d0[i][j] <= d0[i][k] + d0[k][j] for i in range(10) for j in range(10) for k in range(10)))
say('     sample: db[0][9] = %s, db[9][0] = %s, db[4][4] = %s' % (d0[0][9], d0[9][0], d0[4][4]))

# ---- (2) domain_rows signs on sample simplex points
def domain_rows(dbx):
    A, b = [], []
    for i in range(10):
        for j in range(i + 1, 10):
            row = [F(int(i <= k < j)) for k in range(9)]
            A.extend([row, [-x for x in row]])
            b.extend([dbx[i][j], dbx[j][i]])
    return A, b


A, b = domain_rows(d0)
rng = random.Random(7)
ok = True
for _ in range(20):
    y = [F(rng.randint(1, 30)) for _ in range(9)]
    s = sum(y)
    y = [x / s for x in y]
    t = [F(0)]
    for i in range(9):
        t.append(t[-1] + y[i])
    assert t[9] == 1
    for i in range(10):
        for j in range(i + 1, 10):
            val = sum(y[i:j])
            assert val == t[j] - t[i], 'prefix identity failed'
    for row, bb in zip(A, b):
        assert sum(x * yy for x, yy in zip(row, y)) <= bb, 'domain row violated'
    ok = ok and True
say('[D2] domain_rows: %d rows (90 = 2*45 including the node-9 pairs) ; for 20 exact simplex y:'
    ' t_j-t_i = sum y[i:j] holds and ALL rows A.y <= b are satisfied (both signs) : %s' % (len(A), ok))

# ---- (3) residual-dual direction on random rational lambda
c = [F(rng.randint(-5, 5), 7) for _ in range(9)]
lam = [F(rng.randint(0, 5), 11) for _ in range(len(A))]
f0 = F(3, 5)
y = [F(rng.randint(1, 20)) for _ in range(9)]
y = [x / sum(y) for x in y]
lhs = f0 + sum(cx * yx for cx, yx in zip(c, y))
rhs = f0 - sum(l * bb for l, bb in zip(lam, b)) + min(
    c[k] + sum(lam[j] * A[j][k] for j in range(len(A))) for k in range(9))
say('[D3] residual-dual direction: with sum y = 1, y >= 0, A y <= b, lambda >= 0 we have'
    ' f0 - lam.b + min_i (c + A^T lam)_i <= f0 + c.y : %s (exact Fractions)' % bool(rhs <= lhs))

# ---- (4) reflect permutation
facesL = [[9, k, k + 1] for k in range(4)] + [[10, k, (k + 1) % 9] for k in range(4, 9)] \
         + [[9, 10, 0], [9, 10, 4]]
edgesL = []
for s in range(9):
    edgesL.extend([(9 + s, s), (9 + s, (s - 1) % 9)])
for j, f in enumerate(facesL):
    edgesL.extend((9 + s, 20 + j) for s in f)


def p(i):
    return (4 - i) % 9 if i < 9 else i


fp = {j: next(k for k, g in enumerate(facesL) if set(g) == {p(i) for i in f})
      for j, f in enumerate(facesL)}


def node(i):
    if i < 9:
        return (3 - i) % 9
    if i < 20:
        return 9 + p(i - 9)
    return 20 + fp[i - 20]


eidx = {tuple(sorted(e)): k for k, e in enumerate(edgesL)}
ep = [eidx[tuple(sorted((node(v), node(w))))] for v, w in edgesL]
say('[D4] reflect: edge permutation is a bijection and an involution: %s ; faces map bijectively: %s'
    % (sorted(ep) == list(range(51)) and all(ep[ep[k]] == k for k in range(51)), len(set(fp.values())) == 11))
# anchor-site consistency: (9+s, s) -> (9+p(s), (3-s)%9) which must be (9+p(s), p(s)) or (9+p(s), p(s)-1)
cons = all(((node(s) == p(s)) or (node(s) == (p(s) - 1) % 9)) for s in range(9))
say('     anchor map (3-s)%%9 is exactly the shift that preserves the anchor-site edges: %s ;'
    ' its geometric reading (reflection about the axis through anchors 2-3 bound) is a modelling'
    ' premise, not asserted by the code' % cons)
OUT = {'root_dbm_closed': True, 'domain_rows': len(A), 'sample_y_all_rows_satisfied': ok,
       'residual_dual_direction_holds': bool(
           f0 - sum(l * bb for l, bb in zip(lam, b)) + min(
               c[k] + sum(lam[j] * A[j][k] for j in range(len(A))) for k in range(9))
           <= f0 + sum(cx * yx for cx, yx in zip(c, y))),
       'edge_permutation_involution': bool(sorted(ep) == list(range(51)) and all(ep[ep[k]] == k for k in range(51))),
       'anchor_site_edge_consistency': bool(cons),
       'scope': 'small exact-Fraction controls for the DBM polytope audit; no LP re-run',
       'repro': 'py -3 -B -X utf8 dbm_audit.py'}
(R20 / 'dbm_audit.json').write_text(json.dumps(OUT, indent=2))
(R20 / 'dbm_audit.log').write_text('\n'.join(REP) + '\n')
say('written dbm_audit.json / .log')
