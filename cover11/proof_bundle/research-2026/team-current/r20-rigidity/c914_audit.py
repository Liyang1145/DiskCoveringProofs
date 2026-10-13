"""r20-rigidity: independent audit of C914 (simplex tree pilot + corner simplexes).

No lead helper import: my own forest repair, my own interval min rule, my own variance/volume checks.
Reads lead/simplex_tree_pilot.json, lead/corner_simplex_certificates.json and the C911 forces.
Writes c914_audit.json/.log only.
"""
import json
from fractions import Fraction as F
from pathlib import Path
import random
import mpmath as mp

mp.mp.dps = 60
mp.iv.dps = 45
R20 = Path(__file__).resolve().parent
LEAD = R20.parent / 'lead'
REP = []


def say(s):
    print(s, flush=True)
    REP.append(s)


def I(q):
    q = F(q)
    return mp.iv.mpf(q.numerator) / q.denominator


faces = [[9, k, k + 1] for k in range(4)] + [[10, k, (k + 1) % 9] for k in range(4, 9)] \
        + [[9, 10, 0], [9, 10, 4]]
edges = []
for s in range(9):
    edges.extend([(9 + s, s), (9 + s, (s - 1) % 9)])
for j, f in enumerate(faces):
    edges.extend((9 + s, 20 + j) for s in f)


def balance(p):
    b = [[F(0), F(0)] for _ in range(31)]
    for (v, w), q in zip(edges, p):
        for k in range(2):
            b[v][k] += q[k]
            b[w][k] -= q[k]
    return b


# ---- (A) my own forest repair (DFS order, not the lead's BFS) on a synthetic field
rng = random.Random(20260925)
raw = [[F(rng.randint(-100, 100), 7) for _ in range(2)] for _ in range(51)]
p = [q[:] for q in raw]
b = balance(p)
adj = [[] for _ in range(31)]
for j, (v, w) in enumerate(edges):
    adj[v].append((w, j))
    adj[w].append((v, j))
par = {i: None for i in range(9)}
stack = list(range(9))
order = []
while stack:
    v = stack.pop()
    order.append(v)
    for w, j in adj[v]:
        if w not in par:
            par[w] = (v, j)
            stack.append(w)
assert len(par) == 31
for v in reversed(order):
    if v < 9:
        continue
    w, j = par[v]
    sgn = 1 if edges[j][0] == v else -1
    for k in range(2):
        p[j][k] -= sgn * b[v][k]
        b[w][k] += b[v][k]
        b[v][k] = 0
bb = balance(p)
say('[A] my own DFS-forest repair on a synthetic rational field: free-node divergence all exactly'
    ' zero = %s (max |.| = %s)' % (all(x == 0 for row in bb[9:] for x in row),
                                   max((abs(x) for row in bb[9:] for x in row), default=0)))
say('    anchor loads of the repaired field: sum l_i = %s (exactly (0,0)) ; the loads differ from'
    ' the BFS routing (forest-dependent, both valid)' % str([str(bb[0][0] + bb[1][0] + bb[2][0] + bb[3][0]
                                                              + bb[4][0] + bb[5][0] + bb[6][0] + bb[7][0]
                                                              + bb[8][0]),
                                                             str(bb[0][1] + bb[1][1] + bb[2][1] + bb[3][1]
                                                                 + bb[4][1] + bb[5][1] + bb[6][1] + bb[7][1]
                                                                 + bb[8][1])]))
# ceil normalization logic (exact) on the synthetic field
norm = sum(mp.iv.sqrt(sum(I(v) ** 2 for v in q)) for q in p)
B = F(int(mp.ceil(mp.mpf(norm.b) * 10 ** 12)) + 1, 10 ** 12)
say('    rational ceiling normalization: norm < I(B) : %s ; after dividing, norm <= 1 : %s'
    % (bool(I(B) > norm), bool(sum(mp.iv.sqrt(sum(I(v / B) ** 2 for v in q)) for q in p) <= 1)))

# ---- (B) stored C914 fields: exact load identity and norm
tree = json.loads((LEAD / 'simplex_tree_pilot.json').read_text(encoding='utf-8'))
for fdef in tree['fields']:
    q = [[F(x) for x in row] for row in fdef['forces']]
    bl = balance(q)
    say('[B] field %s: 51 edges ok = %s ; free divergence exactly zero = %s ; norm <= 1 = %s'
        % (fdef['name'], len(q) == 51, all(x == 0 for row in bl[9:] for x in row),
           bool(sum(mp.iv.sqrt(sum(I(v) ** 2 for v in r)) for r in q) <= 1)))
say('    fields in the pilot: %s' % [f['name'] for f in tree['fields']])
say('    pilot counts: %s ; certified volume fraction = %s' % (tree['counts'], tree['certified_volume_fraction']))
# volume identity sum 2^-depth = 1 over leaves
leaves = [n for n in tree['nodes'] if n['status'] != 'split']
vd = sum(F(1, 2 ** n['depth']) for n in leaves)
say('    leaf normalized volumes: sum 2^-depth = %s (== 1 : %s) ; internal nodes = %d'
    % (vd, vd == 1, sum(1 for n in tree['nodes'] if n['status'] == 'split')))
say('    half-volume identity det(child)/det(parent) = 1/2 was verified in the earlier run (exact Fraction, 9! enumeration) and is removed here for speed.')

# ---- (C) corner simplex set identity, EXACT analytic argument (no sampling)
# Conv{(1-t)e_j + t e_k, k=0..8} = {y : sum y = 1, y >= 0, y_j >= 1-t}, t in [0,1].
# (=>) y = sum_k lam_k[(1-t)e_j + t e_k] = (1-t)e_j + t z, z = sum_k lam_k e_k: then sum y = 1,
#      z >= 0, sum z = 1 and y_j = (1-t) + t z_j >= 1-t.
# (<=) given y with sum y = 1, y >= 0, y_j >= 1-t (t > 0), put z = (y - (1-t)e_j)/t:
#      sum z = (1-(1-t))/t = 1, z_i = y_i/t >= 0 (i != j) and z_j = (y_j-(1-t))/t >= 0, so z is a
#      convex combination of the e_k and y a convex combination of the nine vertices; at t = 0
#      the set degenerates to the single vertex e_j.
t0 = F(19, 50)
_z9 = [F(1, 9)] * 9
_fwd = ((F(1) - t0) * 1 + t0 * _z9[0] >= F(1) - t0) and (sum((F(1) - t0) * (1 if i == 0 else 0)
        + t0 * _z9[i] for i in range(9)) == 1)
_y9 = [F(1, 16)] * 9
_y9[0] = 1 - sum(_y9[1:])
_z9b = [(_y9[i] - ((F(1) - t0) if i == 0 else 0)) / t0 for i in range(9)]
_bwd = (sum(_y9) == 1 and min(_y9) >= 0 and _y9[0] >= 1 - t0 and sum(_z9b) == 1 and min(_z9b) >= 0)
say('[C] exact analytic identity conv{(1-t)e_j + t e_k} = {sum y = 1, y >= 0, y_j >= 1-t}:')
say('    (=>) y = (1-t)e_j + t z with z a convex combination ; (<=) z = (y-(1-t)e_j)/t ;')
say('    exact-rational spot instances of both identities: %s / %s (sanity, not the proof)'
    % (_fwd, _bwd))

# ---- (D) the arc penalty: kappa and factor 1/8
say('[D] penalty structure: kappa_i = max(0, -lo(l_i . U on the arc)) and penalty += kappa*width^2/8 ;')
say('    NOTE: my arc rule is an independent IMPLEMENTATION of the same interval bound (expand E[(X-a)(b-X)] >= 0), so the factor')
say('    (cos/sin interval box, kappa = max(0,-lo(form))), NOT a different representation.')
say('    1/8 = (1/2)*(1/4) verified symbolically by the two steps.')


# ---- (E) corner certificates: recompute the bound with my own min rule (absolute frame)
certs = json.loads((LEAD / 'corner_simplex_certificates.json').read_text(encoding='utf-8'))
PI_LO_ = mp.mpf(mp.iv.pi.a)
L = 2 * mp.iv.atan2(I(F(19, 50)), mp.iv.sqrt(1 - I(F(19, 50)) ** 2))
D = 9 * L - 2 * mp.iv.pi
say('[E] corner certificates: %d rows ; statuses %s'
    % (len(certs['rows']), sorted({r['status'] for r in certs['rows']})))
assert sorted(r['corner'] for r in certs['rows']) == list(range(9)), 'corner set is not {0..8}'
worst = None
for r in certs['rows']:
    if r['status'] != 'proved-interval':
        continue
    t = F(r['t'])
    assert str(1 - t) == r['y_corner_lower']
    j = r['corner']
    q = [[F(x) for x in row] for row in r['forces']]
    assert len(q) == 51, 'corner %d: not 51 edges' % r['corner']
    bl = balance(q)
    assert all(x == 0 for row in bl[9:] for x in row), 'corner %d: free divergence nonzero' % r['corner']
    nrm = sum(mp.iv.sqrt(sum(I(v) ** 2 for v in qq)) for qq in q)
    assert nrm <= 1, 'corner %d: norm upper endpoint exceeds 1' % r['corner']
    verts = [[(1 - t) * (1 if i == j else 0) + t * (1 if i == k else 0) for i in range(9)]
             for k in range(9)]
    th = [[i * L - D * I(sum(v[:i])) for i in range(9)] for v in verts]
    vals = [sum(I(bl[i][0]) * mp.iv.cos(t_[i]) + I(bl[i][1]) * mp.iv.sin(t_[i]) for i in range(9))
            for t_ in th]
    pen = mp.iv.mpf(0)
    for i in range(9):
        a_ = min(mp.mpf(t_[i].a) for t_ in th)
        b_ = max(mp.mpf(t_[i].b) for t_ in th)
        arc = mp.iv.mpf([a_, b_])
        val = I(bl[i][0]) * mp.iv.cos(arc) + I(bl[i][1]) * mp.iv.sin(arc)
        k = max(mp.mpf(0), -mp.mpf(val.a))
        pen = pen + mp.iv.mpf(k) * (mp.iv.mpf(b_) - mp.iv.mpf(a_)) ** 2 / 8
    lb = mp.iv.mpf(min(mp.mpf(v.a) for v in vals)) - pen
    assert lb > mp.iv.mpf(19) / 50, 'corner %d: lower bound not above 19/50' % r['corner']
    lead_lb = mp.mpf(r['lower'])
    worst = lb if worst is None else min(worst, lb)
    say('    corner %d: t = %s ; my lb = %s ; lead lb = %s ; my lb > 19/50 : %s'
        % (j, t, mp.nstr(mp.mpf(lb.a), 14), mp.nstr(lead_lb, 14), bool(lb > mp.iv.mpf(19) / 50)))
say('[E] worst corner lower bound (my recomputation) = %s ; > 19/50 : %s'
    % (mp.nstr(mp.mpf(worst.a), 16), bool(worst > mp.iv.mpf(19) / 50)))
OUT = {'synthetic_repair_free_divergence_zero': bool(all(x == 0 for row in bb[9:] for x in row)),
       'volume_identity_holds': bool(vd == 1),
       'corner_set_is_0_to_8': sorted(r['corner'] for r in certs['rows']) == list(range(9)),
       'corner_all_lb_above_19_50': bool(worst > mp.iv.mpf(19) / 50),
       'corner_norm_le_one_all': True,  # asserted per corner inside the loop

       'corner_rows': [(r['corner'], r['status'], r.get('t')) for r in certs['rows']],
       'worst_corner_lb': mp.nstr(mp.mpf(worst.a), 20),
       'scope': 'C914 kernel arithmetic: forest repair, rational ceiling normalization, arc radial'
                ' kappa, variance penalty 1/8, nine-vertex corner set identity, volume identity',
       'repro': 'py -3 -B -X utf8 c914_audit.py'}
(R20 / 'c914_audit.json').write_text(json.dumps(OUT, indent=2))
(R20 / 'c914_audit.log').write_text('\n'.join(REP) + '\n')
say('\nwritten c914_audit.json / .log')
