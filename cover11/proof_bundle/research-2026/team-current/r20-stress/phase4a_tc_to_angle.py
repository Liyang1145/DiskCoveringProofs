"""Phase 4a: TC-root geometry -> q0 angle-model map; active list; dimension bookkeeping.
NO optimization. Pure evaluation of the lead's certified 12D TC root.

Sources read-only:
  lead/repaired_tc_krawczyk.json  (12 numeric root: 7 TC params + 5 multipliers)
  session2/n11tc/py/tc_s32_kraw.py res5 (geometry formulas, re-implemented here)
  lead/check_angle_only.py q0 model (faces list, constraint Jacobian, x0 for comparison)
Writes only in research-2026/team-current/r20-stress/out .
"""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp

W_DIR = Path(__file__).parent; OUT = W_DIR / 'out'
LEAD = W_DIR.parent / 'lead'
mp.mp.dps = 60

# ---------------- 1. TC root -------------------------------------------------------------
D = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text())
root = [mp.mpf(s) for s in D['numeric_root']]
a04, y0, y1, R = root[:4], root[4], root[5], root[6]
lam = root[7:]
a4 = mp.pi - 2 * sum(a04)
a = [a04[0], a04[1], a04[2], a04[3], a4, a04[3], a04[2], a04[1], a04[0]]
rho = [mp.cos(a[k]) - mp.sqrt(R * R - mp.sin(a[k]) ** 2) for k in range(9)]
th = [mp.mpf(0)] * 9
for k in range(5, 9):
    th[k] = th[k - 1] + a[k - 1] + a[k]
for k in range(3, -1, -1):
    th[k] = th[k + 1] - (a[k] + a[k + 1])
C = [(rho[k] * mp.cos(th[k]), rho[k] * mp.sin(th[k])) for k in range(9)]
U = []
for k in range(9):
    k2 = (k + 1) % 9
    U.append((C[k][0] + C[k2][0] - mp.cos(th[k] + a[k]), C[k][1] + C[k2][1] - mp.sin(th[k] + a[k])))
hubs = [(y0, mp.mpf(0)), (y1, mp.mpf(0))]
m_, d_ = (y0 + y1) / 2, (y1 - y0) / 2
h_ = mp.sqrt(R * R - d_ * d_)
waist = [(m_, h_), (m_, -h_)]
dist = lambda p, q: mp.sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)
print('== TC root: R = %s' % mp.nstr(R, 40))
print('   a (deg) =', [float(mp.degrees(v)) for v in a])
print('   rho =', [mp.nstr(v, 12) for v in rho])
print('   th (deg) =', [float(mp.degrees(v)) for v in th])
print('   y0=%s y1=%s  lam=%s' % (mp.nstr(y0, 12), mp.nstr(y1, 12), [mp.nstr(v, 8) for v in lam]))

# ---------------- 2. active list at the root ---------------------------------------------
act = {'corner_hub': [], 'waist_ring': [], 'arc_endpoint': [], 'corner_ring': []}
for k in range(9):
    for l, hb in enumerate(hubs):
        act['corner_hub'].append(dict(k=k, hub=l, d_minus_R=float(dist(U[k], hb) - R)))
for w in waist:
    for k in (2, 6):
        act['waist_ring'].append(dict(k=k, d_minus_R=float(dist(w, C[k]) - R)))
for k in range(9):
    for s in (+1, -1):
        P = (mp.cos(th[k] + s * a[k]), mp.sin(th[k] + s * a[k]))
        act['arc_endpoint'].append(dict(k=k, s=s, d_minus_R=float(dist(P, C[k]) - R)))
for k in range(9):
    for k2 in ((k + 1) % 9,):
        act['corner_ring'].append(dict(k=k, d_minus_R=float(dist(U[k], C[k]) - R), other=k2))
ch = sorted([x for x in act['corner_hub'] if abs(x['d_minus_R']) < 1e-9], key=lambda x: (x['hub'], x['k']))
wr = sorted([x for x in act['waist_ring'] if abs(x['d_minus_R']) < 1e-9], key=lambda x: x['k'])
ae = [x for x in act['arc_endpoint'] if abs(x['d_minus_R']) < 1e-9]
cr = [x for x in act['corner_ring'] if abs(x['d_minus_R']) < 1e-9]
print('== ACTIVE LIST (|d-R| < 1e-9 at the root)')
print('   corner-hub contacts (k,hub):', [(x['k'], x['hub']) for x in ch])
print('   waist-ring contacts (ring k):', [x['k'] for x in wr])
print('   arc-endpoint contacts (k,s): count =', len(ae), '(all 9 arcs, both ends, by construction)')
print('   corner-ring (2nd circle of the pair) contacts: count =', len(cr))
print('   max |d-R| over all 18 corner-hub pairs = %.3e' % max(abs(x['d_minus_R']) for x in act['corner_hub']))

# ---------------- 3. switch half-angles from the TC geometry -----------------------------
b_tc = []
for k in range(9):
    k2 = (k + 1) % 9
    base = dist(C[k], C[k2])
    b_tc.append(float(mp.asin(base / (2 * R))))
print('== switch half-angles from TC geometry (deg), arc-junction order:',
      [round(math.degrees(v), 6) for v in b_tc])

# model x0 comparison
zz = {'__file__': str(LEAD / 'check_angle_only.py')}
exec((LEAD / 'check_angle_only.py').read_text(encoding='utf-8').split("a=ns['x0'][:42]")[0], zz)
ns, shape = zz['ns'], zz['shape']
a0 = ns['x0'][:42]
b_model = np.array(a0[33:42])
print('   model b (deg)                :', [round(math.degrees(v), 6) for v in b_model])
# find relabeling: rotation+reflection matching the palindromic pattern
cands = []
for shift in range(9):
    for rev in (False, True):
        idx = [((shift - i) % 9 if rev else (shift + i) % 9) for i in range(9)]
        err = max(abs(b_tc[i] - b_model[idx[i]]) for i in range(9))
        cands.append((err, shift, rev, idx))
cands.sort()
print('   best relabeling: err=%.3e shift=%d rev=%s idx=%s' % (cands[0][0], cands[0][1], cands[0][2], cands[0][3]))

# ---------------- 4. dimension bookkeeping ------------------------------------------------
faces = [list(f) for f in ns['faces']]
# site reflection: ring i -> (4-i)%9 ; hubs fixed (both on the symmetry axis of the TC model)
sig = lambda s: ((4 - s) % 9) if s < 9 else s
# permutation on the 33 site-face angle coordinates
perm33 = [None] * 33
for t, f in enumerate(faces):
    ft = sorted([sig(v) for v in f])
    t2 = next(i for i, g in enumerate(faces) if sorted(g) == ft)
    for j, v in enumerate(f):
        j2 = faces[t2].index(sig(v))
        perm33[3 * t + j] = 3 * t2 + j2
perm = perm33 + [None] * 9
# switch coordinate i -> (3-i)%9
for i in range(9):
    perm[33 + i] = 33 + ((3 - i) % 9)
fixed = sum(1 for i in range(42) if perm[i] == i)
pairs = (42 - fixed) // 2
print('== symmetry action on the 42 angle coordinates (site i->(4-i)%9, hubs fixed):')
print('   fixed coords = %d ; 2-cycles = %d ; orbits = %d (= dim of symmetric subspace of R^42)'
      % (fixed, pairs, fixed + pairs))
print('   face set sigma-invariant:', all(sorted([sig(v) for v in f]) in [sorted(g) for g in faces] for f in faces))
# rank of the 21 constraints restricted to the symmetric subspace
orb = []
seen = [False] * 42
for i in range(42):
    if not seen[i]:
        j = perm[i]
        seen[i] = seen[j] = True
        if j == i:
            v = np.zeros(42); v[i] = 1; orb.append(v)
        else:
            v = np.zeros(42); v[i] = v[j] = 1 / math.sqrt(2); orb.append(v)
S = np.array(orb).T                     # 42 x 22
J = np.column_stack([(shape(a0 + 1e-6 * S @ np.eye(S.shape[1])[:, k])[1] - shape(a0 - 1e-6 * S @ np.eye(S.shape[1])[:, k])[1]) / (2e-6)
                     for k in range(S.shape[1])])          # 21 x 22
sv = np.linalg.svd(J, compute_uv=False)
r = int((sv > 1e-7).sum())
print('   constraint Jacobian on the symmetric subspace: shape %s, singular values %s' % (J.shape, np.round(sv, 5).tolist()))
print('   rank = %d  =>  dim M_sigma = %d - %d = %d' % (r, S.shape[1], r, S.shape[1] - r))
print('   TC family: 7 params (%d ring angles + 2 hub-axis coords + R), 5 contacts => contact manifold dim 2' % 4)
print('   TC 12D system: 5 contacts + 7 stationarity components -> isolated root (rank 12 per lead certificate)')

out = dict(scope='TC-root geometry -> q0 angle map, active list, dimension bookkeeping; evaluation only',
           R=str(R), a_deg=[float(mp.degrees(v)) for v in a], rho=[mp.nstr(v, 12) for v in rho],
           th_deg=[float(mp.degrees(v)) for v in th], y0=str(y0), y1=str(y1), lam=[str(v) for v in lam],
           active=dict(corner_hub=[(x['k'], x['hub']) for x in ch], waist_ring=[x['k'] for x in wr],
                       n_arc_endpoints=len(ae), n_corner_ring=len(cr),
                       max_corner_hub_abs=float(max(abs(x['d_minus_R']) for x in act['corner_hub']))),
           b_tc_deg=[math.degrees(v) for v in b_tc], b_model_deg=[math.degrees(v) for v in b_model],
           relabeling=dict(err=float(cands[0][0]), shift=int(cands[0][1]), rev=bool(cands[0][2]), idx=[int(v) for v in cands[0][3]]),
           symmetry=dict(fixed=fixed, pairs=pairs, orbits=fixed + pairs, face_set_invariant=True,
                         rank_constraints=int(r), dim_M_sigma=int(S.shape[1] - r)))
(OUT / 'phase4a_tc_to_angle.json').write_text(json.dumps(out, indent=2))
print('[done] -> out/phase4a_tc_to_angle.json')
