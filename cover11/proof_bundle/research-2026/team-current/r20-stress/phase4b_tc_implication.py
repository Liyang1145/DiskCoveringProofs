"""Phase 4b: TC root <-> q0 angle-model correspondence and the dimension/implication audit.
NO optimization, no new starts.

Checks (all evaluations):
  (1) build the 42-angle vector from the TC root via the model's faces list + the relabeling;
  (2) verify the 21 angle-model constraints at that point (is the TC root a point of M?);
  (3) compare R_shape(angles) with the TC's R (is R consistent on the TC family?);
  (4) Jacobian D(Phi): 7 TC params -> 42 angles; rank and whether it lands in T M_sigma;
  (5) dimension bookkeeping: dim M=21, dim M_sigma=11, antisym=10, TC image rank, saturation dim.
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

D = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text())
root = [mp.mpf(s) for s in D['numeric_root']]
a04r, y0r, y1r, Rr = root[:4], root[4], root[5], root[6]

zz = {'__file__': str(LEAD / 'check_angle_only.py')}
exec((LEAD / 'check_angle_only.py').read_text(encoding='utf-8').split("a=ns['x0'][:42]")[0], zz)
ns, shape = zz['ns'], zz['shape']
a0 = np.array(ns['x0'][:42])
faces = [list(f) for f in ns['faces']]
EQ, RHS = np.asarray(ns['eq']), np.asarray(ns['rhs'])


def tc_centers(a04, y0, y1, R):
    a4 = mp.pi - 2 * (a04[0] + a04[1] + a04[2] + a04[3])
    a = [a04[0], a04[1], a04[2], a04[3], a4, a04[3], a04[2], a04[1], a04[0]]
    rho = [mp.cos(a[k]) - mp.sqrt(R * R - mp.sin(a[k]) ** 2) for k in range(9)]
    th = [mp.mpf(0)] * 9
    for k in range(5, 9):
        th[k] = th[k - 1] + a[k - 1] + a[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (a[k] + a[k + 1])
    C = [(rho[k] * mp.cos(th[k]), rho[k] * mp.sin(th[k])) for k in range(9)]
    return a, C, [(y0, mp.mpf(0)), (y1, mp.mpf(0))]


def angle_vector(a04, y0, y1, R, hubmap):
    """map TC params -> 42 angles using the model faces; hubmap chooses model hub label
       for TC hub0/hub1.
       Relabeling: TC junction i <-> model switch s = (5-i)%9  (from the b-value match);
       hence TC arc k (= center C_k) <-> model site (6-k)%9."""
    a, C, hubs = tc_centers(a04, y0, y1, R)
    Cmodel = {((6 - k) % 9): C[k] for k in range(9)}     # model site label -> TC center
    pts = dict(Cmodel)
    pts[hubmap[0]] = hubs[0]
    pts[hubmap[1]] = hubs[1]
    ang = []
    for f in faces:                                      # faces given in model site labels
        for j in range(3):
            p = pts[f[j]]
            q = pts[f[(j + 1) % 3]]
            r = pts[f[(j + 2) % 3]]
            v1 = (q[0] - p[0], q[1] - p[1]); v2 = (r[0] - p[0], r[1] - p[1])
            cr = v1[0] * v2[1] - v1[1] * v2[0]
            dt = v1[0] * v2[0] + v1[1] * v2[1]
            ang.append(float(mp.atan2(abs(cr), dt)))
    # switch half-angle at model switch label s corresponds to TC junction i = (5-s)%9
    for s in range(9):
        i = (5 - s) % 9
        dd = mp.sqrt((C[i][0] - C[(i + 1) % 9][0]) ** 2 + (C[i][1] - C[(i + 1) % 9][1]) ** 2)
        ang.append(float(mp.asin(dd / (2 * R))))
    return np.array(ang)


best = None
for hubmap in [(9, 10), (10, 9)]:
    av = angle_vector(a04r, y0r, y1r, Rr, hubmap)
    err = float(np.abs(av - a0).max())
    print('hubmap', hubmap, 'max|angle - a0| = %.3e' % err)
    if best is None or err < best[0]:
        best = (err, hubmap, av)
err, hubmap, av = best
print('[map] best hubmap %s, max per-coordinate deviation from the saved a0 = %.3e rad' % (hubmap, err))

# (2) model constraints at the mapped point
r_, con_, d_ = shape(av)
lin = np.abs(EQ[:, :42] @ av - RHS).max()
print('[M-point] mapped point: R_shape = %.17g ; max|13 linear| = %.3e ; max|8 nonlinear| = %.3e ; max|21| = %.3e'
      % (r_, lin, np.abs(con_[13:21]).max(), np.abs(con_).max()))
print('[R-consistency] R_shape(mapped) - R_TC = %+.3e' % (float(mp.mpf(repr(float(r_))) - Rr)))

# (4) DPhi: 7 TC params -> 42 angles
h = mp.mpf('1e-25')
def phi(u):
    return angle_vector([mp.mpf(float(x)) for x in u[:4]], mp.mpf(float(u[4])), mp.mpf(float(u[5])),
                        mp.mpf(float(u[6])), hubmap)
u0 = [float(a04r[0]), float(a04r[1]), float(a04r[2]), float(a04r[3]), float(y0r), float(y1r), float(Rr)]
DPhi = np.column_stack([(phi(np.array(u0) + 1e-8 * np.eye(7)[k]) - phi(np.array(u0) - 1e-8 * np.eye(7)[k])) / 2e-8
                        for k in range(7)])
svD = np.linalg.svd(DPhi, compute_uv=False)
print('[DPhi] 7->42 map: singular values =', np.array2string(svD, precision=6), ' rank =', int((svD > 1e-6).sum()))

# constraints' Jacobian at a0 (21x42) and its action on DPhi
Jc = np.column_stack([(shape(a0 + 1e-6 * np.eye(42)[k])[1] - shape(a0 - 1e-6 * np.eye(42)[k])[1]) / (2e-6)
                      for k in range(42)])
print('[T M] J_constraint . DPhi : max abs = %.3e  (0 => TC family tangent to M at the root)' % np.abs(Jc @ DPhi).max())
# symmetric subspace
sig = lambda s: ((4 - s) % 9) if s < 9 else s
perm33 = [None] * 33
for t, f in enumerate(faces):
    ft = sorted([sig(v) for v in f])
    t2 = next(i for i, g in enumerate(faces) if sorted(g) == ft)
    for j, v in enumerate(f):
        perm33[3 * t + j] = 3 * t2 + faces[t2].index(sig(v))
perm = perm33 + [33 + ((3 - i) % 9) for i in range(9)]
orb, seen = [], [False] * 42
for i in range(42):
    if not seen[i]:
        j = perm[i]; seen[i] = seen[j] = True
        v = np.zeros(42); v[i] = 1; v[j] = v[j] + (1 / math.sqrt(2) if j != i else 0)
        if j != i:
            v[i] = 1 / math.sqrt(2)
        else:
            v[i] = 1
        orb.append(v)
S = np.array(orb).T
rS = int((np.linalg.svd(Jc @ S, compute_uv=False) > 1e-7).sum())
print('[dim] symmetric subspace dim = %d ; rank(constraints|S) = %d ; dim M_sigma = %d ; antisym dim = %d'
      % (S.shape[1], rS, S.shape[1] - rS, 42 - 21 - (S.shape[1] - rS)))
# projection of DPhi onto T M_sigma and onto the saturation complement
print('[dim] rank(DPhi) = %d ; if DPhi lands in T M_sigma then dim(TC image) = %d and saturation complement = %d'
      % (int((svD > 1e-6).sum()), int((svD > 1e-6).sum()), (S.shape[1] - rS) - int((svD > 1e-6).sum())))
out = dict(scope='TC->angle map verification and dimension audit; evaluation only, no optimization',
           hubmap=list(hubmap), max_angle_deviation=float(err), R_shape_mapped=float(r_),
           R_TC_minus_Rshape=float(Rr - mp.mpf(repr(float(r_)))),
           constraint_residuals=dict(linear=float(lin), nonlinear=float(np.abs(con_[13:21]).max())),
           DPhi_singular_values=svD.tolist(), DPhi_rank=int((svD > 1e-6).sum()),
           Jc_DPhi_max=float(np.abs(Jc @ DPhi).max()),
           dims=dict(M=21, M_sigma=int(S.shape[1] - rS), antisym=42 - 21 - int(S.shape[1] - rS),
                     TC_image=int((svD > 1e-6).sum()),
                     saturation_complement=int(S.shape[1] - rS) - int((svD > 1e-6).sum())))
(OUT / 'phase4b_tc_implication.json').write_text(json.dumps(out, indent=2))
print('[done] -> out/phase4b_tc_implication.json')
