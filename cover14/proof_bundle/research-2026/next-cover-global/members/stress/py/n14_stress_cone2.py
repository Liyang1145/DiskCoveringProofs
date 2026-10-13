"""n14_stress_cone2.py — 加入**锚点扭矩平衡**后的应力锥判定（n12 中该条件恒等成立）。

自由节点平衡 A α = 0（55 独立行）只约束自由节点；锚点固定，故其切向（torque）残差
必须**另外**要求为 0：  T_i(α) = Σ_{e∋i} α_e τ_i·(z_e − u_i) = 0, τ_i = (−u_iy, u_ix)。
n12 的 7 轨道应力满足它（T=0 ⟺ yv = zt sinα 恒等式）；n14 需要显式施加。

判定：rank([A;T]) vs 边数；锥 [A;T]α=0, α>=0, Σα=1 是否非空/是否含正元；
每个解点的 Schur q 与 M|1^perp 余量。
"""
import json
import sys
from pathlib import Path

import numpy as np
import mpmath as mp

mp.mp.dps = 50
sys.path.insert(0, str(Path(__file__).resolve().parent))
from stress_core import Net, cos_minorants, eig_1perp, L_and_defect   # noqa: E402
import n14_extract as X                                              # noqa: E402
from n14_stress_cone import build, equilibrium_matrix, schur_nonneg, analyse  # noqa: E402

U = '0.33173203427623414'
OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

th, R, C = X.load()
active, anchors, owners = X.arcs_and_anchors(C, R)
faces = X.voronoi_faces(C, R)
act_faces = [f for f in faces if f[3]]
slack_faces = [f for f in faces if not f[3]]


def torque_matrix(net):
    m = len(net.edges)
    T = np.zeros((net.na, m))
    for e, (u, v) in enumerate(net.edges):
        for node, other in ((u, v), (v, u)):
            if node < net.na:                      # anchor
                ai = node
                ux, uy = net.A[ai]
                zx, zy = net._z(other)
                T[ai, e] = -uy * (zx - ux) + ux * (zy - uy)
    return T


for name, fl in (('14active', act_faces), ('16faces', faces)):
    net = build(fl)
    A = equilibrium_matrix(net)
    T = torque_matrix(net)
    m = len(net.edges)
    sv = np.linalg.svd(np.vstack([A, T]), compute_uv=False)
    rank_AT = int((sv > 1e-9 * sv[0]).sum())
    W("== %s: edges=%d ; rank(A)=%d ; rank([A;T])=%d ; nullity(A)=%d ; nullity([A;T])=%d"
      % (name, m, np.linalg.matrix_rank(A, tol=1e-9 * np.linalg.svd(A, compute_uv=False)[0]),
         rank_AT, m - np.linalg.matrix_rank(A, tol=1e-9), m - rank_AT))
    from scipy.optimize import linprog
    Aeq = np.vstack([A, T, np.ones((1, m))])
    beq = np.zeros(Aeq.shape[0]); beq[-1] = 1.0
    res = linprog(np.zeros(m), A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * m, method='highs')
    W("   cone [A;T]α=0, α>=0, Σα=1 nonempty: %s   (%s)" % (res.success, res.message[:60]))
    if not res.success:
        # minimum-norm least squares: how badly violated?
        Mmat = np.vstack([A, T])
        sv2 = np.linalg.svd(Mmat, compute_uv=False)
        W("   smallest singular values of [A;T]: %s" % [round(float(s), 8) for s in sv2[-3:]])
        continue
    alpha = res.x
    W("   support=%d  min α=%.3e  max α=%.3e" % (int((alpha > 1e-12).sum()), alpha.min(), alpha.max()))
    # strict positivity within the cone?
    A_ub = np.zeros((m, m + 1))
    for e in range(m):
        A_ub[e, e] = -1.0; A_ub[e, -1] = 1.0
    Aeq2 = np.vstack([np.c_[A, np.zeros(A.shape[0])], np.c_[T, np.zeros(T.shape[0])],
                      np.r_[np.ones(m), 0.0][None, :]])
    res_t = linprog(np.r_[np.zeros(m), -1.0], A_ub=A_ub, b_ub=np.zeros(m), A_eq=Aeq2, b_eq=beq,
                    bounds=[(0, None)] * m + [(None, None)], method='highs')
    tmax = res_t.x[-1] if res_t.success else float('nan')
    W("   max uniform lower bound t = %.3e  (strict positivity: %s)" % (tmax, tmax > 1e-12))
    # torque check on the found stress (independent recomputation)
    tor = T @ alpha
    W("   max |anchor torque| = %.3e   (residual of T α)" % np.abs(tor).max())
    st = analyse(net, alpha, 'cone+torque')
    # sample the (now smaller) solution polytope
    rng = np.random.default_rng(11)
    verts, seen = [], set()
    for _ in range(200):
        c = rng.normal(size=m)
        r = linprog(-c, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * m, method='highs')
        if not r.success:
            continue
        key = tuple(np.round(r.x, 9))
        if key in seen:
            continue
        seen.add(key); verts.append(r.x)
    W("   distinct vertices in cone+torque: %d" % len(verts))
    stats = [analyse(net, a, 'v%d' % i) for i, a in enumerate(verts)]
    if stats:
        best = max(stats, key=lambda s: s['lam_min_1perp'])
        W("   => best lambda_min(M|1perp) = %.6e (%s) ; worst %.6e"
          % (best['lam_min_1perp'], best['label'], min(s['lam_min_1perp'] for s in stats)))
    json.dump({'network': name, 'edges': m, 'rank_AT': int(rank_AT), 'cone_nonempty': True,
               't_max': float(tmax), 'support': int((alpha > 1e-12).sum()),
               'alpha': [float(x) for x in alpha], 'best_lam': best['lam_min_1perp'] if stats else None,
               'best_eig': best['M_eig_1perp'] if stats else None},
              open(Path(__file__).resolve().parents[1] / 'evidence' / ('conetorque_%s.json' % name), 'w'), indent=1)

Path(Path(__file__).resolve().parents[1] / 'logs' / 'n14_stress_cone2.txt').write_text("\n".join(OUT), encoding='utf-8')
print("\nwrote logs/n14_stress_cone2.txt")
