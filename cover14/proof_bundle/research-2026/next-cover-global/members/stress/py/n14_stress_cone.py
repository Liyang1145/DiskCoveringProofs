"""n14_stress_cone.py — n14 应力锥 + Schur + 常数次式 M 的路线诊断。

问题：14 活动面/10 锚网络是否存在**非负**应力（含强正应力）？其 Schur 电导与
M（c_d = T_d(1-2U^2), d<=4；c5=-1 因 5L>pi）在 1^perp 上是否有正余量？
若全锥都给出负余量 => 单一常应力全域凸性不可直接沿用（需分域/Taylor/消元）。

方法：A α = 0, α>=0, Σα=1 的多面体；顶点用随机线性目标 LP 采样；
每个应力点 → Schur（跳过零权隔离节点）→ q>=0 → M → λ_min(1^perp)。
数值仅路线诊断，不宣称正定=证明。
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

U = '0.33173203427623414'
OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

th, R, C = X.load()
active, anchors, owners = X.arcs_and_anchors(C, R)
faces = X.voronoi_faces(C, R)
act_faces = [f for f in faces if f[3]]
slack_faces = [f for f in faces if not f[3]]
W("n14: R=%s" % mp.nstr(R, 25))
W("centers=14  boundary-active=%s  anchors=%d  Voronoi-in-D=%d (active %d, slack %d)"
  % (active, len(anchors), len(faces), len(act_faces), len(slack_faces)))
W("anchor owners (cyclic): %s" % owners)
L, defect = L_and_defect(U)
W("L = 2asinU = %s ; 10L-2pi = %s ; 4L<pi %s ; 5L<pi %s"
  % (mp.nstr(L, 15), mp.nstr(defect, 15), 4 * L < mp.pi, 5 * L < mp.pi))


def build(face_list):
    net = Net(anchors, C, [f[0] for f in face_list])
    net.add_anchor_edges([tuple(o) for o in owners])
    net.add_face_edges([f[1] for f in face_list])
    return net


def equilibrium_matrix(net):
    n = net.na + net.ns + net.nf
    free = list(range(net.na, n))
    fnode = {v: k for k, v in enumerate(free)}
    A = np.zeros((2 * len(free), len(net.edges)))
    for e, (u, v) in enumerate(net.edges):
        for node in (u, v):
            if node in fnode:
                r = fnode[node]
                zu = net._z(u); zv = net._z(v)
                d = (zu[0] - zv[0], zu[1] - zv[1]) if node == u else (zv[0] - zu[0], zv[1] - zu[1])
                A[2 * r, e] = float(d[0]); A[2 * r + 1, e] = float(d[1])
    return A


def schur_nonneg(net, alpha, tol=1e-12):
    """Schur complement keeping only supported free nodes (zero-weight nodes dropped)."""
    n = net.na + net.ns + net.nf
    L = [[mp.mpf(0)] * n for _ in range(n)]
    for e, (u, v) in enumerate(net.edges):
        w = mp.mpf(float(alpha[e]))
        if w == 0:
            continue
        L[u][u] += w; L[v][v] += w; L[u][v] -= w; L[v][u] -= w
    supported = [k for k in range(net.na, n) if L[k][k] > 0]
    order = supported
    for ii, k in enumerate(order):
        p = L[k][k]
        assert p > 0
        remain = order[ii + 1:] + list(range(net.na))
        for ix_i, i in enumerate(remain):
            if L[i][k] == 0:
                continue
            for j in remain[ix_i:]:
                val = L[i][j] - L[i][k] * L[k][j] / p
                L[i][j] = val
                if j != i:
                    L[j][i] = val
    q = {}
    for i in range(net.na):
        for j in range(i + 1, net.na):
            q[i, j] = -L[i][j]
    return q, supported


def analyse(net, alpha, label=''):
    q, supported = schur_nonneg(net, alpha)
    negq = {k: v for k, v in q.items() if v < -1e-18}
    lab = lambda i, j: min(abs(i - j), net.na - abs(i - j))
    cd = cos_minorants(U, 4)
    c_by_d = {d: mp.mpf(float(v)) for d, v in cd.items()}
    c_by_d[5] = mp.mpf(-1)
    M, _ = net.M_from_q_and_labels(q, c_by_d, lab)
    ev, ev1, lam = eig_1perp(M)
    nz = sum(1 for v in q.values() if abs(v) > 1e-18)
    supported_anchors = len({i for (i, j) in q if abs(q[i, j]) > 1e-18} |
                            {j for (i, j) in q if abs(q[i, j]) > 1e-18})
    W("   [%s] edges=%d supported free nodes=%d  q: nonzero %d  negatives %d  anchors touched %d/10  "
      "lambda_min(M|1perp) = %.6e" % (label, len(net.edges), len(supported), nz, len(negq),
                                      supported_anchors, lam))
    return dict(label=label, n_edges=len(net.edges), n_supported=len(supported), q_nonzero=nz,
                q_negative=len(negq), anchors_touched=supported_anchors, lam_min_1perp=lam,
                M_eig_1perp=ev1)


for name, fl in (('14 active faces', act_faces), ('16 faces (incl. 2 slack)', faces)):
    net = build(fl)
    A = equilibrium_matrix(net)
    sv = np.linalg.svd(A, compute_uv=False)
    rank = int((sv > 1e-9 * sv[0]).sum())
    W("== network '%s': anchors=%d sites=%d witnesses=%d edges=%d ; rank(A)=%d ; nullity=%d"
      % (name, net.na, net.ns, net.nf, len(net.edges), rank, len(net.edges) - rank))
    # feasibility of the nonneg cone
    from scipy.optimize import linprog
    m = len(net.edges)
    Aeq = np.vstack([A, np.ones((1, m))])
    beq = np.zeros(A.shape[0] + 1); beq[-1] = 1.0
    res = linprog(np.zeros(m), A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * m, method='highs')
    W("   nonneg stress cone nonempty: %s" % res.success)
    # strict positivity?
    A_ub = np.zeros((m, m + 1)); 
    for e in range(m):
        A_ub[e, e] = -1.0; A_ub[e, -1] = 1.0
    res_t = linprog(np.r_[np.zeros(m), -1.0], A_ub=A_ub, b_ub=np.zeros(m),
                    A_eq=np.vstack([np.c_[A, np.zeros(A.shape[0])], np.r_[np.ones(m), 0.0][None, :]]),
                    b_eq=beq, bounds=[(0, None)] * m + [(None, None)], method='highs')
    tmax = res_t.x[-1] if res_t.success else float('nan')
    W("   max uniform lower bound t = %.3e  (strictly positive stress exists: %s)" % (tmax, tmax > 1e-12))
    # per-edge max weight => forced-zero edges
    amax = np.zeros(m)
    for e in range(m):
        c = np.zeros(m); c[e] = -1.0
        r = linprog(c, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * m, method='highs')
        amax[e] = -r.fun if r.success else float('nan')
    forced = [e for e in range(m) if amax[e] < 1e-12]
    W("   forced-zero edges: %d of %d  %s" % (len(forced), m,
      [(net.edges[e], round(amax[e], 8)) for e in forced][:12]))
    # sample vertices of the normalized polytope with random objectives
    rng = np.random.default_rng(7)
    verts, seen = [], set()
    for _ in range(300):
        c = rng.normal(size=m)
        r = linprog(-c, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * m, method='highs')
        if not r.success:
            continue
        key = tuple(np.round(r.x, 9))
        if key in seen:
            continue
        seen.add(key); verts.append(r.x)
    W("   distinct vertices sampled: %d" % len(verts))
    stats = [analyse(net, a, 'vertex%d' % i) for i, a in enumerate(verts)]
    stats.append(analyse(net, res.x, 'LP-feas'))
    best = max(stats, key=lambda s: s['lam_min_1perp'])
    worst = min(stats, key=lambda s: s['lam_min_1perp'])
    W("   => lambda_min(M|1perp) over %d stresses: best %.6e  worst %.6e"
      % (len(stats), best['lam_min_1perp'], worst['lam_min_1perp']))
    json.dump({'network': name, 'n_edges': m, 'rank_A': rank, 'nullity': m - rank,
               't_max': float(tmax), 'forced_zero': [list(net.edges[e]) for e in forced],
               'n_vertices': len(verts), 'best': best, 'worst': worst},
              open(Path(__file__).resolve().parents[1] / 'evidence' / ('cone_%s.json' % name.split()[0]), 'w'),
              indent=1, default=str)

Path(Path(__file__).resolve().parents[1] / 'logs' / 'n14_stress_cone.txt').write_text("\n".join(OUT), encoding='utf-8')
print("\nwrote logs/n14_stress_cone.txt")
