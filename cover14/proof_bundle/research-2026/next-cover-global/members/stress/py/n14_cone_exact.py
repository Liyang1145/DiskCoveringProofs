"""n14_cone_exact.py (v2) — 显式零空间 + (α>=0, Σα=1) 解集 + λ_min(M|1^perp) 复核。

只依赖 n14_extract（几何）与 stress_core（常数/M/特征）；不 import 其它 cone 脚本（避免副作用打印）。
"""
import sys
from pathlib import Path

import numpy as np
import mpmath as mp

mp.mp.dps = 60
sys.path.insert(0, str(Path(__file__).resolve().parent))
from stress_core import Net, cos_minorants, L_and_defect       # noqa: E402
import n14_extract as X                                        # noqa: E402

U = '0.33173203427623414'
OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)


def build(face_list, anchors, C):
    net = Net(anchors, C, [f[0] for f in face_list])
    net.add_anchor_edges([tuple(o) for o in X.arcs_and_anchors(C, mp.mpf(0))[2]] if False else None)  # placeholder
    return net


def make_net(face_list, anchors, owners, C):
    net = Net(anchors, C, [f[0] for f in face_list])
    net.add_anchor_edges([tuple(o) for o in owners])
    net.add_face_edges([f[1] for f in face_list])
    return net


def eq_matrix(net):
    n = net.na + net.ns + net.nf
    free = list(range(net.na, n))
    fnode = {v: k for k, v in enumerate(free)}
    A = np.zeros((2 * len(free), len(net.edges)))
    for e, (u, v) in enumerate(net.edges):
        for node in (u, v):
            if node in fnode:
                r = fnode[node]
                zu, zv = net._z(u), net._z(v)
                d = (zu[0] - zv[0], zu[1] - zv[1]) if node == u else (zv[0] - zu[0], zv[1] - zu[1])
                A[2 * r, e] = float(d[0]); A[2 * r + 1, e] = float(d[1])
    return A


def tor_matrix(net):
    m = len(net.edges)
    T = np.zeros((net.na, m))
    for e, (u, v) in enumerate(net.edges):
        for node, other in ((u, v), (v, u)):
            if node < net.na:
                ux, uy = net.A[node]
                zx, zy = net._z(other)
                T[node, e] = -uy * (zx - ux) + ux * (zy - uy)
    return T


def schur_q(net, alpha):
    n = net.na + net.ns + net.nf
    L = [[mp.mpf(0)] * n for _ in range(n)]
    for e, (u, v) in enumerate(net.edges):
        w = mp.mpf(float(alpha[e]))
        if w == 0:
            continue
        L[u][u] += w; L[v][v] += w; L[u][v] -= w; L[v][u] -= w
    order = [k for k in range(net.na, n) if L[k][k] > 0]
    for ii, k in enumerate(order):
        p = L[k][k]; assert p > 0
        remain = order[ii + 1:] + list(range(net.na))
        for ix_i, i in enumerate(remain):
            if L[i][k] == 0:
                continue
            for j in remain[ix_i:]:
                val = L[i][j] - L[i][k] * L[k][j] / p
                L[i][j] = val
                if j != i:
                    L[j][i] = val
    return {(i, j): -L[i][j] for i in range(net.na) for j in range(i + 1, net.na)}


def lam_min_M(net, q):
    lab = lambda i, j: min(abs(i - j), net.na - abs(i - j))
    cd = cos_minorants(U, 4)
    c_by_d = {d: mp.mpf(float(v)) for d, v in cd.items()}; c_by_d[5] = mp.mpf(-1)
    M, _ = net.M_from_q_and_labels(q, c_by_d, lab)
    na = net.na
    G = mp.matrix(na - 1, na - 1)
    for k in range(1, na):
        for l in range(1, na):
            G[k - 1, l - 1] = M[0][0] - M[0][l] - M[k][0] + M[k][l]
    E, _ = mp.eigsy(G)
    return float(E[0]), [float(v) for v in E]


th, R, C = X.load()
active, anchors, owners = X.arcs_and_anchors(C, R)
faces = X.voronoi_faces(C, R)
act_faces = [f for f in faces if f[3]]

for name, fl in (('14active(62 edges)', act_faces), ('16faces(68 edges)', faces)):
    net = make_net(fl, anchors, owners, C)
    A = eq_matrix(net); T = tor_matrix(net); m = len(net.edges)
    Mst = np.vstack([A, T])
    sv = np.linalg.svd(Mst, compute_uv=False)
    # high precision smallest singular values via mpmath (Gram matrix of Mst)
    Mm = mp.matrix(*Mst.shape)
    for i in range(Mst.shape[0]):
        for j in range(Mst.shape[1]):
            Mm[i, j] = mp.mpf(float(Mst[i, j]))
    G = Mm.T * Mm
    ev = mp.eigsy(G, eigvals_only=True)
    sv_mp = [mp.sqrt(max(ev[k], mp.mpf(0))) for k in range(len(ev))]
    W("== %s" % name)
    W("   numpy sv tail: %s ; mpmath sv tail: %s" % ([round(float(s), 12) for s in sv[-3:]],
                                                     [mp.nstr(s, 8) for s in sv_mp[:3]]))
    rank_mp = sum(1 for s in sv_mp if s > mp.mpf('1e-25') * sv_mp[-1])
    W("   mpmath rank = %d / %d columns  => exact nullity = %d" % (rank_mp, m, m - rank_mp))
    if m - rank_mp == 0:
        W("   => 只有零应力（[A;T] 满列秩）")
        continue

with_uv = np.linalg.svd(np.vstack([eq_matrix(make_net(faces, anchors, owners, C)),
                                   tor_matrix(make_net(faces, anchors, owners, C))]))
sv_uv = with_uv[1]
Vt = with_uv[2]
null_dim = int((sv_uv < 1e-10 * sv_uv[0]).sum())
W("")
W("16-face: numpy nullity=%d ; singular tail=%s" % (null_dim, [round(float(s), 12) for s in sv_uv[-4:]]))
if null_dim:
    V = Vt[-null_dim:].T          # columns span the nullspace
    for k in range(V.shape[1]):
        V[:, k] = V[:, k] / V[:, k].sum()
    W("   nullspace vectors: support (|.|>1e-8) = %s" % [int((np.abs(V[:, k]) > 1e-8).sum()) for k in range(V.shape[1])])
    W("   signs: %s" % [('mixed' if (V[:, k].min() < -1e-9 and V[:, k].max() > 1e-9) else 'one-signed')
                        for k in range(V.shape[1])])
    if null_dim == 2:
        v1, v2 = V[:, 0], V[:, 1]; d = v1 - v2
        lo, hi = 0.0, 1.0
        for e in range(len(d)):
            if abs(d[e]) < 1e-14:
                continue
            t = -v2[e] / d[e]
            if d[e] > 0:
                lo = max(lo, t)
            else:
                hi = min(hi, t)
        W("   feasible segment t in [%.6f, %.6f]  (alpha = v2 + t*(v1-v2))" % (lo, hi))
        net = make_net(faces, anchors, owners, C)
        for t, tag in ((lo, 'endpoint-lo'), (hi, 'endpoint-hi'), (0.5 * (lo + hi), 'midpoint')):
            a = np.clip(v2 + t * d, 0, None)
            q = schur_q(net, a)
            lam, eigs = lam_min_M(net, q)
            W("     %-12s support=%3d  min q=%.3e  lambda_min(M|1perp)=%+.6e   (eig list head %s)"
              % (tag, int((a > 1e-12).sum()), min(q.values()), lam, [round(v, 6) for v in eigs[:4]]))

Path(Path(__file__).resolve().parents[1] / 'logs' / 'n14_cone_exact.txt').write_text("\n".join(OUT), encoding='utf-8')
print("\nwrote logs/n14_cone_exact.txt")
