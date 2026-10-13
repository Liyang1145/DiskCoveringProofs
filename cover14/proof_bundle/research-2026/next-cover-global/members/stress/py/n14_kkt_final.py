"""n14_kkt_final.py — 修正后的 KKT 锥判定（differences 形式）与机制说明。

正确条件（r*-cap；A={4,9} active；ν 自由 ⇒ c 自由）：
    α >= 0, Σα = 1, A α = 0,
    g_k(α) = c  (k ∈ I),   g_k(α) <= c  (k ∈ A),      g_k = Σ_{i=k+1..9} τ_i , τ = −2Tα.
⇒ 齐次部分 = [A ; {g_k − g_0}_{k∈I} ]  (62 x 62)。
对每个核向量：检查非负、c、active 不等式；若可行则算 Schur/M 余量。
"""
import json
import sys
from pathlib import Path

import numpy as np
import mpmath as mp

mp.mp.dps = 60
sys.path.insert(0, str(Path(__file__).resolve().parent))
from stress_core import Net      # noqa: E402
import n14_extract as X          # noqa: E402

OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

th, R, C = X.load()
active, anchors, owners = X.arcs_and_anchors(C, R)
faces = X.voronoi_faces(C, R)
act_faces = [f for f in faces if f[3]]
net = Net(anchors, C, [f[0] for f in act_faces])
net.add_anchor_edges([tuple(o) for o in owners])
net.add_face_edges([f[1] for f in act_faces])
na, ns, nf = net.na, net.ns, net.nf
n = na + ns + nf
m = len(net.edges)
free = list(range(na, n))
fnode = {v: k for k, v in enumerate(free)}

A = mp.matrix(2 * len(free), m)
T = mp.matrix(na, m)
for e, (u, v) in enumerate(net.edges):
    for node in (u, v):
        if node in fnode:
            r = fnode[node]
            zu, zv = net._z(u), net._z(v)
            d = (zu[0] - zv[0], zu[1] - zv[1]) if node == u else (zv[0] - zu[0], zv[1] - zu[1])
            A[2 * r, e] = d[0]; A[2 * r + 1, e] = d[1]
        if node < na:
            other = v if node == u else u
            ux, uy = net.A[node]
            zx, zy = net._z(other)
            T[node, e] = -uy * (zx - ux) + ux * (zy - uy)
G = mp.matrix(10, m)
for e in range(m):
    tau = [-2 * T[i, e] for i in range(10)]
    for k in range(10):
        G[k, e] = sum(tau[k + 1:])

ang = [mp.atan2(a[1], a[0]) % (2 * mp.pi) for a in anchors]
Ls = 2 * mp.asin(R)
gaps_deg = [float(((ang[(k + 1) % 10] - ang[k]) % (2 * mp.pi)) * 180 / mp.pi) for k in range(10)]
Aact = [k for k in range(10) if abs(gaps_deg[k] - float(Ls * 180 / mp.pi)) < 1e-5]
Inact = [k for k in range(10) if k not in Aact]
W("active gaps A = %s ; inactive I = %s ; g_9 row max = %s" % (Aact, Inact, mp.nstr(max(abs(G[9, e]) for e in range(m)), 4)))

rows = A.rows + (len(Inact) - 1)
S = mp.matrix(rows, m)
for i in range(A.rows):
    for j in range(m):
        S[i, j] = A[i, j]
k0 = Inact[0]
for r, k in enumerate([k for k in Inact if k != k0]):
    for j in range(m):
        S[A.rows + r, j] = G[k, j] - G[k0, j]
Gt = S.T * S
E, V = mp.eigsy(Gt)
sv = [mp.sqrt(max(v, mp.mpf(0))) for v in E]
W("differences system: %d x %d ; smallest sv = %s" % (S.rows, m, [mp.nstr(v, 8) for v in sv[:3]]))
rank = sum(1 for v in sv if v > mp.mpf('1e-22') * sv[-1])
W("rank = %d => nullity = %d" % (rank, m - rank))

feasible = []
for j in range(m - rank):
    vec = [V[i, j] for i in range(m)]
    s = sum(vec)
    if abs(s) < mp.mpf('1e-30'):
        W("   kernel %d: Σ=0 (scale-free direction) — skipped" % j)
        continue
    a = [v / s for v in vec]
    if min(a) < -mp.mpf('1e-25'):
        W("   kernel %d: 归一化后含负元 (min=%s) — 非可行" % (j, mp.nstr(min(a), 6)))
        continue
    a = [max(v, mp.mpf(0)) for v in a]
    # verify A a = 0 and g constant on I
    resA = max(abs(sum(A[i, e] * a[e] for e in range(m))) for i in range(A.rows))
    gI = [sum(G[k, e] * a[e] for e in range(m)) for k in range(10)]
    c = gI[k0]
    spread = max(abs(gI[k] - c) for k in Inact)
    act_vals = [(k, gI[k] - c) for k in Aact]
    W("   kernel %d: support=%d  |Aa|max=%.2e  g_I spread=%.2e  c=%+.6e" %
      (j, sum(1 for v in a if v > mp.mpf('1e-12')), float(resA), float(spread), float(c)))
    W("      active g_k - c: %s   (需要 <= 0)" % [(k, round(float(v), 8)) for k, v in act_vals])
    ok = (resA < mp.mpf('1e-25')) and (spread < mp.mpf('1e-25')) and all(v <= mp.mpf('1e-25') for _, v in act_vals)
    W("      KKT 可行: %s" % ok)
    if ok:
        # Schur + M margin
        from n14_cone_exact import schur_q, lam_min_M
        q = schur_q(net, [float(v) for v in a])
        lam, eigs = lam_min_M(net, q)
        W("      -> lambda_min(M|1perp) = %+.6e ; q nonzero=%d" % (lam, sum(1 for v in q.values() if abs(v) > 1e-18)))
        feasible.append({'kernel': j, 'support': sum(1 for v in a if v > mp.mpf('1e-12')),
                         'lambda_min_1perp': lam, 'q_nonzero': sum(1 for v in q.values() if abs(v) > 1e-18)})

W("")
W("=> 14-face(r*-cap) KKT: 可行核向量 %d 个" % len(feasible))
json.dump({'active_gaps': Aact, 'nullity': m - rank, 'feasible_kernels': feasible,
           'gaps_deg': gaps_deg, 'L_cap_deg': float(Ls * 180 / mp.pi)},
          open(Path(__file__).resolve().parents[1] / 'evidence' / 'n14-kkt-final.json', 'w'), indent=1)
Path(Path(__file__).resolve().parents[1] / 'logs' / 'n14_kkt_final.txt').write_text("\n".join(OUT), encoding='utf-8')
print("\nwrote logs/n14_kkt_final.txt")
