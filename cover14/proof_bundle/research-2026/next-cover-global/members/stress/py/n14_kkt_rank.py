"""n14_kkt_rank.py — KKT 可行性判定（高精度，决定性）。

Lead 更正后的正确条件（r*-cap，active gaps A={4,9}，inactive I 含 0）：
    α >= 0, Σα = 1, A α = 0 (自由节点平衡),
    g_k(α) = 0  (k ∈ I),   g_k(α) <= 0  (k ∈ A)
其中 g_k = τ_0 + Σ_{i=k+1..9} τ_i ,  τ = −2 T α 。
（因 g_0 = Σ_{i=0..9} τ_i = 0 恒等（旋转不变），故 c=0。）

本脚本：以 mpmath dps=60 直接重建 A/g 行，计算 63×62 齐次系统的奇异值与零空间，
判断是否存在非零非负解；并给出最小二乘违反量。
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

# ---- mpmath A and T
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

# ---- g rows (linear in alpha): g_k = sum_{i=k+1..9} tau_i ,  tau_i = -2 T_i .
# (delta theta_i = sum_{k<i} delta Delta_k  and  delta theta_10 = 0  =>  no tau_0 term;
#  g is defined up to an additive constant, absorbed by the multiplier nu.)
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
W("active gaps A = %s ; inactive I = %s" % (Aact, Inact))
W("check g_9 row (should be identically zero): max |g_9| = %s" % mp.nstr(max(abs(G[9, e]) for e in range(m)), 5))

S = mp.matrix(A.rows + len(Inact), m)
for i in range(A.rows):
    for j in range(m):
        S[i, j] = A[i, j]
for r, k in enumerate(Inact):
    for j in range(m):
        S[A.rows + r, j] = G[k, j]
W("homogeneous system [A ; g_I] : %d x %d" % (S.rows, S.cols))
Gt = S.T * S
ev = mp.eigsy(Gt, eigvals_only=True)
sv = [mp.sqrt(max(v, mp.mpf(0))) for v in ev]
W("smallest 5 singular values: %s" % [mp.nstr(v, 8) for v in sv[:5]])
rank = sum(1 for v in sv if v > mp.mpf('1e-22') * sv[-1])
W("rank = %d / %d  => nullity = %d" % (rank, m, m - rank))
if m - rank > 0:
    # nullspace from the eigen-decomposition of S^T S (smallest eigenvalues)
    E, V = mp.eigsy(Gt)
    W("=> 非零解存在；检查非负性与 active 不等式")
    for j in range(m - rank):
        vec = [V[i, j] for i in range(m)]
        nz = [v for v in vec if abs(v) > 1e-12 * max(abs(x) for x in vec)]
        sign = 'mixed' if (min(nz) < 0 < max(nz)) else ('nonneg' if min(nz) >= 0 else 'nonpos')
        W("   nullvec %d: sign=%s  #nonzero=%d" % (j, sign, len(nz)))
else:
    W("=> 齐次系统满列秩：**不存在非零应力**满足 r*-域 KKT（连非负性都不需要）")

# least-squares violation over the simplex (numeric, method-limitation metric)
Anp = np.array([[float(A[i, j]) for j in range(m)] for i in range(A.rows)])
Snp = np.array([[float(S[i, j]) for j in range(m)] for i in range(S.rows)])
from scipy.optimize import minimize
def obj(x):
    r = Snp @ x
    return float(r @ r)
cons = ({'type': 'eq', 'fun': lambda x: x.sum() - 1.0},)
res = minimize(obj, np.full(m, 1.0 / m), constraints=cons, bounds=[(0, None)] * m,
               method='SLSQP', options={'maxiter': 800, 'ftol': 1e-22})
r = Snp @ res.x
W("")
W("在 {α>=0, Σα=1} 上的最小二乘违反：||[A;g_I]α||₂ = %.6e  (||Aα||=%.3e, max|g_I|=%.3e)"
  % (np.linalg.norm(r), np.linalg.norm(Anp @ res.x), max(abs(r[Anp.shape[0]:])) if len(r) > Anp.shape[0] else 0))
W("   support=%d ; （该值远大于 1e-15 即表示 KKT 精确不可行；~1e-16 表示可行）" % int((res.x > 1e-12).sum()))

json.dump({'nullity': m - rank, 'sv_smallest5': [mp.nstr(v, 10) for v in sv[:5]],
           'active_gaps': Aact, 'ls_violation': float(np.linalg.norm(r)),
           'ls_violation_A': float(np.linalg.norm(Anp @ res.x))},
          open(Path(__file__).resolve().parents[1] / 'evidence' / 'n14-kkt-rank.json', 'w'), indent=1)
Path(Path(__file__).resolve().parents[1] / 'logs' / 'n14_kkt_rank.txt').write_text("\n".join(OUT), encoding='utf-8')
print("\nwrote logs/n14_kkt_rank.txt")
