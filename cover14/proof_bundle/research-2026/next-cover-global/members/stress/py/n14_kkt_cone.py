"""n14_kkt_cone.py — 修正后的应力/stationarity 判定（采纳 Lead 更正）。

要点：
  * 候选的 ±x ring（s=√(1−r²)）**owning arc 恰为 2·asin r** ⇒ 在该 r 域里 **两条 gap 顶到 cap** ⇒
    stationarity 不是 Tα=0（内点零梯度），而是 capped-simplex 的 KKT：
        g_k := ∂E/∂Δ_k = τ_0 + Σ_{i=k+1..9} τ_i ,  τ_i = −2 (Tα)_i
        存在 c:  g_k = c (inactive k) ,  g_k ≤ c (active k) .
    （n12 全 gap 内点 ⇒ g≡0 ⇒ τ≡0，正是那边 T=0 恒等式。）
  * cap 取 sharp 值 L* = 2·asin(r*)（r* = hprec_sol 的 R），而非 2·asin(U)：
    U-域里候选是内点 ⇒ 需 τ=0（可能不存在，属方法限制，不是判死）；r*-域里 cap 活跃 ⇒ 只需 KKT。
  * 图取 **14 active faces**（16-face 的两条 slack 三边权重必须为 0，故不作为证书网络）。
输出：logs/n14_kkt_cone.txt, evidence/n14-kkt-cone.json（数值仅路线诊断）。
"""
import json
import sys
from pathlib import Path

import numpy as np
import mpmath as mp

mp.mp.dps = 60
sys.path.insert(0, str(Path(__file__).resolve().parent))
from stress_core import Net, cos_minorants      # noqa: E402
import n14_extract as X                          # noqa: E402
from n14_cone_exact import make_net, eq_matrix, tor_matrix, schur_q, lam_min_M   # noqa: E402

OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

th, R, C = X.load()
rstar = R
mp.mp.dps = 60
Ls = 2 * mp.asin(rstar)                     # sharp cap (r*-domain)
LU = 2 * mp.asin(mp.mpf('0.33173203427623414'))
W("r* = %s" % mp.nstr(rstar, 30))
W("L* = 2 asin(r*) = %s ;  L_U = 2 asin(U) = %s ;  L_U - L* = %s"
  % (mp.nstr(Ls, 25), mp.nstr(LU, 25), mp.nstr(LU - Ls, 6)))

active, anchors, owners = X.arcs_and_anchors(C, R)
faces = X.voronoi_faces(C, R)
act_faces = [f for f in faces if f[3]]
net = make_net(act_faces, anchors, owners, C)
A = eq_matrix(net); T = tor_matrix(net)
m = len(net.edges)
ang = [mp.atan2(a[1], a[0]) % (2 * mp.pi) for a in anchors]
gaps = [float(((ang[(k + 1) % 10] - ang[k]) % (2 * mp.pi)) * 180 / mp.pi) for k in range(10)]
W("anchor gaps (deg): %s" % [round(g, 6) for g in gaps])
W("cap L* in deg = %.9f ; active gaps (within 1e-9 deg of cap): %s"
  % (float(Ls * 180 / mp.pi), [k for k in range(10) if abs(gaps[k] - float(Ls * 180 / mp.pi)) < 1e-5]))
Aact = [k for k in range(10) if abs(gaps[k] - float(Ls * 180 / mp.pi)) < 1e-5]
Inact = [k for k in range(10) if k not in Aact]
W("active set A = %s ; inactive I = %s" % (Aact, Inact))

# g = suffix sums of tau (tau_i = -2 (T alpha)_i), with tau_10 := tau_0
def g_of(alpha):
    tau = -2.0 * (T @ alpha)
    tau10 = tau[0]
    g = np.array([tau[0] + tau[k + 1:].sum() for k in range(10)])   # k=0..9 : sum_{i>=k+1} tau_i + tau_0
    return g, tau

from scipy.optimize import linprog
# KKT rows: g_k - c = 0 for k in I ; g_k - c <= 0 for k in A
rows_eq, rows_le = [], []
Gmat = np.zeros((10, m))
for e in range(m):
    t = np.zeros(m); t[e] = 1.0
    Gmat[:, e], _ = g_of(t)     # g is linear in alpha
for k in Inact:
    r = np.zeros(m + 1); r[:m] = Gmat[k]; r[m] = -1.0
    rows_eq.append(r)
for k in Aact:
    r = np.zeros(m + 1); r[:m] = Gmat[k]; r[m] = -1.0
    rows_le.append(r)
Aeq = np.zeros((A.shape[0] + len(rows_eq) + 1, m + 1))
Aeq[:A.shape[0], :m] = A
Aeq[A.shape[0]:A.shape[0] + len(rows_eq), :] = np.array(rows_eq)
Aeq[-1, :m] = 1.0
beq = np.zeros(Aeq.shape[0]); beq[-1] = 1.0
A_ub = np.array(rows_le) if rows_le else None
b_ub = np.zeros(len(rows_le)) if rows_le else None
bounds = [(0, None)] * m + [(None, None)]
res = linprog(np.zeros(m + 1), A_ub=A_ub, b_ub=b_ub, A_eq=Aeq, b_eq=beq, bounds=bounds, method='highs')
W("")
W("KKT cone (r*-cap) nonempty: %s (%s)" % (res.success, res.message[:70]))
if res.success:
    alpha = np.clip(res.x[:m], 0, None); c = res.x[m]
    g, tau = g_of(alpha)
    W("   solution: support=%d  min α=%.3e  max α=%.3e  c=%.3e" % (int((alpha > 1e-12).sum()), alpha.min(), alpha.max(), c))
    W("   g = %s" % [round(float(x), 6) for x in g])
    W("   active-gap g_k - c = %s ; inactive residuals g_k - c = %s"
      % ([round(float(g[k] - c), 8) for k in Aact], [round(float(g[k] - c), 8) for k in Inact]))
    q = schur_q(net, alpha)
    # c_d from the SHARP cap L*
    cdU = cos_minorants('0.33173203427623414', 4)
    cd = {d: mp.cos(d * Ls) for d in range(1, 5)}
    W("   c_d from L*: %s" % {d: round(float(v), 8) for d, v in cd.items()})
    lam, eigs = lam_min_M(net, q)
    W("   lambda_min(M|1perp) with L* constants = %+.6e" % lam)
    W("   M|1perp eig head: %s" % [round(v, 7) for v in eigs[:5]])
    # also with the U-cap constants (slightly weaker)
    lamU, eigsU = lam_min_M(net, q)
    W("   (same stress, L* vs U constants: c1 %.10f vs %.10f)" % (float(cd[1]), float(cdU[1])))
    json.dump({'kkt_feasible': True, 'support': int((alpha > 1e-12).sum()), 'c': float(c),
               'alpha': [float(x) for x in alpha], 'g': [float(x) for x in g],
               'active_gaps': Aact, 'lambda_min_1perp_Lstar': lam,
               'eig_1perp_Lstar': eigs, 'gaps_deg': gaps},
              open(Path(__file__).resolve().parents[1] / 'evidence' / 'n14-kkt-cone.json', 'w'), indent=1)
else:
    # diagnose: least-squares KKT residual
    W("   -> 记录方法限制：在 L* 域 KKT 锥空。后续可用软约束/权重扫描量化最小违反量。")
    json.dump({'kkt_feasible': False, 'active_gaps': Aact, 'gaps_deg': gaps},
              open(Path(__file__).resolve().parents[1] / 'evidence' / 'n14-kkt-cone.json', 'w'), indent=1)

Path(Path(__file__).resolve().parents[1] / 'logs' / 'n14_kkt_cone.txt').write_text("\n".join(OUT), encoding='utf-8')
print("\nwrote logs/n14_kkt_cone.txt")
