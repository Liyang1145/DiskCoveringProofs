"""n14_subnet_search.py — 方法限制量化 + 活跃面子网络扫描（有界实验，非全面搜索）。

1) 对 14-face 网络量化 KKT 锥的最小违反（软 KKT，最小化违反量），给出"离可行多远"。
2) 对去掉 1..2 个活跃面的子网络（最多 1+14+91 个），检查 r*-域 KKT 锥是否非空，
   若非空则算 Schur q 与 λ_min(M|1⊥)，找是否存在"有正余量"的子网络（若存在，则 sharp 路线
   只需拓扑侧保证这些面的存在性）。
3) 也报告 slack 面三边是否为 0（Lead 指出 16-face 证书里 slack 三边必须 0）。
"""
import itertools
import json
import sys
from pathlib import Path

import numpy as np
import mpmath as mp

mp.mp.dps = 60
sys.path.insert(0, str(Path(__file__).resolve().parent))
from stress_core import cos_minorants      # noqa: E402
import n14_extract as X                    # noqa: E402
from n14_cone_exact import make_net, eq_matrix, tor_matrix, schur_q, lam_min_M   # noqa: E402

OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

th, R, C = X.load()
rstar = R
Ls = 2 * mp.asin(rstar)
active, anchors, owners = X.arcs_and_anchors(C, R)
faces = X.voronoi_faces(C, R)
act_faces = [f for f in faces if f[3]]
slack_faces = [f for f in faces if not f[3]]
W("active faces: %d ; slack faces: %d -> %s" % (len(act_faces), len(slack_faces),
                                                 [tuple(f[0]) for f in slack_faces]))
ang = [mp.atan2(a[1], a[0]) % (2 * mp.pi) for a in anchors]
gaps_deg = [float(((ang[(k + 1) % 10] - ang[k]) % (2 * mp.pi)) * 180 / mp.pi) for k in range(10)]
Aact = [k for k in range(10) if abs(gaps_deg[k] - float(Ls * 180 / mp.pi)) < 1e-5]
Inact = [k for k in range(10) if k not in Aact]
W("active gaps (cap) = %s ; cap = %.9f deg" % (Aact, float(Ls * 180 / mp.pi)))


def kkt_lp(net):
    A = eq_matrix(net); T = tor_matrix(net); m = len(net.edges)
    Gm = np.zeros((10, m))
    for e in range(m):
        t = np.zeros(m); t[e] = 1.0
        tau = -2.0 * (T @ t)
        Gm[:, e] = [tau[0] + tau[k + 1:].sum() for k in range(10)]
    rows_eq = np.zeros((len(Inact), m + 1))
    for i, k in enumerate(Inact):
        rows_eq[i, :m] = Gm[k]; rows_eq[i, m] = -1.0
    rows_le = np.zeros((len(Aact), m + 1))
    for i, k in enumerate(Aact):
        rows_le[i, :m] = Gm[k]; rows_le[i, m] = -1.0
    Aeq = np.vstack([np.c_[A, np.zeros(A.shape[0])], rows_eq, np.r_[np.ones(m), 0.0][None, :]])
    beq = np.zeros(Aeq.shape[0]); beq[-1] = 1.0
    return A, T, Aeq, beq, rows_le, m


from scipy.optimize import linprog


def feas(net):
    A, T, Aeq, beq, rows_le, m = kkt_lp(net)
    res = linprog(np.zeros(m + 1), A_ub=rows_le, b_ub=np.zeros(len(Aact)), A_eq=Aeq, b_eq=beq,
                  bounds=[(0, None)] * m + [(None, None)], method='highs')
    if res.success:
        a = np.clip(res.x[:m], 0, None)
        q = schur_q(net, a)
        lam, eigs = lam_min_M(net, q)
        return True, a, q, lam, eigs
    return False, None, None, None, None


def soft_kkt(net):
    """min z s.t. alpha>=0, sum=1, Aa=0, |g_k - c| <= z (inactive), g_k - c <= z (active)."""
    A, T, Aeq0, beq, rows_le, m = kkt_lp(net)
    # variables: alpha(m), c(1), z(1)
    Aeq = np.zeros((A.shape[0] + 1, m + 2))
    Aeq[:A.shape[0], :m] = A
    Aeq[-1, :m] = 1.0
    beq2 = np.zeros(Aeq.shape[0]); beq2[-1] = 1.0
    G = np.zeros((len(Inact), m))
    for i, k in enumerate(Inact):
        G[i] = rows_le[i, :m] if False else 0
    # rebuild g rows for inactive equalities
    Gm = np.zeros((10, m))
    for e in range(m):
        t = np.zeros(m); t[e] = 1.0
        tau = -2.0 * (T @ t)
        Gm[:, e] = [tau[0] + tau[k + 1:].sum() for k in range(10)]
    rows_ub = []
    for k in Inact:
        r1 = np.zeros(m + 2); r1[:m] = Gm[k]; r1[m] = -1.0; r1[m + 1] = -1.0; rows_ub.append(r1)
        r2 = np.zeros(m + 2); r2[:m] = -Gm[k]; r2[m] = 1.0; r2[m + 1] = -1.0; rows_ub.append(r2)
    for k in Aact:
        r = np.zeros(m + 2); r[:m] = Gm[k]; r[m] = -1.0; r[m + 1] = -1.0; rows_ub.append(r)
    c = np.zeros(m + 2); c[m + 1] = 1.0
    res = linprog(c, A_ub=np.array(rows_ub), b_ub=np.zeros(len(rows_ub)), A_eq=Aeq, b_eq=beq2,
                  bounds=[(0, None)] * m + [(None, None), (0, None)], method='highs')
    return (res.fun, res.x[:m] if res.success else None) if res.success else (float('nan'), None)


results = []
for k in (0, 1, 2):
    for drop in itertools.combinations(range(len(act_faces)), k):
        kept = [f for i, f in enumerate(act_faces) if i not in drop]
        net = make_net(kept, anchors, owners, C)
        ok, a, q, lam, eigs = feas(net)
        results.append((k, drop, ok, lam if ok else None, int((a > 1e-12).sum()) if ok else 0))
feasible = [r for r in results if r[2]]
W("")
W("=> 子网络扫描: 共 %d 个（k<=2），KKT 可行 %d 个" % (len(results), len(feasible)))
W("   可行计数按 k: %s" % {k: sum(1 for r in results if r[0] == k and r[2]) for k in (0, 1, 2)})
if feasible:
    best = max(feasible, key=lambda r: r[3])
    W("   最优 λ_min = %+.6e  (k=%d, drop=%s)" % (best[3], best[0], best[1]))
    W("   可行例（前 8）: %s" % [(r[0], r[1], round(r[3], 8)) for r in feasible[:8]])

# soft-KKT violation for the FULL 14-face network (method-limitation metric)
net14 = make_net(act_faces, anchors, owners, C)
z, a_soft = soft_kkt(net14)
W("")
W("== 14-face 网络的最小 KKT 违反量 z* = %.6e （α>=0,Σα=1,Aα=0 下 |g-c| 的最小可行上界）" % z)
if a_soft is not None:
    tau = -2.0 * (tor_matrix(net14) @ a_soft)
    g = np.array([tau[0] + tau[k + 1:].sum() for k in range(10)])
    W("   该软解的 g 范围 = [%.6e, %.6e] ; 要求 inactive 相等/active ≤ c（c 自由）" % (g.min(), g.max()))

json.dump({'n_checked': len(results), 'n_feasible': len(feasible),
           'rows': [{'k': r[0], 'drop': list(r[1]), 'feasible': bool(r[2]),
                     'lam_min_1perp': r[3], 'support': r[4]} for r in results],
           'soft_kkt_violation_full14': float(z), 'active_gaps': Aact,
           'slack_faces': [list(f[0]) for f in slack_faces]},
          open(Path(__file__).resolve().parents[1] / 'evidence' / 'n14-subnet-search.json', 'w'), indent=1)
Path(Path(__file__).resolve().parents[1] / 'logs' / 'n14_subnet_search.txt').write_text("\n".join(OUT), encoding='utf-8')
print("\nwrote logs/n14_subnet_search.txt")
