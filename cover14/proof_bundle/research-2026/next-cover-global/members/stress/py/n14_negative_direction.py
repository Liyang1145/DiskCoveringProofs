"""n14_negative_direction.py — 定位 M|1^perp 负方向的来源与路线选项。

内容：
  1. 16-face 网络的锥应力（含 torque）→ q 按 label 距离分布（多少质量落在 d=5）。
  2. M 用 c5=-1（全局有效但粗糙）vs c5=cos(实际角)（仅局部参考）vs c5=0 vs 精确局部 Hessian：
     比较 λ_min(M|1^perp)，判定负方向是否只由 d=5 系数造成。
  3. 输出负特征向量的支撑结构（哪些锚/对贡献）。
"""
import json
import sys
from pathlib import Path

import numpy as np
import mpmath as mp

mp.mp.dps = 50
sys.path.insert(0, str(Path(__file__).resolve().parent))
from stress_core import Net, cos_minorants, L_and_defect   # noqa: E402
import n14_extract as X                                    # noqa: E402
from n14_stress_cone import build, equilibrium_matrix      # noqa: E402
from n14_stress_cone2 import torque_matrix                 # noqa: E402

U = '0.33173203427623414'
OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

th, R, C = X.load()
active, anchors, owners = X.arcs_and_anchors(C, R)
faces = X.voronoi_faces(C, R)
net = build(faces)                       # all 16 faces
A = equilibrium_matrix(net); T = torque_matrix(net)
m = len(net.edges)
from scipy.optimize import linprog
Aeq = np.vstack([A, T, np.ones((1, m))]); beq = np.zeros(Aeq.shape[0]); beq[-1] = 1.0
res = linprog(np.zeros(m), A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * m, method='highs')
alpha = np.clip(res.x, 0, None)
W("cone stress: support %d/%d, min %.3e, max %.3e" % (int((alpha > 1e-12).sum()), m, alpha.min(), alpha.max()))

# q with the supported-node elimination (reuse the shared helper)
from n14_stress_cone import schur_nonneg
q, supported = schur_nonneg(net, alpha)
lab = lambda i, j: min(abs(i - j), net.na - abs(i - j))
by_d = {}
for (i, j), v in q.items():
    by_d.setdefault(lab(i, j), []).append(float(v))
W("q by label distance: " + "  ".join("d=%d n=%d sum=%.4e max=%.4e" % (d, len(v), sum(v), max(v))
                                      for d, v in sorted(by_d.items())))

ang = [mp.atan2(a[1], a[0]) for a in anchors]
cd = cos_minorants(U, 4)
L, defect = L_and_defect(U)
W("L=%s  5L=%s > pi ? %s" % (mp.nstr(L, 12), mp.nstr(5 * L, 12), 5 * L > mp.pi))


def build_M(cfun, tag):
    M = [[mp.mpf(0)] * net.na for _ in range(net.na)]
    for (i, j), qq in q.items():
        d = lab(i, j)
        c = cfun(i, j, d)
        if c is None:
            continue
        v = 2 * qq * c
        M[i][i] += v; M[j][j] += v; M[i][j] -= v; M[j][i] -= v
    # eigenvalues on 1^perp via Gram basis, plus the eigenvector
    G = mp.matrix(net.na - 1, net.na - 1)
    for k in range(1, net.na):
        for l in range(1, net.na):
            G[k - 1, l - 1] = M[0][0] - M[0][l] - M[k][0] + M[k][l]
    E, V = mp.eigsy(G)
    lam = E[0]
    w = [V[i, 0] for i in range(net.na - 1)]
    sup = [i + 1 for i in range(net.na - 1) if abs(w[i]) > 0.15 * max(abs(x) for x in w)]
    W("  %-28s lambda_min(M|1perp) = %+.6e   neg-eigvec support anchors(excl.0): %s"
      % (tag, float(lam), sup))
    return float(lam), sup


c_exact = {d: mp.mpf(float(v)) for d, v in cd.items()}
lam1, sup1 = build_M(lambda i, j, d: c_exact[d] if d <= 4 else mp.mpf(-1), 'c5=-1 (valid global)')
lam2, sup2 = build_M(lambda i, j, d: c_exact[d] if d <= 4 else mp.cos(ang[i] - ang[j]), 'c5=cos(actual) (local ref)')
lam3, sup3 = build_M(lambda i, j, d: c_exact[d] if d <= 4 else mp.mpf(0), 'c5=0 (reference)')
lam4, sup4 = build_M(lambda i, j, d: c_exact[d] if d <= 4 else mp.mpf(-1) * 0 + mp.mpf(1), 'c5=+1 (reference)')
W("  q mass on d=5 pairs: %.4e ; on d<=4: %.4e" % (sum(by_d.get(5, [0])), sum(sum(v) for d, v in by_d.items() if d <= 4)))

# exact local Hessian at the candidate (real angles, same q)
H = [[mp.mpf(0)] * net.na for _ in range(net.na)]
for (i, j), qq in q.items():
    c = mp.cos(ang[i] - ang[j])
    v = 2 * qq * c
    H[i][i] += v; H[j][j] += v; H[i][j] -= v; H[j][i] -= v
HG = mp.matrix(net.na - 1, net.na - 1)
for k in range(1, net.na):
    for l in range(1, net.na):
        HG[k - 1, l - 1] = H[0][0] - H[0][l] - H[k][0] + H[k][l]
EH, VH = mp.eigsy(HG)
W("  exact local Hessian H(theta*) on 1^perp: lambda_min = %+.6e ; full list %s"
  % (float(EH[0]), [round(float(v), 8) for v in EH]))
W("  (d=5 pairs' actual angles at candidate, deg: %s)"
  % [round(float((ang[i] - ang[j]) * 180 / mp.pi), 3) for (i, j) in q if lab(i, j) == 5])

json.dump({'support': int((alpha > 1e-12).sum()), 'q_by_d': {str(d): [len(v), sum(v)] for d, v in by_d.items()},
           'lam_c5_minus1': lam1, 'lam_c5_actual': lam2, 'lam_c5_zero': lam3, 'lam_c5_plus1': lam4,
           'negvec_support_c5m1': sup1, 'localH_lambda_min': float(EH[0]),
           'localH_eig': [float(v) for v in EH], 'L': float(L), '5L': float(5 * L)},
          open(Path(__file__).resolve().parents[1] / 'evidence' / 'negative-direction.json', 'w'), indent=1)
Path(Path(__file__).resolve().parents[1] / 'logs' / 'n14_negative_direction.txt').write_text("\n".join(OUT), encoding='utf-8')
print("\nwrote logs/n14_negative_direction.txt")
