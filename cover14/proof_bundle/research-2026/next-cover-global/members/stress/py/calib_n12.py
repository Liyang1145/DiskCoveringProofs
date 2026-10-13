"""calib_n12.py — 用同一个 stress_core 复现 n12 已证候选的已知读数（只读校准）。

对照值（来自 n12 审计，members/stress-audit 与 evidence/candidate-stress-probe.json）：
  * 正应力存在；归一化后 min weight ≈ 0.0116599（probe 值）
  * min Schur conductance ≈ 6.684002e-05
  * M (c_d = T_d(1-2U12^2)) 在 1^perp 上的最小特征值 ≈ 2.366154692e-03
"""
import json
import sys
from pathlib import Path

import mpmath as mp

mp.mp.dps = 50
sys.path.insert(0, str(Path(__file__).resolve().parent))
from stress_core import Net, cos_minorants, eig_1perp      # noqa: E402

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
N12 = ROOT / "research-2026/n12-global"
U12 = mp.mpf('0.361102963744508672616920293904')

cal = json.loads((N12 / 'evidence/d3-chart-calibration.json').read_text(encoding='utf-8'))
a, t, r, w = [mp.mpf(s) for s in cal['root']]
b = (1 + a + r) / 2
S = b * b + w * w / 3
A = 3 * b * b - w * w - 2 * b * w
X = {'x': -b * r * r / (S - b), 'y': (b - 1) * S / (S - b), 'p': mp.mpf(1), 'q': 2 * (1 - b) / r}
X['u'] = X['q'] * r / (2 * a - t + r)
X['j'] = X['u'] * (2 * t - 2 * r - a) / r
X['z'] = X['j'] * r * t / (1 - t * t - r * r)
Wtot = 6 * X['x'] + 6 * X['y'] + 6 * X['z'] + 6 * X['p'] + 3 * X['q'] + 6 * X['u'] + 3 * X['j']
print('n12 weights (unnormalised):', {k: round(float(v), 8) for k, v in X.items()})
print('  normalised min weight = %.10f   (expected ~0.01165992192009)' % float(min(X.values()) / Wtot))

# geometry exactly as in the n12 probe
ang = [2 * mp.atan2(w / mp.sqrt(3), b), 2 * mp.pi / 3 - 2 * mp.atan2(w / mp.sqrt(3), b), 2 * mp.pi / 3,
       2 * mp.pi / 3 + 2 * mp.atan2(w / mp.sqrt(3), b), 4 * mp.pi / 3 - 2 * mp.atan2(w / mp.sqrt(3), b),
       4 * mp.pi / 3, 4 * mp.pi / 3 + 2 * mp.atan2(w / mp.sqrt(3), b), 2 * mp.pi - 2 * mp.atan2(w / mp.sqrt(3), b), 2 * mp.pi]
anchors = [(mp.cos(x), mp.sin(x)) for x in ang]
rot = lambda th: [(mp.cos(th), -mp.sin(th)), (mp.sin(th), mp.cos(th))]
sites = []
for k in range(3):
    Rk = rot(2 * mp.pi * k / 3)
    mv = lambda M, p: (M[0][0] * p[0] + M[0][1] * p[1], M[1][0] * p[0] + M[1][1] * p[1])
    sites.append(mv(Rk, (b, w / mp.sqrt(3))))
    sites.append(mv(rot(2 * mp.pi * k / 3 + mp.pi / 3), (t, 0)))
    sites.append(mv(rot(2 * mp.pi * (k + 1) / 3), (b, -w / mp.sqrt(3))))
hubs = [(mp.cos(2 * mp.pi * k / 3) * a, mp.sin(2 * mp.pi * k / 3) * a) for k in range(3)]
sites = sites + hubs
wits = [(mp.cos(2 * mp.pi * k / 3) * (a + r), mp.sin(2 * mp.pi * k / 3) * (a + r)) for k in range(3)] + \
       [(mp.cos(2 * mp.pi * k / 3 + mp.pi / 3) * (t - r), mp.sin(2 * mp.pi * k / 3 + mp.pi / 3) * (t - r)) for k in range(3)]
faces = [(8, 0, 9), (2, 3, 10), (5, 6, 11), (9, 10, 1), (10, 11, 4), (11, 9, 7)]   # witness k <-> sites

net = Net(anchors, sites, faces)
owners = [(i, (i + 1) % 9) for i in range(9)]      # n12: anchor i owns sites i and i+1
net.add_anchor_edges(owners)
net.add_face_edges(wits)
print('n12 network: anchors=%d sites=%d witnesses=%d edges=%d' % (net.na, net.ns, net.nf, len(net.edges)))

alpha, tmax = net.positive_stress()
print('  positive stress exists: %s (t_max=%.8f) ; min alpha=%.8f max=%.8f sum=%.12f'
      % (tmax > 0, tmax, alpha.min(), alpha.max(), alpha.sum()))
q = net.schur(alpha)
print('  Schur conductance: n=%d min=%.8e (expected 6.684002e-05)' % (len(q), min(q.values())))
lab = lambda i, j: min(abs(i - j), 9 - abs(i - j))
cd = cos_minorants('0.361102963744508672616920293904', 4)
c_by_d = {d: mp.mpf(float(v)) for d, v in cd.items()}
M, neg = net.M_from_q_and_labels(q, c_by_d, lab)
ev, ev1, lam = eig_1perp(M)
print('  M on 1^perp min eigenvalue = %.10e (expected 2.366154692e-03)' % lam)
print('  M eigenvalues on 1^perp: %s' % [round(v, 8) for v in ev1])
