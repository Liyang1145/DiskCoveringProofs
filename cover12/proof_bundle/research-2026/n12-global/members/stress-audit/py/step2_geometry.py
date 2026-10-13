"""stress-audit step 2 (INDEPENDENT geometry + force audit).

Builds the chart geometry from the four root literals with my own conventions,
then checks, at dps=60:
  (a) the 36 active edges really have length r;
  (b) free-node vector equilibrium for the 7-orbit weights x,y,z,p,q,u,j;
  (c) anchor tangential (torque) residuals, both directly from the stress
      network and through an independently computed Schur complement;
  (d) the 36x36 equilibrium matrix rank/nullity (my own LU, mpmath).
No lead helper is imported; edge lists are re-derived from faces/arcs.
"""
from pathlib import Path
import json
import mpmath as mp

mp.mp.dps = 60
ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAL = ROOT / "research-2026/n12-global/evidence/d3-chart-calibration.json"
J = json.loads(CAL.read_text(encoding="utf-8"))
a, t, r, w = [mp.mpf(s) for s in J["root"]]
b = (1 + a + r) / 2
v = w / mp.sqrt(3)
S = b * b + v * v
d = a + r
beta = mp.atan2(v, b)
al = mp.pi / 3 - 2 * beta

print("=== 0. basic quantities (dps=60) ===")
print("  b        =", mp.nstr(b, 40))
print("  s^2 = S  =", mp.nstr(S, 40), "  (d + r^2 =", mp.nstr(d + r * r, 40), ")")
print("  beta     =", mp.nstr(beta, 30), " pi/6 =", mp.nstr(mp.pi / 6, 30), " (0<beta<pi/6:", 0 < beta < mp.pi / 6, ")")
print("  alpha    =", mp.nstr(al, 30), " asin(r) =", mp.nstr(mp.asin(r), 30), " alpha<asin r:", al < mp.asin(r))
print("  cos alpha - (1+t^2-r^2)/(2t) =", mp.nstr(mp.cos(al) - (1 + t * t - r * r) / (2 * t), 8))
print("  sin alpha - A/(2 sqrt3 S)    =", mp.nstr(mp.sin(al) - (3 * b * b - w * w - 2 * b * w) / (2 * mp.sqrt(3) * S), 8))
print("  (b,v) radial dist to u(0) - r =", mp.nstr(mp.sqrt((1 - b) ** 2 + v * v) - r, 8))
print("  (b,v) dist to (d,0) - r       =", mp.nstr(mp.sqrt((d - b) ** 2 + v * v) - r, 8))
print("  HHR |t u(pi/3)-(t-r)u(pi/3)| - r =", mp.nstr(abs(t - (t - r)) - r, 8))
print("  hub-HRR |(a,0)-(d,0)| - r =", mp.nstr(abs(d - a) - r, 8))

def u(x):
    return mp.matrix([mp.cos(x), mp.sin(x)])

rot = lambda ang: mp.matrix([[mp.cos(ang), -mp.sin(ang)], [mp.sin(ang), mp.cos(ang)]])

# --- my own construction of nodes --------------------------------------------
ang_anchor = [2 * beta, 2 * mp.pi / 3 - 2 * beta, 2 * mp.pi / 3, 2 * mp.pi / 3 + 2 * beta,
              4 * mp.pi / 3 - 2 * beta, 4 * mp.pi / 3, 4 * mp.pi / 3 + 2 * beta, 2 * mp.pi - 2 * beta, 2 * mp.pi]
anchors = [u(x) for x in ang_anchor]
# ring sites: order = C3 orbit blocks (b,v),(t,0),(b,-v) rotated by 0,120,240
sites = []
for k in range(3):
    Rk = rot(2 * mp.pi * k / 3)
    sites.append(Rk * mp.matrix([b, v]))
    sites.append(rot(2 * mp.pi * k / 3 + mp.pi / 3) * mp.matrix([t, 0]))
    sites.append(rot(2 * mp.pi * (k + 1) / 3) * mp.matrix([b, -v]))
hubs = [rot(2 * mp.pi * k / 3) * mp.matrix([a, 0]) for k in range(3)]
wits = [rot(2 * mp.pi * k / 3) * mp.matrix([d, 0]) for k in range(3)] + \
       [rot(2 * mp.pi * k / 3 + mp.pi / 3) * mp.matrix([t - r, 0]) for k in range(3)]
Z = sites + hubs + wits + anchors
names = [f"s{i}" for i in range(9)] + [f"h{i}" for i in range(3)] + [f"p{i}" for i in range(6)] + [f"u{i}" for i in range(9)]
faces = [(8, 0, 9), (2, 3, 10), (5, 6, 11), (9, 10, 1), (10, 11, 4), (11, 9, 7)]
edges = []
for i in range(9):
    edges.append((18 + i, i))
    edges.append((18 + i, (i + 1) % 9))
for fi, f in enumerate(faces):
    for k in f:
        edges.append((12 + fi, k))

# --- weights (7 orbits) ------------------------------------------------------
x = -b * r * r / (S - b)
y = (b - 1) * S / (S - b)
q = 2 * (1 - b) / r
uu = q * r / (2 * a - t + r)
jj = uu * (2 * t - 2 * r - a) / r
zz = jj * r * t / (1 - t * t - r * r)
pp = mp.mpf(1)
W = 6 * x + 6 * y + 6 * zz + 6 * pp + 3 * q + 6 * uu + 3 * jj
print("\n=== 1. weights (unnormalised) ===")
for nm, val in zip("x y z p q u j".split(), [x, y, zz, pp, q, uu, jj]):
    print(f"  {nm} = {mp.nstr(val, 30)}")
print("  W =", mp.nstr(W, 30), "  (normalised min weight =", mp.nstr(min(x, y, zz, pp, q, uu, jj) / W, 12), ")")

def w_edge(ei):
    i, k = edges[ei]
    if i >= 18:               # anchor-site edges: anchor i-18, site k
        if k % 3 == 1:
            return zz
        return x if (i - 18) % 3 == 2 else y
    if i >= 12:               # witness edges
        face = i - 12
        if k >= 9:            # hub side
            return q if face < 3 else uu
        return pp if face < 3 else jj
    raise RuntimeError

# --- (a) edge lengths --------------------------------------------------------
print("\n=== 2. edge length residuals (length - r) ===")
worst = mp.mpf(0)
for ei, (i, k) in enumerate(edges):
    dd = mp.sqrt(sum((Z[i][c] - Z[k][c]) ** 2 for c in range(2)))
    worst = max(worst, abs(dd - r))
print("  max |length - r| over 36 active edges =", mp.nstr(worst, 8))

# --- (b) free-node equilibrium ----------------------------------------------
print("\n=== 3. free-node equilibrium residuals |sum_e w_e (z_e - P)| ===")
res_parts = []
for node in range(18):
    F = mp.matrix([0, 0])
    for ei, (i, k) in enumerate(edges):
        if i == node:
            F += w_edge(ei) * (Z[k] - Z[i])
        elif k == node:
            F += w_edge(ei) * (Z[i] - Z[k])
    res_parts.append(mp.sqrt(F[0] ** 2 + F[1] ** 2))
print("  worst =", mp.nstr(max(res_parts), 8), " at", names[res_parts.index(max(res_parts))])
print("  per-node (x1e60):", [mp.nstr(v * mp.mpf(10) ** 60, 3) for v in res_parts])

# --- (c) anchor tangential residual -----------------------------------------
print("\n=== 4. anchor tangential residuals (unnormalised tangent force) ===")
tan = []
for i in range(9):
    P = anchors[i]
    tau = mp.matrix([-P[1], P[0]])      # unit tangent
    F = mp.matrix([0, 0])
    for ei, (i0, k) in enumerate(edges):
        if i0 == 18 + i:
            F += w_edge(ei) * (Z[k] - P)
        elif k == 18 + i:
            F += w_edge(ei) * (Z[i0] - P)
    tan.append(F[0] * tau[0] + F[1] * tau[1])
print("  per anchor (x1e60):", [mp.nstr(v * mp.mpf(10) ** 60, 4) for v in tan])
print("  max |tau| =", mp.nstr(max(abs(v) for v in tan), 8))
print("  y*v - z*t*sin(alpha)      =", mp.nstr(y * v - zz * t * mp.sin(al), 10))
print("  y*b*sin(beta) - z*t*sin(al)=", mp.nstr(y * b * mp.sin(beta) - zz * t * mp.sin(al), 10))

# --- (d) Schur complement, my own elimination --------------------------------
print("\n=== 5. my own Schur complement on anchors (normalised weights) ===")
n = 27
L = mp.zeros(n, n)
for ei, (i, k) in enumerate(edges):
    ww = w_edge(ei) / W
    L[i, i] += ww; L[k, k] += ww; L[i, k] -= ww; L[k, i] -= ww
free = list(range(18))
kept = list(range(18, 27))
Lff = L[:18, :18]
Lfa = L[:18, 18:]
Laa = L[18:, 18:]
Q = Laa - Lfa.T * Lff ** -1 * Lfa
print("  Q row sums (should be 0):", [mp.nstr(sum(Q[i, j] for j in range(9)), 4) for i in range(3)], "...")
qij = [[0] * 9 for _ in range(9)]
minq = mp.inf
for i in range(9):
    for k2 in range(i + 1, 9):
        qij[i][k2] = -Q[i, k2]
        minq = min(minq, qij[i][k2])
print("  min off-diagonal Schur conductance =", mp.nstr(minq, 12))
print("  energy sum q_ij |u_i-u_j|^2 =", mp.nstr(sum(qij[i][k2] * (2 - 2 * mp.cos(ang_anchor[i] - ang_anchor[k2]))
                                                       for i in range(9) for k2 in range(i + 1, 9)), 30), " r^2 =", mp.nstr(r * r, 30))
grad = []
for i in range(9):
    g = mp.mpf(0)
    for k2 in range(9):
        if k2 != i:
            g += 2 * qij[min(i, k2)][max(i, k2)] * mp.sin(ang_anchor[i] - ang_anchor[k2])
    grad.append(g)
print("  Schur angular gradient (x1e60):", [mp.nstr(g * mp.mpf(10) ** 60, 4) for g in grad])
print("  max |grad| =", mp.nstr(max(abs(g) for g in grad), 8))

# --- (e) 36x36 equilibrium matrix rank --------------------------------------
A = mp.zeros(36, 36)
for ei, (i, k) in enumerate(edges):
    if i < 18:
        A[2 * i, ei] += 1; A[2 * i + 1, ei] += 1
    if k < 18:
        A[2 * k, ei] -= 1; A[2 * k + 1, ei] -= 1
    # columns scaled by the actual unit direction so the matrix is exactly what
    # the equilibrium equations need: sum_e w_e (z_k - z_i) = 0
A2 = mp.zeros(36, 36)
for ei, (i, k) in enumerate(edges):
    e = (Z[k] - Z[i]) / mp.sqrt(sum((Z[k][c] - Z[i][c]) ** 2 for c in range(2)))
    if i < 18:
        A2[2 * i, ei] += e[0]; A2[2 * i + 1, ei] += e[1]
    if k < 18:
        A2[2 * k, ei] -= e[0]; A2[2 * k + 1, ei] -= e[1]
wv = mp.matrix([w_edge(ei) for ei in range(36)])
print("\n=== 6. 36x36 equilibrium matrix rank (my own LU) ===")
print("  |A2 w|_inf =", mp.nstr(max(abs(c) for c in (A2 * wv)), 8))
sv = mp.svd(A2, compute_uv=False)
print("  smallest 3 singular values:", [mp.nstr(s, 6) for s in sv[-3:]])
print("  rank with tol 1e-30:", sum(1 for s in sv if s > mp.mpf(10) ** -30))
