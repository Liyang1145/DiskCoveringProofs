"""n14_portrait_stress.py — 独立画像：从 hprec_sol 的 7 参数按 verify_c407_lead.py:186-195
展开 14 中心，几何自建 10 边界锚 / 活动内孔图，再做应力 + Schur + 常数 Hessian 次式诊断。

明确不做：不读 candidate 的 REPORT-n13-14-15 / n14_dual.txt / n14_symmetry.txt（已被 Lead 判为索引错误），
只读 session2/type14/out/*.json（旧资产）作交叉参照（kkt 的 near 列表仅作对照，不参与构造）。

输出：logs/n14_portrait_stress.txt, evidence/n14-portrait-stress.json
数值仅路线诊断；不主张正定=证明。
"""
import json
import sys
from pathlib import Path

import mpmath as mp
import numpy as np

mp.mp.dps = 60
sys.path.insert(0, str(Path(__file__).resolve().parent))
from stress_core import Net, cos_minorants, L_and_defect, eig_1perp   # noqa: E402

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
T14 = ROOT / "research-2026/session2/type14/out"
U = '0.33173203427623414'            # C411 threshold (decimal as given by Lead)

OUT = []
def W(s=""):
    OUT.append(str(s))
    print(s)


# ---------------------------------------------------------------- 1. centers (authoritative expansion)
sol = json.loads((T14 / 'hprec_sol.json').read_text(encoding='utf-8'))
solr = json.loads((T14 / 'hprec_sol_refined.json').read_text(encoding='utf-8'))
th = [mp.mpf(s) for s in solr['th'][:7]]
R = mp.mpf(solr['R'])
W("== n14 portrait (independent) ==")
W("R (refined sol) = %s" % mp.nstr(R, 30))
W("th (7) = %s" % [mp.nstr(v, 12) for v in th])

C = []
for j in (0, 2):
    for s in (-1, 1):
        for t in (-1, 1):
            C.append((s * th[j], t * th[j + 1]))
for j in (4, 5):
    C.extend([(th[j], mp.mpf(0)), (-th[j], mp.mpf(0))])
C.extend([(mp.mpf(0), th[6]), (mp.mpf(0), -th[6])])
assert len(C) == 14
norm = lambda p: mp.sqrt(p[0] ** 2 + p[1] ** 2)
dd = lambda p, q: mp.sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)

W("")
W("### centers (verify_c407_lead expansion order)")
for i, c in enumerate(C):
    W("  %2d: (%s, %s)  |c|=%s  deg=%s" % (i, mp.nstr(c[0], 16), mp.nstr(c[1], 16),
                                           mp.nstr(norm(c), 12), mp.nstr(mp.atan2(c[1], c[0]) * 180 / mp.pi, 10)))

# ---------------------------------------------------------------- 2. D2 orbits (independent)
def orbit(c):
    pts = {(c[0], c[1]), (-c[0], c[1]), (c[0], -c[1]), (-c[0], -c[1])}
    idx = []
    for p in pts:
        for i, q in enumerate(C):
            if dd(p, q) < mp.mpf('1e-30'):
                idx.append(i); break
    return tuple(sorted(idx))

seen, orbits = set(), []
for i in range(14):
    o = orbit(C[i])
    if o not in seen:
        seen.add(o); orbits.append(o)
W("")
W("### D2 orbits (independent): sizes %s  total %d" % ([len(o) for o in orbits], sum(len(o) for o in orbits)))
for o in orbits:
    W("   orbit %s : |c|=%s" % (list(o), [mp.nstr(norm(C[i]), 10) for i in o]))
assert sum(len(o) for o in orbits) == 14

# ---------------------------------------------------------------- 3. boundary arcs / anchors
W("")
W("### boundary-active arcs and anchors")
active, inactive = [], []
for i, c in enumerate(C):
    (active if norm(c) + R >= 1 else inactive).append(i)
W("   boundary-active (%d): %s" % (len(active), active))
W("   inactive        (%d): %s" % (len(inactive), inactive))

endpoints = []          # (angle, site)
for i in active:
    ci = C[i]
    r = norm(ci)
    m = (1 + r * r - R * R) / (2 * r)
    assert -1 <= m <= 1, (i, float(m))
    psi = mp.acos(m)
    phi = mp.atan2(ci[1], ci[0])
    endpoints.append(((phi - psi) % (2 * mp.pi), i))
    endpoints.append(((phi + psi) % (2 * mp.pi), i))
endpoints.sort(key=lambda z: z[0])
# cluster coincident endpoints
clusters, cur = [], [endpoints[0]]
for e in endpoints[1:]:
    if abs(e[0] - cur[-1][0]) < mp.mpf('1e-25') or abs(e[0] - cur[-1][0] - 2 * mp.pi) < mp.mpf('1e-25'):
        cur.append(e)
    else:
        clusters.append(cur); cur = [e]
clusters.append(cur)
W("   arc endpoints clustered: %d clusters (sizes %s)" % (len(clusters), [len(c) for c in clusters]))
anchors, owners = [], []
for cl in clusters:
    ang = sum(e[0] for e in cl) / len(cl)
    sites = sorted({e[1] for e in cl})
    anchors.append((mp.cos(ang), mp.sin(ang)))
    owners.append(sites)
    if len(sites) != 2:
        W("   !! cluster with %d distinct owners at %.12f: %s" % (len(sites), float(ang), sites))
# check distances and arc tiling
maxerr = max(abs(dd(anchors[k], C[s]) - R) for k, ss in enumerate(owners) for s in ss)
W("   max | |anchor-site| - R | = %s" % mp.nstr(maxerr, 6))
# each active site owns exactly 2 anchors
from collections import Counter
cnt = Counter(s for ss in owners for s in ss)
W("   anchors per boundary site: %s" % dict(sorted(cnt.items())))
# order anchors cyclically
order = sorted(range(len(anchors)), key=lambda k: mp.atan2(anchors[k][1], anchors[k][0]) % (2 * mp.pi))
anchors = [anchors[k] for k in order]
owners = [owners[k] for k in order]
W("   anchor angles (deg, cyclic): %s" % [round(float(mp.atan2(a[1], a[0]) * 180 / mp.pi), 6) for a in anchors])
W("   anchor owners (cyclic): %s" % owners)
gaps = []
ang = [mp.atan2(a[1], a[0]) % (2 * mp.pi) for a in anchors]
for k in range(len(ang)):
    gaps.append((ang[(k + 1) % len(ang)] - ang[k]) % (2 * mp.pi))
L, defect = L_and_defect(U)
W("   anchor gaps (deg): %s" % [round(float(g * 180 / mp.pi), 6) for g in gaps])
W("   max gap = %s ; L = 2asinU = %s (deg %.6f) ; max gap <= L : %s"
  % (mp.nstr(max(gaps), 12), mp.nstr(L, 12), float(L * 180 / mp.pi), max(gaps) <= L))
W("   10L - 2pi = %s  (>0 : %s)   4L<pi : %s   5L<pi : %s"
  % (mp.nstr(defect, 12), defect > 0, 4 * L < mp.pi, 5 * L < mp.pi))

# ---------------------------------------------------------------- 4. Delaunay + in-D + empty-circle filter
W("")
W("### Delaunay (in-D Voronoi) filter for faces")
import itertools
faces_active, faces_slack = [], []
for tri in itertools.combinations(range(14), 3):
    p, q, s = (C[t] for t in tri)
    det = 2 * ((p[0] - s[0]) * (q[1] - s[1]) - (p[1] - s[1]) * (q[0] - s[0]))
    if abs(det) < mp.mpf('1e-40'):
        continue
    b1 = p[0] ** 2 + p[1] ** 2 - s[0] ** 2 - s[1] ** 2
    b2 = q[0] ** 2 + q[1] ** 2 - s[0] ** 2 - s[1] ** 2
    ux = (b1 * (q[1] - s[1]) - (p[1] - s[1]) * b2) / det
    uy = ((p[0] - s[0]) * b2 - b1 * (q[0] - s[0])) / det
    u = (ux, uy)
    if norm(u) > 1 + mp.mpf('1e-30'):
        continue
    d = dd(u, p)
    others = [dd(u, C[l]) for l in range(14) if l not in tri]
    if min(others) < d - mp.mpf('1e-20'):
        continue                      # not a Voronoi vertex (empty-circle fails)
    typ = ''.join('B' if t in active else 'H' for t in tri)
    rec = (tri, u, d, typ)
    (faces_active if abs(d - R) < mp.mpf('1e-14') else faces_slack).append(rec)
W("   Voronoi vertices in D : %d  (active %d, slack %d)"
  % (len(faces_active) + len(faces_slack), len(faces_active), len(faces_slack)))
W("   ACTIVE faces:")
for tri, u, d, typ in sorted(faces_active, key=lambda z: z[0]):
    W("     tri%-18s type=%-4s f-R=%s  |u|=%s" % (str(tuple(tri)), typ, mp.nstr(d - R, 4), mp.nstr(norm(u), 12)))
# orbit structure of active faces under D2 (map center indices by the mirror/c2 permutations derived from geometry)
def perm_of(g):
    pm = []
    for i, c in enumerate(C):
        img = g(c)
        best = min(range(14), key=lambda j: dd(img, C[j]))
        assert dd(img, C[best]) < mp.mpf('1e-30'), (i, g)
        pm.append(best)
    return tuple(pm)
perms = [perm_of(lambda c: (-c[0], -c[1])), perm_of(lambda c: (-c[0], c[1])), perm_of(lambda c: (c[0], -c[1]))]
def orbit_faces(tri):
    out = set()
    for pm in perms:
        out.add(tuple(sorted(pm[t] for t in tri)))
    return frozenset(out)
fseen, forbits = set(), []
for tri, u, d, typ in faces_active:
    o = orbit_faces(tri)
    if o not in fseen:
        fseen.add(o); forbits.append(o)
W("   active-face D2 orbits: %d  (sizes %s)" % (len(forbits), [len(o) for o in forbits]))
for o in forbits:
    W("     %s" % sorted(tuple(t) for t in o))

# ---------------------------------------------------------------- 5. graph + stress + Schur + M
W("")
W("### stress network: 10 anchors + 14 sites + %d active witnesses" % len(faces_active))
net = Net(anchors, C, [tri for tri, u, d, typ in faces_active])
net.add_anchor_edges([tuple(ss) for ss in owners])
net.add_face_edges([u for tri, u, d, typ in faces_active])
W("   nodes=%d edges=%d (anchor-site %d, witness-site %d)"
  % (net.na + net.ns + net.nf, len(net.edges), 2 * net.na, 3 * net.nf))
alpha, tpos = net.positive_stress()
if alpha is None:
    W("   !! positive stress LP failed")
else:
    W("   max common lower bound on edge weights t_max = %.10f  (positive stress exists: %s)"
      % (tpos, tpos > 0))
    W("   min/max alpha = %.8f / %.8f ; sum = %.12f" % (alpha.min(), alpha.max(), alpha.sum()))
q = net.schur(alpha)
W("   Schur conductances: n=%d ; min=%.8e" % (len(q), min(q.values())))
lab = lambda i, j: min(abs(i - j), net.na - abs(i - j))
by_d = {d: [] for d in range(1, net.na // 2 + 1)}
for (i, j), v in q.items():
    by_d[lab(i, j)].append(float(v))
W("   q by label distance: " + "  ".join("d=%d:n=%d,total=%.3e" % (d, len(v), sum(v)) for d, v in sorted(by_d.items())))

cd = cos_minorants(U, 4)          # exact rationals, valid while dL<pi (d<=4)
W("   c_d = T_d(1-2U^2): " + ", ".join("c%d=%.10f" % (d, float(cd[d])) for d in sorted(cd)))
c5 = -1                            # universal minorant for d=5 since 5L>pi: cos(min-arc) >= -1
W("   c5 = -1 (required: 5L = %.6f > pi = %.6f)" % (float(5 * L), float(mp.pi)))
c_by_d = dict(cd); c_by_d[5] = mp.mpf(c5)
M, neg = net.M_from_q_and_labels(q, c_by_d, lab)
ev_all, ev_1p, lam_min = eig_1perp(M)
W("   M eigenvalues (all 10): %s" % [round(v, 8) for v in ev_all])
W("   M restricted to 1^perp eigenvalues: %s" % [round(v, 10) for v in ev_1p])
W("   lambda_min(M on 1^perp) = %.8e   ->  %s" % (lam_min, "POSITIVE margin" if lam_min > 0 else "NEGATIVE (single constant minorant fails)"))

# local Hessian at the candidate (exact angles) for reference
ang = [mp.atan2(a[1], a[0]) for a in anchors]
H = [[mp.mpf(0)] * net.na for _ in range(net.na)]
for (i, j), qq in q.items():
    c = mp.cos(ang[i] - ang[j])
    v = 2 * qq * c
    H[i][i] += v; H[j][j] += v; H[i][j] -= v; H[j][i] -= v
evH, evH_1p, lamH = eig_1perp(H)
W("   local Hessian on 1^perp eigenvalues: %s" % [round(v, 10) for v in evH_1p])
W("   lambda_min(local H on 1^perp) = %.8e" % lamH)

# cross-check with old kkt near list (read-only, diagnostic only)
kk = json.loads((T14 / 'kkt_clean.json').read_text(encoding='utf-8'))
W("")
W("### cross-check vs old kkt_clean.json near list (diagnostic only)")
W("   kkt pairs  : %s" % [n for n in kk['nears'] if len(n) == 2])
W("   kkt triples: %s" % [n for n in kk['nears'] if len(n) == 3])
W("   my owner pairs: %s" % [tuple(ss) for ss in owners])
W("   my active triples: %s" % sorted(tuple(tri) for tri, _, _, _ in faces_active))

out = {
    'R': mp.nstr(R, 40), 'U_decimal': U, 'L': mp.nstr(L, 30), 'defect_10L_2pi': mp.nstr(defect, 30),
    'centers': [[mp.nstr(c[0], 30), mp.nstr(c[1], 30)] for c in C],
    'boundary_active': active, 'inactive': inactive,
    'd2_orbits': [list(o) for o in orbits],
    'anchors_deg': [float(mp.atan2(a[1], a[0]) * 180 / mp.pi) for a in anchors],
    'anchor_owners': owners,
    'gaps_deg': [float(g * 180 / mp.pi) for g in gaps],
    'active_faces': [list(tri) for tri, _, _, _ in faces_active],
    'active_face_orbits': [sorted(list(t) for t in o) for o in forbits],
    'stress_t_max': float(tpos) if tpos is not None else None,
    'min_schur_q': float(min(q.values())),
    'q_by_distance': {str(d): [sum(v), len(v)] for d, v in by_d.items()},
    'M_eig_1perp': ev_1p, 'M_lambda_min_1perp': lam_min,
    'localH_eig_1perp': evH_1p, 'localH_lambda_min_1perp': lamH,
    'c_d': {str(d): float(v) for d, v in cd.items()}, 'c5': c5,
    '4L_lt_pi': bool(4 * L < mp.pi), '5L_lt_pi': bool(5 * L < mp.pi),
}
dest = Path(__file__).resolve().parents[1]
(dest / 'logs').mkdir(exist_ok=True)
(dest / 'evidence').mkdir(exist_ok=True)
(dest / 'logs' / 'n14_portrait_stress.txt').write_text("\n".join(OUT), encoding='utf-8')
(dest / 'evidence' / 'n14-portrait-stress.json').write_text(json.dumps(out, indent=1), encoding='utf-8')
print("\nwrote logs/n14_portrait_stress.txt and evidence/n14-portrait-stress.json")
