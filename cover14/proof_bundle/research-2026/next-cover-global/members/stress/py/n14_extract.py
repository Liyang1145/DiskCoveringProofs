"""n14_extract.py — n14 几何与图提取（可复用模块，无副作用打印）。

中心 = hprec_sol 的 7 参数按 verify_c407_lead.py:186-195 展开；
锚 = 10 个边界活跃盘在 ∂D 的弧端点（重合端点聚类）；
见证 = D 内 Voronoi 顶点（Delaunay 空圆 + circumcentre in D），活动 = 距离 = R。
"""
import itertools
import json
from pathlib import Path

import mpmath as mp

T14 = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\session2\type14\out")
dd = lambda p, q: mp.sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)
norm = lambda p: mp.sqrt(p[0] ** 2 + p[1] ** 2)


def load(dps=60):
    mp.mp.dps = dps
    sol = json.loads((T14 / 'hprec_sol_refined.json').read_text(encoding='utf-8'))
    th = [mp.mpf(s) for s in sol['th'][:7]]
    R = mp.mpf(sol['R'])
    C = []
    for j in (0, 2):
        for s in (-1, 1):
            for t in (-1, 1):
                C.append((s * th[j], t * th[j + 1]))
    for j in (4, 5):
        C.extend([(th[j], mp.mpf(0)), (-th[j], mp.mpf(0))])
    C.extend([(mp.mpf(0), th[6]), (mp.mpf(0), -th[6])])
    return th, R, C


def arcs_and_anchors(C, R):
    """returns anchors (cyclic, unit circle), owners (list of site-index pairs)."""
    active = [i for i, c in enumerate(C) if norm(c) + R >= 1]
    ends = []
    for i in active:
        r = norm(C[i]); m = (1 + r * r - R * R) / (2 * r)
        assert -1 <= m <= 1
        psi = mp.acos(m); phi = mp.atan2(C[i][1], C[i][0])
        ends.append(((phi - psi) % (2 * mp.pi), i)); ends.append(((phi + psi) % (2 * mp.pi), i))
    ends.sort(key=lambda z: z[0])
    clusters, cur = [], [ends[0]]
    for e in ends[1:]:
        if abs(e[0] - cur[-1][0]) < mp.mpf('1e-25'):
            cur.append(e)
        else:
            clusters.append(cur); cur = [e]
    clusters.append(cur)
    A, O = [], []
    for cl in clusters:
        ang = sum(x[0] for x in cl) / len(cl)
        A.append((mp.cos(ang), mp.sin(ang)))
        O.append(sorted({x[1] for x in cl}))
    order = sorted(range(len(A)), key=lambda k: mp.atan2(A[k][1], A[k][0]) % (2 * mp.pi))
    return active, [A[k] for k in order], [O[k] for k in order]


def voronoi_faces(C, R, tol_active=mp.mpf('1e-14')):
    """D-internal Voronoi vertices with empty-circle property; classified active/slack."""
    faces = []
    for tri in itertools.combinations(range(len(C)), 3):
        p, q, s = (C[t] for t in tri)
        det = 2 * ((p[0] - s[0]) * (q[1] - s[1]) - (p[1] - s[1]) * (q[0] - s[0]))
        if abs(det) < mp.mpf('1e-40'):
            continue
        b1 = p[0] ** 2 + p[1] ** 2 - s[0] ** 2 - s[1] ** 2
        b2 = q[0] ** 2 + q[1] ** 2 - s[0] ** 2 - s[1] ** 2
        u = ((b1 * (q[1] - s[1]) - (p[1] - s[1]) * b2) / det,
             ((p[0] - s[0]) * b2 - b1 * (q[0] - s[0])) / det)
        if norm(u) > 1 + mp.mpf('1e-30'):
            continue
        d = dd(u, p)
        if min(dd(u, C[l]) for l in range(len(C)) if l not in tri) < d - mp.mpf('1e-20'):
            continue
        faces.append((tri, u, d, abs(d - R) < tol_active))
    return faces


def d2_perms(C):
    """permutations induced by C2 and the two axis mirrors (geometrically exact)."""
    def pm(g):
        out = []
        for i, c in enumerate(C):
            img = g(c)
            best = min(range(len(C)), key=lambda j: dd(img, C[j]))
            assert dd(img, C[best]) < mp.mpf('1e-30')
            out.append(best)
        return tuple(out)
    return [pm(lambda c: (-c[0], -c[1])), pm(lambda c: (-c[0], c[1])), pm(lambda c: (c[0], -c[1]))]
