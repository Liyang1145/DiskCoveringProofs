"""geom.py -- independent reconstruction of the n14 candidate geometry at the NEW stationary root.

Input: coordinates GIVEN by Lead (lead/root-scout.json, z_c_r). No re-solving, no use of
old hprec_sol / hprec_sol_refined except as an explicitly labelled comparison object.

Index convention (Lead C-order, from root_scout geom + old solve's center scale set):
  a=(s+z)/2, b=r+sqrt(r^2-(a-z)^2), c=given, d=1-sqrt(r^2-c^2), s=sqrt(1-r^2),
  z=given, t=r+sqrt(r^2-z^2)
  sites 0..3   : (+-a, +-b)   : (a,b),(a,-b),(-a,b),(-a,-b)
  sites 4..7   : (+-c, +-d)
  sites 8,9     : (+-s, 0)
  sites 10,11   : (+-z, 0)
  sites 12,13   : (0, -+t)
"""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 60   # numeric working precision; NOT an interval/exact certificate

ROOT = Path(__file__).resolve().parents[5]
SCOUT = ROOT / "research-2026/next-cover-global/lead/root-scout.json"


def new_geom():
    d = json.loads(SCOUT.read_text(encoding="utf-8"))
    z, c, r = (mp.mpf(s) for s in d["z_c_r"])
    s = mp.sqrt(1 - r * r)
    a = (s + z) / 2
    b = r + mp.sqrt(r * r - (a - z) ** 2)
    dd = 1 - mp.sqrt(r * r - c * c)
    t = r + mp.sqrt(r * r - z * z)
    return dict(a=a, b=b, c=c, d=dd, s=s, z=z, t=t, r=r)


def centers_from(g):
    a, b, c, dd, s, z, t = g["a"], g["b"], g["c"], g["d"], g["s"], g["z"], g["t"]
    C = []
    for sy in (1, -1):
        for sx in (1, -1):
            C.append((sx * a, sy * b))
    for sy in (1, -1):
        for sx in (1, -1):
            C.append((sx * c, sy * dd))
    C.append((s, mp.mpf(0)))
    C.append((-s, mp.mpf(0)))
    C.append((z, mp.mpf(0)))
    C.append((-z, mp.mpf(0)))
    C.append((mp.mpf(0), -t))
    C.append((mp.mpf(0), t))
    return C


def old_geom_centers():
    """OLD (nonstationary) refined-solve centers, old portrait index order, for comparison only."""
    p = ROOT / "research-2026/session2/type14/out/hprec_sol_refined.json"
    j = json.loads(p.read_text(encoding="utf-8"))
    th = [mp.mpf(s) for s in j["th"][:7]]
    R = mp.mpf(j["R"])
    C = []
    for jj in (0, 2):
        for sx in (-1, 1):
            for sy in (-1, 1):
                C.append((sx * th[jj], sy * th[jj + 1]))
    for jj in (4, 5):
        C.extend([(th[jj], mp.mpf(0)), (-th[jj], mp.mpf(0))])
    C.extend([(mp.mpf(0), th[6]), (mp.mpf(0), -th[6])])
    return C, R, th


def norm(p):
    return mp.sqrt(p[0] ** 2 + p[1] ** 2)


def dist(p, q):
    return mp.sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)


def circumcenter(p, q, s):
    """Exact-ish rational-formula circumcenter in mp arithmetic (no division by tiny det unchecked)."""
    d = 2 * ((p[0] - s[0]) * (q[1] - s[1]) - (p[1] - s[1]) * (q[0] - s[0]))
    if d == 0:
        return None, mp.mpf(0)
    b1 = p[0] ** 2 + p[1] ** 2 - s[0] ** 2 - s[1] ** 2
    b2 = q[0] ** 2 + q[1] ** 2 - s[0] ** 2 - s[1] ** 2
    ux = (b1 * (q[1] - s[1]) - (p[1] - s[1]) * b2) / d
    uy = ((p[0] - s[0]) * b2 - b1 * (q[0] - s[0])) / d
    return (ux, uy), d


def voronoi_vertices(C, tol_in=mp.mpf("1e-40"), tol_empty=mp.mpf("1e-30")):
    """All triples whose circumcenter lies in closed unit disk and satisfies empty-circle
    (weak: no other site strictly closer). Returns list of dicts."""
    import itertools
    out = []
    for tri in itertools.combinations(range(len(C)), 3):
        u, d = circumcenter(C[tri[0]], C[tri[1]], C[tri[2]])
        if u is None:
            continue
        ru = norm(u)
        if ru > 1 + tol_in:
            continue
        R3 = dist(u, C[tri[0]])
        others = [dist(u, C[l]) for l in range(len(C)) if l not in tri]
        m = min(others) if others else mp.inf
        if m < R3 - tol_empty:
            continue
        out.append(dict(tri=tuple(tri), u=u, R=R3, absu=ru, slack_margin=m - R3))
    return out
