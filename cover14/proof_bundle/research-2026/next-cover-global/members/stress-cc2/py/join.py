"""join.py -- explicit coordinate join between my 14-centre array and lead/n14-actual-vertices-numeric.json.

(1) best-match permutation by coordinates and a coordinate-consistency test (pairwise distances);
(2) search for a permutation of my indices that maps my 14 tight + 2 slack triples onto the lead's
    16 literal triples; verify it against the coordinates rather than assuming it.
(3) corrected witness null vectors (previous script had a solve sign bug; the gap test was fine).
"""
import json, sys, itertools
from pathlib import Path
import numpy as np
import mpmath as mp

mp.mp.dps = 60
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
sys.path.insert(0, str(HERE))
from geom import new_geom, centers_from, dist, norm

OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

g = new_geom(); C = centers_from(g); r = g["r"]
lead = json.loads((ROOT / "research-2026/next-cover-global/lead/n14-actual-vertices-numeric.json").read_text(encoding="utf-8"))
LC = [(mp.mpf(str(p[0])), mp.mpf(str(p[1]))) for p in lead["centers"]]
AUD = json.loads((ROOT / "research-2026/next-cover-global/lead/catalogue-audit.json").read_text(encoding="utf-8"))
L16 = [tuple(sorted(t)) for t in AUD["exact_literal_nearest_triples"]]
LTIGHT_lead = [tuple(sorted(t["sites"])) for t in lead["tight"]]
LSLACK_lead = [tuple(sorted(t["sites"])) for t in lead["actual"] if tuple(sorted(t["sites"])) not in LTIGHT_lead]

W("== coordinate join, my index order vs lead/n14-actual-vertices-numeric.json ==")
W("my centres (index: coords, |c|):")
for i, p in enumerate(C):
    W("   %2d (%s, %s)  |c|=%s" % (i, mp.nstr(p[0], 18), mp.nstr(p[1], 18), mp.nstr(norm(p), 12)))
W("lead centres (index: coords, |c|):")
for j, p in enumerate(LC):
    W("   %2d (%s, %s)  |c|=%s" % (j, mp.nstr(p[0], 18), mp.nstr(p[1], 18), mp.nstr(norm(p), 12)))
permx = [min(range(14), key=lambda j: dist(C[i], LC[j])) for i in range(14)]
W("best-match permutation my->lead: %s (injective: %s)" % (permx, sorted(permx) == list(range(14))))
W("coordinate distances for the matched pairs: %s" % [mp.nstr(dist(C[i], LC[permx[i]]), 3) for i in range(14)])

# coordinate-consistency test: pairwise distances must match
W("")
W("pairwise-distance consistency (max |d_mine(i,j) - d_lead(perm i, perm j)|):")
mx = mp.mpf(0)
for i in range(14):
    for j in range(i + 1, 14):
        mx = max(mx, abs(dist(C[i], C[j]) - dist(LC[permx[i]], LC[permx[j]])))
W("   %s" % mp.nstr(mx, 6))

# ---- permutation search over my block structure, both directions
def blocks():
    for p03 in itertools.permutations(range(4)):
        for p47 in itertools.permutations(range(4, 8)):
            for p89 in [(8, 9), (9, 8)]:
                for p1011 in [(10, 11), (11, 10)]:
                    for p1213 in [(12, 13), (13, 12)]:
                        pm = list(range(14))
                        for k, v in enumerate(p03): pm[k] = v
                        for k, v in enumerate(p47): pm[4 + k] = v
                        pm[8], pm[9] = p89; pm[10], pm[11] = p1011; pm[12], pm[13] = p1213
                        yield pm

MINE16 = [(0, 4, 13), (0, 8, 10), (0, 10, 13), (1, 5, 13), (1, 9, 11), (1, 11, 13),
          (2, 6, 12), (2, 8, 10), (2, 10, 12), (3, 7, 12), (3, 9, 11), (3, 11, 12),
          (10, 11, 12), (10, 11, 13), (4, 5, 13), (6, 7, 12)]   # 14 tight + 2 slack
target = set(L16)
found = []
for pm in blocks():
    img = set(tuple(sorted(pm[t] for t in tri)) for tri in MINE16)
    if img == target:
        found.append(pm)
W("")
W("permutations (over the signed block structure) mapping my 16 triple set onto the lead's 16: %d" % len(found))
for pm in found[:6]:
    W("   %s" % pm)
    # does this permutation agree with the coordinate best-match?
    agree = sum(1 for i in range(14) if pm[i] == permx[i])
    W("      agrees with the coordinate best-match on %d/14 indices" % agree)
# also try the dihedral maps
W("")
def perm_of(g2):
    pm = []
    for i in range(14):
        img = g2(C[i]); best = min(range(14), key=lambda j: dist(img, LC[j]))
        if dist(img, LC[best]) > mp.mpf("1e-12"):
            return None
        pm.append(best)
    return pm
maps = {"C2": lambda p: (-p[0], -p[1]), "mirror_y": lambda p: (-p[0], p[1]),
        "mirror_x": lambda p: (p[0], -p[1]), "swap_xy": lambda p: (p[1], p[0]),
        "swap_xy-": lambda p: (-p[1], -p[0])}
for nm, f in maps.items():
    pm = perm_of(f)
    if pm is None:
        W("   %-9s not a symmetry of the lead array" % nm); continue
    img = set(tuple(sorted(pm[t] for t in tri)) for tri in MINE16)
    W("   %-9s perm=%s -> leads 16? %s (symdiff %d)" % (nm, pm, img == target, len(img ^ target)))
    if img != target:
        W("        symdiff: %s" % sorted(img ^ target))

# ---- corrected witness null vectors
W("")
W("== corrected witness null vectors (solve sign fixed) ==")
SW = [mp.mpf(x) * mp.pi / 180 for x in ["19.37393668027073", "51.774419687402606", "90.0",
      "128.2255803125974", "160.62606331972927", "199.37393668027073", "231.7744196874026",
      "270.0", "308.2255803125974", "340.62606331972927"]]
AN = [(mp.cos(a), mp.sin(a)) for a in SW]
def circum(P):
    A = mp.matrix([[2 * (P[1][0] - P[0][0]), 2 * (P[1][1] - P[0][1])],
                   [2 * (P[2][0] - P[0][0]), 2 * (P[2][1] - P[0][1])]])
    b = mp.matrix([P[1][0] ** 2 + P[1][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2,
                   P[2][0] ** 2 + P[2][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2])
    s = mp.lu_solve(A, b); return (s[0], s[1])
FACES = [(0, 4, 13), (0, 8, 10), (0, 10, 13), (1, 5, 13), (1, 9, 11), (1, 11, 13),
         (2, 6, 12), (2, 8, 10), (2, 10, 12), (3, 7, 12), (3, 9, 11), (3, 11, 12),
         (10, 11, 12), (10, 11, 13)]
for k, f in enumerate(FACES):
    Wk = circum([C[i] for i in f])
    us = []
    for j in f:
        dv = (C[j][0] - Wk[0], C[j][1] - Wk[1]); n_ = mp.sqrt(dv[0] ** 2 + dv[1] ** 2)
        us.append((dv[0] / n_, dv[1] / n_))
    # solve a*u0 + b*u1 + c*u2 = 0 by fixing a=1:  b*(u1-u0) + c*(u2-u0) = -u0
    M = mp.matrix([[us[1][0] - us[0][0], us[2][0] - us[0][0]],
                   [us[1][1] - us[0][1], us[2][1] - us[0][1]]])
    sol = mp.lu_solve(M, mp.matrix([-us[0][0], -us[0][1]]))
    v = (mp.mpf(1), sol[0], sol[1])
    s = sum(v); vn = tuple(x / s for x in v)
    rx = sum(vn[t] * us[t][0] for t in range(3)); ry = sum(vn[t] * us[t][1] for t in range(3))
    W("   witness %2d %-14s null vector = (%s, %s, %s) residual = %s ; positive = %s" % (
        k, str(f), mp.nstr(vn[0], 10), mp.nstr(vn[1], 10), mp.nstr(vn[2], 10),
        mp.nstr(mp.sqrt(rx * rx + ry * ry), 3), all(x > 0 for x in vn)))
json.dump(dict(best_perm=permx, pairwise_consistency=mp.nstr(mx, 20),
               permutations_matching=found[:8]), open(HERE.parent / "evidence/join.json", "w"), indent=1)
(HERE.parent / "logs/join.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/join.txt")
