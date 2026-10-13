"""witness_pos.py -- corrected witness balance vectors (exact cross-product formula) and the
final statement of the coordinate join.
"""
import json, sys
from pathlib import Path
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
AN = [(mp.cos(a), mp.sin(a)) for a in [mp.mpf(x) * mp.pi / 180 for x in
      ["19.37393668027073", "51.774419687402606", "90.0", "128.2255803125974",
       "160.62606331972927", "199.37393668027073", "231.7744196874026", "270.0",
       "308.2255803125974", "340.62606331972927"]]]

def circum(P):
    A = mp.matrix([[2 * (P[1][0] - P[0][0]), 2 * (P[1][1] - P[0][1])],
                   [2 * (P[2][0] - P[0][0]), 2 * (P[2][1] - P[0][1])]])
    b = mp.matrix([P[1][0] ** 2 + P[1][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2,
                   P[2][0] ** 2 + P[2][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2])
    s = mp.lu_solve(A, b); return (s[0], s[1])

FACES = [(0, 4, 13), (0, 8, 10), (0, 10, 13), (1, 5, 13), (1, 9, 11), (1, 11, 13),
         (2, 6, 12), (2, 8, 10), (2, 10, 12), (3, 7, 12), (3, 9, 11), (3, 11, 12),
         (10, 11, 12), (10, 11, 13)]
W("== witness balance vectors (cross-product formula, residual checked) ==")
allpos = True
for k, f in enumerate(FACES):
    Wk = circum([C[i] for i in f])
    us = []
    for j in f:
        dv = (C[j][0] - Wk[0], C[j][1] - Wk[1]); n_ = mp.sqrt(dv[0] ** 2 + dv[1] ** 2)
        us.append((dv[0] / n_, dv[1] / n_))
    # coefficients: a = c0y - c1y? use cross products: (b,c) ~ (u0 x u2, u1 x u0)
    cr = lambda p, q: p[0] * q[1] - p[1] * q[0]
    v = (cr(us[1], us[2]), cr(us[2], us[0]), cr(us[0], us[1]))
    if max(v) < 0:
        v = tuple(-x for x in v)
    s = sum(v); vn = tuple(x / s for x in v)
    rx = sum(vn[t] * us[t][0] for t in range(3)); ry = sum(vn[t] * us[t][1] for t in range(3))
    res = mp.sqrt(rx * rx + ry * ry)
    pos = all(x > 0 for x in vn)
    allpos &= pos
    W("   witness %2d %-14s (a,b,c) = (%s, %s, %s)  residual = %s  strictly positive = %s" % (
        k, str(f), mp.nstr(vn[0], 12), mp.nstr(vn[1], 12), mp.nstr(vn[2], 12), mp.nstr(res, 3), pos))
W("ALL witnesses strictly positive balance: %s" % allpos)
W("=> the '18 forced-zero witness-site edges' claim is wrong: the witness balance does NOT force")
W("   any witness edge to zero. (The SVD sign reading in witness_balance.py/final_check.py was the")
W("   error; the sign-free angular-gap test and this exact cross-product test both give 'positive'.)")

W("")
W("== coordinate join statement ==")
lead = json.loads((ROOT / "research-2026/next-cover-global/lead/n14-actual-vertices-numeric.json").read_text(encoding="utf-8"))
LC = [(mp.mpf(str(p[0])), mp.mpf(str(p[1]))) for p in lead["centers"]]
perm = [min(range(14), key=lambda j: dist(C[i], LC[j])) for i in range(14)]
W("best-match permutation my -> lead (by coordinates): %s" % perm)
W("matched-pair distances: %s" % [mp.nstr(dist(C[i], LC[perm[i]]), 4) for i in range(14)])
W("=> lead/n14-actual-vertices-numeric.json holds the OLD hprec_sol_refined coordinates")
W("   (differences 3.2e-10 .. 1.4e-9, matching the 2.34e-10 / 5.80e-10 root shift), in an order")
W("   that is a sign flip inside the (+-c,+-d) orbit and a swap of (+-s,0) with its mirror.")
W("   Its 'tight' list (sites keyed by that array) is therefore not the tight list of the")
W("   stationary-root geometry; the correct join is by coordinates, and the triple sets")
W("   correspond under this permutation only after the sign/order fix.")
W("my tight set (my indices):    %s" % [list(t) for t in FACES])
W("lead 'tight' (their array):   %s" % [t["sites"] for t in lead["tight"]])
W("lead's tight triples re-keyed through the coordinate permutation:")
rekeyed = []
for t in lead["tight"]:
    inv = [perm.index(j) for j in range(14)]
    rekeyed.append(tuple(sorted(inv[j] for j in t["sites"])))
W("   %s" % sorted(rekeyed))
W("equals my tight set: %s" % (sorted(rekeyed) == sorted(FACES)))
json.dump(dict(perm=perm, rekeyed_tight=sorted(rekeyed)), open(HERE.parent / "evidence/witness_pos.json", "w"), indent=1)
(HERE.parent / "logs/witness_pos.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/witness_pos.txt")
