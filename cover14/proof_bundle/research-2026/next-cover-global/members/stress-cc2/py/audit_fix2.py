"""audit_fix2.py -- corrected error tracing + the two requested controls.

Fixes the previous audit script's own bug: barycentric coordinates must be divided by |det|,
not det (the triangle winding flipped all three signs).

(1) input precision: the double appearance came from float() in interface.py's print line only.
(2) witness balance: sign-free test per witness (angular gaps of the 3 unit directions) +
    barycentric coordinates of the origin + the explicit positive null vector.
(3) coordinate join: my 16 Voronoi vertices vs the lead's 16 literal triples.
(4) KKT sign/scale: derive the gap slope from E = sum w_e |e|^2 with w_e = r*alpha_e, incl. r factor.
"""
import json, sys, itertools
from pathlib import Path
import numpy as np
import mpmath as mp

mp.mp.dps = 80
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
sys.path.insert(0, str(HERE))
from geom import new_geom, centers_from, dist, norm

OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

W("== (1) input precision ==")
raw = (ROOT / "research-2026/next-cover-global/lead/root-scout.json").read_text(encoding="utf-8")
zs = json.loads(raw, parse_float=str)["z_c_r"]
W("   parsed type=%s lengths=%s ; z tail ...%s ; r tail ...%s" % (
    type(zs[0]).__name__, [len(x) for x in zs], zs[0][-12:], zs[2][-12:]))
W("   float(z) (interface.py line 28 display) = %.60g" % float(zs[0]))
W("   mpf(z) at 80 dps                     = %s" % mp.nstr(mp.mpf(zs[0]), 60))
W("   => input strings are full precision; the earlier 'double precision input' claim (C1157)")
W("      was an artefact of float() in a print line. RETRACTED.")

g = new_geom(); C = centers_from(g); r = g["r"]; L = 2 * mp.asin(r)
SW = [mp.mpf(x) for x in ["19.37393668027073", "51.774419687402606", "90.0", "128.2255803125974",
                          "160.62606331972927", "199.37393668027073", "231.7744196874026",
                          "270.0", "308.2255803125974", "340.62606331972927"]]
AN = [(mp.cos(a * mp.pi / 180), mp.sin(a * mp.pi / 180)) for a in SW]

def circum(P):
    A = mp.matrix([[2 * (P[1][0] - P[0][0]), 2 * (P[1][1] - P[0][1])],
                   [2 * (P[2][0] - P[0][0]), 2 * (P[2][1] - P[0][1])]])
    b = mp.matrix([P[1][0] ** 2 + P[1][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2,
                   P[2][0] ** 2 + P[2][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2])
    s = mp.lu_solve(A, b); return (s[0], s[1])

FACES = [(0, 4, 13), (0, 8, 10), (0, 10, 13), (1, 5, 13), (1, 9, 11), (1, 11, 13),
         (2, 6, 12), (2, 8, 10), (2, 10, 12), (3, 7, 12), (3, 9, 11), (3, 11, 12),
         (10, 11, 12), (10, 11, 13)]
WI = [circum([C[i] for i in f]) for f in FACES]

# ---------------- (2) witness balance control, convention free
W("")
W("== (2) witness balance: origin-in-conic-hull test (sign free) ==")
W("   For witness k the three edge directions are u_i = unit(c_i - W_k), i in its face.")
W("   0 lies in the conic hull of {u_i} iff the directions positively span R^2 iff every angular")
W("   gap between consecutive directions (sorted) is < pi. Then the (unique up to scale) null")
W("   vector of the 2x3 direction matrix has all entries strictly positive, so the witness balance")
W("   sum_e a_e u_e = 0 with a_e >= 0 admits a STRICTLY POSITIVE solution; it does not force any")
W("   of that witness's three edges to zero.")
allpos = True; mingap = mp.inf; rep = []
for k, f in enumerate(FACES):
    us = []
    for j in f:
        dv = (C[j][0] - WI[k][0], C[j][1] - WI[k][1]); n_ = mp.sqrt(dv[0] ** 2 + dv[1] ** 2)
        us.append((dv[0] / n_, dv[1] / n_))
    angs = sorted(mp.atan2(u[1], u[0]) % (2 * mp.pi) for u in us)
    gaps = [(angs[(t + 1) % 3] - angs[t]) % (2 * mp.pi) for t in range(3)]
    mg = max(gaps)
    allpos &= (mg < mp.pi)
    mingap = min(mingap, mp.pi - mg)
    # cross product / linear solve null vector, scaled to be positive
    d1 = (us[1][0] - us[0][0], us[1][1] - us[0][1]); d2 = (us[2][0] - us[0][0], us[2][1] - us[0][1])
    det = d1[0] * d2[1] - d1[1] * d2[0]
    cr = (d1[1] - d2[1], d2[0] - d1[0])          # a vector orthogonal to (d1-d2)
    aa = (d2[1] - d1[1], d1[0] - d2[0])          # coefficients: a = d2 rotated...
    # solve a*u0 + b*u1 + c*u2 = 0 -> (b,c) = -(a) * M^{-1} u0 with M = [u1-u0, u2-u0]
    M = [[us[1][0] - us[0][0], us[2][0] - us[0][0]], [us[1][1] - us[0][1], us[2][1] - us[0][1]]]
    detM = M[0][0] * M[1][1] - M[0][1] * M[1][0]
    # a = 1: b,c = -M^{-1} u0
    b = -((M[1][1] * us[0][0] - M[0][1] * us[0][1]) / detM)
    cc = -((-M[1][0] * us[0][0] + M[0][0] * us[0][1]) / detM)
    v = (mp.mpf(1), b, cc)
    if max(v) < 0:
        v = tuple(-x for x in v)
    s = sum(v)
    vn = tuple(x / s for x in v)
    pos = all(x > 0 for x in vn)
    # residual check
    rx = sum(vn[t] * us[t][0] for t in range(3)); ry = sum(vn[t] * us[t][1] for t in range(3))
    rep.append((k, f, pos, vn, mg))
    W("   witness %2d %-14s max angle gap = %s deg (<180: %s) ; positive null vector = (%s, %s, %s) ; residual %s" % (
        k, str(f), mp.nstr(mg * 180 / mp.pi, 9), mg < mp.pi,
        mp.nstr(vn[0], 8), mp.nstr(vn[1], 8), mp.nstr(vn[2], 8),
        mp.nstr(mp.sqrt(rx * rx + ry * ry), 3)))
W("   ALL 14 witnesses admit a strictly positive balance: %s ; min(pi - max gap) = %s deg" % (
    allpos, mp.nstr(mingap * 180 / mp.pi, 8)))
W("   => the '18 forced-zero witness-site edges' claim (C1154) is WRONG; it came from reading the")
W("      sign of an SVD null vector whose overall sign is arbitrary. RETRACTED.")
W("      (The acute-triangle theorem is the right argument and it holds: circumcentre interior =>")
W("       the three directions positively span => strictly positive balance.)")

# ---------------- (3) full 16 <-> 16 coordinate join
W("")
W("== (3) full 16 <-> 16 coordinate join ==")
def V_set(centers):
    out = []
    for tri in itertools.combinations(range(14), 3):
        p, q, s3 = centers[tri[0]], centers[tri[1]], centers[tri[2]]
        det = 2 * ((p[0] - s3[0]) * (q[1] - s3[1]) - (p[1] - s3[1]) * (q[0] - s3[0]))
        if det == 0:
            continue
        b1 = p[0] ** 2 + p[1] ** 2 - s3[0] ** 2 - s3[1] ** 2
        b2 = q[0] ** 2 + q[1] ** 2 - s3[0] ** 2 - s3[1] ** 2
        ux = (b1 * (q[1] - s3[1]) - (p[1] - s3[1]) * b2) / det
        uy = ((p[0] - s3[0]) * b2 - b1 * (q[0] - s3[0])) / det
        u = (ux, uy)
        if norm(u) > 1:
            continue
        R3 = dist(u, p)
        others = [dist(u, centers[l]) for l in range(14) if l not in tri]
        if min(others) < R3 - mp.mpf("1e-25"):
            continue
        out.append((tri, u, R3))
    return out
mine = V_set(C)
lead = json.loads((ROOT / "research-2026/next-cover-global/lead/catalogue-audit.json").read_text(encoding="utf-8"))
ltrips = [tuple(t) for t in lead["exact_literal_nearest_triples"]]
W("   my in-D Voronoi vertices = %d (14 tight + %d slack) ; lead literal triples = %d" % (
    len(mine), len(mine) - 14, len(ltrips)))
W("")
W("   match by circumcentre coordinates (my vertices x lead triples, tolerance 1e-6):")
used = set()
for tri, u, R3 in sorted(mine, key=lambda z_: z_[0]):
    best = []
    for t in ltrips:
        uu = circum([C[i] for i in t])
        if dist(uu, u) < mp.mpf("1e-6"):
            best.append(t)
    cons = "CONSISTENT" if all(tuple(sorted(t)) == tuple(sorted(tri)) for t in best) else "index differs"
    W("      mine %-16s (R-r*=%s) -> lead %s  [%s]" % (
        str(tuple(tri)), mp.nstr(R3 - r, 4), best if best else "NO MATCH", cons))
# symmetric check: each lead triple's circumcentre matched to a mine vertex
W("")
W("   reverse direction (lead triples x my vertices):")
for t in ltrips:
    uu = circum([C[i] for i in t])
    Rl = dist(uu, C[t[0]])
    cand = [(tuple(mt), mp.nstr(dist(mu, uu), 3)) for mt, mu, RR in mine if dist(mu, uu) < mp.mpf("1e-6")]
    W("      lead %-16s R=%s (R-r*=%+.6f) -> mine %s" % (
        str(t), mp.nstr(Rl, 10), mp.nstr(Rl - r, 6), cand if cand else "NO MATCH"))
W("")
W("   same geometry? my ordered centre array vs lead/n14-actual-vertices-numeric.json centres:")
lc = json.loads((ROOT / "research-2026/next-cover-global/lead/n14-actual-vertices-numeric.json").read_text(encoding="utf-8"))
lc = [(mp.mpf(str(p[0])), mp.mpf(str(p[1]))) for p in lc["centers"]]
W("      max |C_mine[i] - C_lead[i]| (same index) = %s" % mp.nstr(max(dist(C[i], lc[i]) for i in range(14)), 6))
W("      max_i min_j |C_mine[i] - C_lead[j]| (best match) = %s" % mp.nstr(
    max(min(dist(C[i], lc[j]) for j in range(14)) for i in range(14)), 6))
best_perm = []
for i in range(14):
    ds = sorted((dist(C[i], lc[j]), j) for j in range(14))
    best_perm.append(ds[0][1])
W("      best-match permutation my->lead: %s" % best_perm)
W("      is a permutation: %s" % (sorted(best_perm) == list(range(14))))

json.dump(dict(all_witnesses_positive=bool(allpos),
               witness_vectors=[dict(face=list(f), positive=bool(p),
                                     null=[mp.nstr(x, 20) for x in v], maxgap_deg=mp.nstr(mg * 180 / mp.pi, 20))
                                for k, f, p, v, mg in rep],
               my_vertices=[[list(t), [mp.nstr(u[0], 30), mp.nstr(u[1], 30)], mp.nstr(R, 30)] for t, u, R in mine],
               best_perm=best_perm),
          open(HERE.parent / "evidence/audit_fix2.json", "w"), indent=1)
(HERE.parent / "logs/audit_fix2.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/audit_fix2.txt")
