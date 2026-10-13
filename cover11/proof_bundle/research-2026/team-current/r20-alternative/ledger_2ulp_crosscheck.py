# -*- coding: utf-8 -*-
"""
r20-alternative / cross-check of R_D(certified_object) against the ledger value C249.

Two independent evaluations of the same rational object (integers/1e17):
  (i)  candidate family V3 (circumcentres) + V2b (bisector cap unit circle), computed in two
       different parameterisations (line-normal form, and rotation/angle form),
  (ii) a direct dense scan of D (Polar + Cartesian) to see whether anything exceeds the family max.
Also: at the reported argmax we print |p|^2 - 1 and the individual centre distances at 50 digits.
"""
import json, os
import numpy as np
from mpmath import mp, mpf, sqrt, acos, pi, cos, sin, atan2, hypot

mp.dps = 60
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
raw = json.load(open(os.path.join(ROOT, "n11", "upper", "certified_object.json"), encoding="utf-8-sig"))
S = mpf(10) ** int(raw["decimals"])
C = [(mpf(str(a)) / S, mpf(str(b)) / S) for a, b in raw["centers_scaled_1e17"]]
n = len(C)
C249 = mpf("0.379983853119838689722261606136093214308718957")
print("C249 (ledger upper bound) =", mp.nstr(C249, 40))


def dm(p):
    return min(sqrt((p[0] - c[0]) ** 2 + (p[1] - c[1]) ** 2) for c in C)


# ---- (i-a) V2b in line-normal form ----
fam = []
for i in range(n):
    for j in range(i + 1, n):
        ax, ay = C[i]; bx, by = C[j]
        dx, dy = bx - ax, by - ay
        rhs = (bx ** 2 + by ** 2 - ax ** 2 - ay ** 2) / 2
        nrm = sqrt(dx ** 2 + dy ** 2)
        dd = rhs / nrm
        if abs(dd) > 1:
            continue
        ux, uy = dx / nrm, dy / nrm
        h = sqrt(1 - dd ** 2)
        for sg in (1, -1):
            p = (dd * ux - sg * h * uy, dd * uy + sg * h * ux)
            fam.append(("V2b-line", (i, j), p, dm(p)))

# ---- (i-b) V2b in angle form (independent parameterisation) ----
for i in range(n):
    for j in range(i + 1, n):
        ax, ay = C[i]; bx, by = C[j]
        # perpendicular bisector direction (rotate d by 90deg), passing through midpoint
        dx, dy = bx - ax, by - ay
        mx, my = (ax + bx) / 2, (ay + by) / 2
        # points of unit circle: p = (cos t, sin t); solve 2 p.(b-a) = |b|^2-|a|^2
        # => A cos t + B sin t = D with A = 2dx, B = 2dy, D = |b|^2-|a|^2
        A, B = 2 * dx, 2 * dy
        D = bx ** 2 + by ** 2 - ax ** 2 - ay ** 2
        Rr = sqrt(A * A + B * B)
        if abs(D) > Rr:
            continue
        phi0 = atan2(B, A)
        alp = acos(min(mpf(1), max(mpf(-1), D / Rr)))
        for sg in (1, -1):
            t = sg * alp + phi0
            p = (cos(t), sin(t))
            fam.append(("V2b-ang", (i, j), p, dm(p)))

# ---- (i-c) V3 circumcentres ----
for i in range(n):
    for j in range(i + 1, n):
        for k in range(j + 1, n):
            (ax, ay), (bx, by), (cx, cy) = C[i], C[j], C[k]
            d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
            if abs(d) < mpf(10) ** -25:
                continue
            ux = ((ax ** 2 + ay ** 2) * (by - cy) + (bx ** 2 + by ** 2) * (cy - ay) + (cx ** 2 + cy ** 2) * (ay - by)) / d
            uy = ((ax ** 2 + ay ** 2) * (cx - bx) + (bx ** 2 + by ** 2) * (ax - cx) + (cx ** 2 + cy ** 2) * (bx - ax)) / d
            p = (ux, uy)
            if p[0] ** 2 + p[1] ** 2 <= 1 + mpf(10) ** -30:
                fam.append(("V3", (i, j, k), p, dm(p)))

fam.sort(key=lambda t: -t[3])
print("\ntop of candidate family:")
seen = []
for tag, idx, p, d in fam:
    if any(sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2) < mpf(10) ** -8 for q in seen):
        continue
    seen.append(p)
    print("   %-9s %-12s depth=%s   |p|^2-1=%s" % (tag, str(idx), mp.nstr(d, 35), mp.nstr(p[0] ** 2 + p[1] ** 2 - 1, 12)))
    if len(seen) >= 6:
        break

# cross-check: V2b-line vs V2b-ang agree? (match per pair, 2x2, order may be swapped)
byl = {}
for tag, idx, p, d in fam:
    if tag == "V2b-line":
        byl.setdefault(idx, []).append(p)
bya = {}
for tag, idx, p, d in fam:
    if tag == "V2b-ang":
        bya.setdefault(idx, []).append(p)
worst = mpf(0)
for idx in byl:
    if idx not in bya:
        continue
    P1, P2 = byl[idx], bya[idx]
    d_same = max(sqrt((P1[0][0] - P2[0][0]) ** 2 + (P1[0][1] - P2[0][1]) ** 2),
                 sqrt((P1[1][0] - P2[1][0]) ** 2 + (P1[1][1] - P2[1][1]) ** 2))
    d_swap = max(sqrt((P1[0][0] - P2[1][0]) ** 2 + (P1[0][1] - P2[1][1]) ** 2),
                 sqrt((P1[1][0] - P2[0][0]) ** 2 + (P1[1][1] - P2[0][1]) ** 2))
    worst = max(worst, min(d_same, d_swap))
print("\nmax disagreement between the two V2b parameterisations (best matching):", mp.nstr(worst, 6))
print("number of V2b-line points:", sum(1 for t in fam if t[0] == "V2b-line"),
      " V2b-ang points:", sum(1 for t in fam if t[0] == "V2b-ang"))

# ---- (ii) dense direct scan ----
best = (mpf(0), None)
N = 400000
for t in range(N):
    th = 2 * pi * t / N
    p = (cos(th), sin(th))
    d = dm(p)
    if d > best[0]:
        best = (d, p)
print("\ndirect 400k scan of bd D :", mp.nstr(best[0], 30))
bestr = (mpf(0), None)
for a in range(220):
    for b in range(220):
        x = -1 + 2 * mpf(a) / 219; y = -1 + 2 * mpf(b) / 219
        if x * x + y * y > 1:
            continue
        d = dm((x, y))
        if d > bestr[0]:
            bestr = (d, (x, y))
print("direct Cartesian 220^2 scan:", mp.nstr(bestr[0], 30))

# ---- argmax details ----
p = fam[0][2]
print("\nargmax family member:", fam[0][0], fam[0][1])
print("  |p| =", mp.nstr(sqrt(p[0] ** 2 + p[1] ** 2), 40), "  |p|^2-1 =", mp.nstr(p[0] ** 2 + p[1] ** 2 - 1, 12))
ds = sorted((sqrt((p[0] - c[0]) ** 2 + (p[1] - c[1]) ** 2), i) for i, c in enumerate(C))
for d, i in ds[:4]:
    print("   dist to c%-2d = %s" % (i, mp.nstr(d, 35)))
print("\nfamily max - C249 =", mp.nstr(fam[0][3] - C249, 12))
