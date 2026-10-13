# -*- coding: utf-8 -*-
"""
r20-alternative / structural reading of the n=14 certified candidate (read-only).

Object: type14/out/hprec_sol.json  (52-digit solution; R = 0.3317320342762341235155066403893542386599...)
Output: ring/interior split, arc half-width spectrum, and the flat-sector test |c| vs sqrt(1-R^2).
"""
import json, os
from mpmath import mp, mpf, sqrt, acos, asin, pi

mp.dps = 60
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
d = json.load(open(os.path.join(ROOT, "research-2026", "session2", "type14", "out", "hprec_sol.json"),
                   encoding="utf-8"))
C = [[mpf(a), mpf(b)] for a, b in d["centers"]]
R = mpf(d["R"])
n = len(C)
print("n =", n, " R =", mp.nstr(R, 40))
print("sqrt(1-R^2) =", mp.nstr(sqrt(1 - R * R), 30), "   arcsin R =", mp.nstr(asin(R) * 180 / pi, 12), "deg\n")
rad = [sqrt(c[0] ** 2 + c[1] ** 2) for c in C]
ring = [i for i in range(n) if rad[i] >= 1 - R]
inner = [i for i in range(n) if rad[i] < 1 - R]
tot = mpf(0)
for i in range(n):
    tag = "ring " if i in ring else "inner"
    psi = None
    if i in ring:
        cs = (1 + rad[i] ** 2 - R ** 2) / (2 * rad[i])
        psi = acos(min(mpf(1), max(mpf(-1), cs)))
        tot += psi
    print("  %2d %s |c| = %s%s  %s" % (
        i, tag, mp.nstr(rad[i], 24),
        ("   psi = %s deg" % mp.nstr(psi * 180 / pi, 9)) if psi is not None else "",
        ("  <-- |c|-sqrt(1-R^2) = %s" % mp.nstr(rad[i] - sqrt(1 - R * R), 6)) if abs(rad[i] - sqrt(1 - R * R)) < mpf("1e-12") else ""))
print("\n#ring =", len(ring), " #inner =", len(inner), " inner indices:", inner)
print("sum of ring arc half-widths =", mp.nstr(tot * 180 / pi, 14), "deg   (pi = 180 deg)  slack =", mp.nstr(tot - pi, 8))
qs = d.get("qpts", [])
print("\n#tied q-points:", len(qs))
nb = sum(1 for q in qs if abs(sqrt(mpf(q[0]) ** 2 + mpf(q[1]) ** 2) - 1) < mpf("1e-20"))
print("  on |q| = 1 :", nb, "   interior :", len(qs) - nb)
for q in qs[:6]:
    print("   q=(%s,%s) active=%s  |q|=%s" % (mp.nstr(mpf(q[0]), 12), mp.nstr(mpf(q[1]), 12), q[2],
                                              mp.nstr(sqrt(mpf(q[0]) ** 2 + mpf(q[1]) ** 2), 12)))
