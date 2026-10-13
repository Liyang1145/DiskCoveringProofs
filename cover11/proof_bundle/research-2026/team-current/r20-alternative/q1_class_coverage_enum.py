# -*- coding: utf-8 -*-
"""
r20-alternative / independent rebuild of the q1 class enumeration + saved-upper audit (v2).

Enumeration rebuilt from scratch (no trust in the doc narrative):
  core 8-cycle = [0,2,3,4,5,6,7,8]  (9-ring cycle 0..8 with the ear middle site 1 removed)
  start s -> rotate the core, then:
      degree-5 hub span (span 3) : a_s = first 4 sites, b_s = c[3:] + c[:1]  (6 sites, = degree-7 hub)
      balanced (span 4)         : a_s = first 5 sites, b_s = c[4:] + c[:1]  (5 sites, = other hub)
  generators: R (ring reflection i -> (2-i) mod 9, applied to both site sets) and, when the two hubs have
  EQUAL degree (balanced case), the hub swap (a,b) -> (b,a).  Orbits are computed by union-find closure.
Then: read every saved certificate JSON, verify strict < pi exactly, and list per-class evidence.
"""
import json
from fractions import Fraction as F
from pathlib import Path

LEAD = Path(__file__).resolve().parent.parent / "lead"
CORE = [0, 2, 3, 4, 5, 6, 7, 8]
R = lambda i: (2 - i) % 9
PI_LOWER = F(314159, 100000)          # 3.14159 < pi


def pairs(size, blen):
    out = {}
    for s in range(8):
        c = CORE[s:] + CORE[:s]
        out[s] = (frozenset(c[:blen]), frozenset(c[blen - 1:] + c[:1]))
    return out


def orbits(pairs, use_swap):
    parent = {s: s for s in pairs}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x

    def union(x, y):
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[max(rx, ry)] = min(rx, ry)

    key = {s: v for s, v in pairs.items()}
    rev = {}
    for s, v in key.items():
        rev.setdefault(v, s)
    for s, (a, b) in key.items():
        for w in [((frozenset(map(R, a)), frozenset(map(R, b))))]:
            if w in rev:
                union(s, rev[w])
        if use_swap and (b, a) in rev:                 # only meaningful for equal degrees
            union(s, rev[(b, a)])
    groups = {}
    for s in key:
        groups.setdefault(find(s), []).append(s)
    return sorted(sorted(v) for v in groups.values())


print("=" * 96)
print("[1] q1 degree-(5,7) : degree-5 hub = 4-site block, degree-7 hub = 6 sites")
p5 = pairs(3, 4)
orb5_R = orbits(p5, use_swap=False)
orb5_RS = orbits(p5, use_swap=True)
print("    orbits under R alone      =", orb5_R)
print("    orbits under R + hub swap =", orb5_RS, " (swap is the identity here: degree-5 <> degree-7)")
print("    claimed in Q1-DEGREE5-EXCLUSION.md = [[0,6],[1,5],[2,4],[3],[7]]  -> match:",
      orb5_R == sorted([[0, 6], [1, 5], [2, 4], [3], [7]]))

print("\n[2] q1 balanced (6,6) : each hub = 5-site block (4 edges)")
p6 = pairs(4, 5)
orb6_R = orbits(p6, use_swap=False)
orb6_RS = orbits(p6, use_swap=True)
print("    orbits under R alone      =", orb6_R)
print("    orbits under R + hub swap =", orb6_RS)
print("    claimed in Q1-BALANCED-EXCLUSION.md = [[0,1,4,5],[2,3,6,7]] -> match (R+swap):",
      orb6_RS == sorted([[0, 1, 4, 5], [2, 3, 6, 7]]))
print("    => the balanced class claim NEEDS the hub-swap identification (equal degrees make it legal);")
print("       R alone would give 4 classes, leaving the certificates at starts 0,2 covering only {0,5},{2,3}.")

print("\n" + "=" * 96)
print("[3] saved upper bounds: strict-below-pi audit (exact rational comparison of recorded strings)")
CERT = [("span3 start0", "shared_factor_certificate_0_3.json", "shared-factor dual (5,7)"),
        ("span3 start1", "shared_factor_certificate_1_3.json", "shared-factor dual (5,7)"),
        ("span3 start2", "shared_factor_certificate_2_3.json", "shared-factor dual (5,7)"),
        ("span3 start3", "shared_factor_certificate_3_3.json", "shared-factor dual (5,7)"),
        ("span3 start7", "compatible_position_certificate.json", "compatible-edge support (5,7)"),
        ("span4 start0", "shared_moment_dense_certificate_0_4.json", "shared-moment dense dual (6,6)"),
        ("span4 start2", "shared_moment_dense_certificate_2_4.json", "shared-moment dense dual (6,6)")]
def parse_iv(s):
    a, b = s.strip().strip("[]").split(",")
    return F(a.strip()), F(b.strip())

rows = []
for tag, fn, kind in CERT:
    d = json.loads((LEAD / fn).read_text(encoding="utf-8"))
    lo, hi = parse_iv(d["upper"]); plo, phi = parse_iv(d["pi"])
    fac = d.get("factors", [])
    sum_hi = sum(F(str(f["upper"])) for f in fac) if fac else None
    rows.append((tag, fn, kind, d["start"], d["span"], lo, hi, plo, phi, bool(d.get("strict")), len(fac), sum_hi))
    print("   %-13s %-40s start=%d span=%d  strict=%s factors=%d" % (tag, fn, d["start"], d["span"], d.get("strict"), len(fac)))
    print("       true upper = [%s, %s]" % (str(float(lo))[:26], str(float(hi))[:26]))
    print("       hi < 3.14159 (exact rational)? %s | hi < pi_lo(recorded)? %s | recorded pi_lo > 3.14159? %s"
          % (hi < PI_LOWER, hi < plo, plo > PI_LOWER))
    if sum_hi is not None:
        print("       INFO: sum of the %d factor uppers = %.9f  (the decomposition constant is NOT recorded"
              % (len(fac), float(sum_hi)))
        print("             in the json, so the total cannot be re-derived from it; magnitude only)")

print("\n[4] class coverage")
cov5 = {0: "shared_factor_certificate_0_3", 1: "shared_factor_certificate_1_3",
        2: "shared_factor_certificate_2_3", 3: "shared_factor_certificate_3_3",
        7: "compatible_position_certificate"}
cov6 = {0: "shared_moment_dense_certificate_0_4", 2: "shared_moment_dense_certificate_2_4"}
ok5 = True
for cls in orb5_R:
    hit = [s for s in cls if s in cov5]
    print("   (5,7) class %-10s certified=%s  propagated by R=%s" % (cls, hit, sorted(set(cls) - set(hit))))
    ok5 &= bool(hit)
ok6 = True
for cls in orb6_RS:
    hit = [s for s in cls if s in cov6]
    print("   (6,6) class %-14s certified=%s  propagated (R+swap)=%s" % (cls, hit, sorted(set(cls) - set(hit))))
    ok6 &= bool(hit)
print("   every (5,7) start covered:", ok5, "| every (6,6) start covered:", ok6)
print("   starts without a certificate file: (5,7):", sorted(set(range(8)) - set(cov5)),
      " (6,6):", sorted(set(range(8)) - set(cov6)))

print("\n[5] exact-fraction control for the start7 class")
fr = json.loads((LEAD / "compatible_position_fraction.json").read_text(encoding="utf-8"))
u = F(fr["upper_rational"])
print("   upper_rational =", fr["upper_rational"], "~", float(u), "| < 3.14159 ?", u < PI_LOWER,
      "| < pi_lower given?", u < F(str(fr["pi_lower"])), "| N =", fr["N"])
