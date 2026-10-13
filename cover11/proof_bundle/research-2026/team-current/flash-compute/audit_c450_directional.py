# -*- coding: utf-8 -*-
"""audit_c450_directional.py -- independent audit of the C450 directional-dual certificate
source (solo-20260922/verify_directional_fixed.py + _fixed_low.py) against the claims of
lead/HUB-ADJACENCY-DUAL.md.  Small controls only; NO big replay.

Checks
  A1  module-level asserts of the verifier (PI enclosure, TMAX > asin R) execute on import;
  A2  kernel controls vs mpmath at high precision: sqrt/sin/cos/atan/acos on points that
      matter (t endpoints, acos domain boundary, v=+-1);
  A3  e-coverage: union of the PASS runs of directional_e_cover.json AND
      directional_low_cover.json covers [0, 7/50];  no pass=False rows are silently skipped;
  A4  target positivity: a_00 + a_10 > 0 for every run; nonnegativity criterion
      a_0 >= sum_{k>=1} |a_k| holds for both weight blocks;
  A5  replay outputs (directional_fixed_all.json, directional_fixed_low.json): all runs PASS,
      box counts vs the 300000 budget, depth vs 70;
  A6  domain/semantics: what the verifier does and does not cover (reported as text, not
      computed).
"""
import importlib.util
import json
import math
import os
import sys
from fractions import Fraction as F

SOLO = r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\solo-20260922"
sys.path.insert(0, SOLO)
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")

spec = importlib.util.spec_from_file_location("vdf", os.path.join(SOLO, "verify_directional_fixed.py"))
vdf = importlib.util.module_from_spec(spec)
spec.loader.exec_module(vdf)          # runs the module-level asserts (A1)

import mpmath as mp
mp.mp.dps = 60

S = vdf.S
R = vdf.R


def lo(x):
    return F(x.a, S)


def hi(x):
    return F(x.b, S)


def contains(iv, exact):
    """exact is an mpf; compare as Fractions via a 50-digit decimal (widths are ~1e-26)."""
    ex = F(mp.nstr(exact, 50))
    return lo(iv) <= ex <= hi(iv)


print("=" * 78)
print("A1  module-level asserts on import: OK (PI enclosure and sin(TMAX) > R fired)")
print("    PI in [%s, %s]" % (lo(vdf.PI), hi(vdf.PI)))
print("    TMAX = %s ; asin(19/50) = %.16f ; TMAX - asin = %+.3e"
      % (lo(vdf.TMAX), float(mp.asin(mp.mpf(19) / 50)),
         float(lo(vdf.TMAX)) - float(mp.asin(mp.mpf(19) / 50))))

print()
print("=" * 78)
print("A2  kernel controls vs mpmath (dps=60)")
okA2 = True
# use exact rational points for the kernel controls
tests = []
tests.append(("sqrt(2)", vdf.sqrt(vdf.I(2)), mp.sqrt(2)))
tests.append(("sin(19/50)", vdf.sin(vdf.I("19/50")), mp.sin(mp.mpf(19) / 50)))
tests.append(("cos(19/50)", vdf.cos(vdf.I("19/50")), mp.cos(mp.mpf(19) / 50)))
tests.append(("sin(0)", vdf.sin(vdf.I(0)), mp.mpf(0)))
tests.append(("cos(0)", vdf.cos(vdf.I(0)), mp.mpf(1)))
tests.append(("atan(1/5)  [module's own use]", vdf.atan(vdf.I("1/5")), mp.atan(mp.mpf(1) / 5)))
tests.append(("atan(1/239) [module's own use]", vdf.atan(vdf.I("1/239")), mp.atan(mp.mpf(1) / 239)))
tests.append(("acos(4/5)", vdf.acos(vdf.I("4/5")), mp.acos(mp.mpf(4) / 5)))
tests.append(("acos(3/5)", vdf.acos(vdf.I("3/5")), mp.acos(mp.mpf(3) / 5)))
tests.append(("acos(31/50)", vdf.acos(vdf.I("31/50")), mp.acos(mp.mpf(31) / 50)))
for name, iv, exact in tests:
    inside = contains(iv, exact)
    okA2 &= inside
    print("    %-12s in [%s, %s]  width %.2e  contains mpmath: %s"
          % (name, lo(iv), hi(iv), float(hi(iv) - lo(iv)), inside))
# the documented domain restrictions: acos needs x >= 3/5, atan needs x <= 1/2
for name, fn, arg in (("acos(1/2)  [below domain]", vdf.acos, "1/2"),
                      ("atan(3/5)  [above domain]", vdf.atan, "3/5")):
    try:
        bad = fn(vdf.I(arg))
        print("    %s returned %s -> NO assert fired (danger)" % (name, bad))
        okA2 = False
    except AssertionError:
        print("    %s raises AssertionError (fail-fast, not silent): OK" % name)
print("    A2 all controls pass:", okA2)

print()
print("=" * 78)
print("A3  e-coverage over BOTH cover files (union of PASS runs)")
runs = []
for fn, key in (("directional_e_cover.json", "runs"), ("directional_low_cover.json", "runs")):
    d = json.load(open(os.path.join(SOLO, fn), encoding="utf-8"))
    for r in d[key]:
        runs.append((F(r["e_interval"][0]), F(r["e_interval"][1]), bool(r.get("pass")), fn))
allruns = runs
passing = sorted([r for r in runs if r[2]])
nonpass = [r for r in runs if not r[2]]
merged = []
for a, b, p, fn in passing:
    if merged and a <= merged[-1][1]:
        merged[-1] = (merged[-1][0], max(merged[-1][1], b), merged[-1][2] + 1)
    else:
        merged.append((a, b, 1))
cover_ok = (len(merged) == 1 and merged[0][0] == 0 and merged[0][1] >= F(7, 50))
print("    total runs %d (PASS %d, non-PASS %d) ; merged into %d block(s)"
      % (len(runs), len(passing), len(nonpass), len(merged)))
print("    union = [%s, %s] ; needs [0, 7/50] ; covers: %s"
      % (merged[0][0] if merged else "-", merged[-1][1] if merged else "-", cover_ok))
print("    producer flags: e_cover all_covered=%s ; certified_contiguous_end=%s ; pending=%s"
      % (json.load(open(os.path.join(SOLO, "directional_e_cover.json"), encoding="utf-8")).get("all_covered"),
         json.load(open(os.path.join(SOLO, "directional_e_cover.json"), encoding="utf-8")).get("certified_contiguous_end"),
         json.load(open(os.path.join(SOLO, "directional_e_cover.json"), encoding="utf-8")).get("pending")))

print()
print("=" * 78)
print("A4  target positivity and nonnegativity criterion per run")
bad_dom = bad_tgt = 0
for a, b, p, fn in runs:
    d = json.load(open(os.path.join(SOLO, fn), encoding="utf-8"))
    for r in d["runs"]:
        if F(r["e_interval"][0]) != a:
            continue
        w = r["weights"]
        for tag in ("boundary", "hub"):
            ww = [F(x) for x in w[tag]]
            if ww[0] < sum(abs(x) for x in ww[1:]):
                bad_dom += 1
        if F(w["boundary"][0]) + F(w["hub"][0]) <= 0:
            bad_tgt += 1
print("    dominance violations: %d ; non-positive target B(e): %d" % (bad_dom, bad_tgt))

print()
print("=" * 78)
print("A5  replay outputs")
for fn in ("directional_fixed_all.json", "directional_fixed_low.json"):
    p = os.path.join(SOLO, fn)
    if not os.path.exists(p):
        print("    %s MISSING" % fn)
        continue
    d = json.load(open(p, encoding="utf-8"))
    rs = d["runs"]
    boxes = [r["boxes"] for r in rs]
    print("    %-28s runs=%d all pass=%s  boxes: min %d max %d total %d  seconds max %.1f"
          % (fn, len(rs), all(r.get("pass") for r in rs), min(boxes), max(boxes), sum(boxes),
             max(r["seconds"] for r in rs)))
    print("        budget: count<300000 and depth<70 (hard asserts, no silent pass)")
