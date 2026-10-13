# -*- coding: utf-8 -*-
"""Own instrument: controls for the crossing/tip lemmas.

L1  (crossing separation)  : for two ring disks whose arcs on dD overlap, the
                             crossing farther from the origin satisfies |v_out| >= 1.
L2a (exact characterisation): R(h,c1,c2) <= r  <=>  h in B(v+,r) and h not in int B(v-,r),
                             where v+ is the crossing on h's side of the midpoint M.
L2b (necessary tip form)   : R(h,c1,c2) <= r  =>  |h - v_in| <= r   (|h|+r<1, |v_out|>=1).
L2c (equivalence)          : if v_in is on h's side of M then R <= r <=> |h-v_in| <= r.
Negative controls (must FAIL the highlighted direction):
 N1: arcs disjoint (no tie point) -> |v_out| >= 1 may fail.
 N2: |h| + r > 1 (hub not strictly interior) -> L2b implication may fail.
"""
import math, os, random, json
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, os.pardir, "out")
os.makedirs(OUT, exist_ok=True)
rng = random.Random(20260924)
lines = []
def P(s=""):
    lines.append(s); print(s)

# ---------- helpers ----------
def rho_of(t, r):
    """inner root: centre radius of a ring disk with arc half-width t."""
    return math.cos(t) - math.sqrt(max(0.0, r * r - math.sin(t) ** 2))

def t_of(a, r):
    ca = (1 + a * a - r * r) / (2 * a)
    return math.acos(max(-1.0, min(1.0, ca)))

def crossings(c1, c2, r):
    d = np.linalg.norm(c2 - c1)
    m = (c1 + c2) / 2
    h2 = r * r - d * d / 4
    if h2 < 0:
        return None, None, None
    hh = math.sqrt(h2)
    perp = np.array([-(c2 - c1)[1], (c2 - c1)[0]]) / d
    a, b = m + hh * perp, m - hh * perp
    return a, b, m

def circum_R(h, c1, c2):
    ax, ay = c1; bx, by = c2; cx, cy = h
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    if abs(d) < 1e-15:
        return float("inf")
    ux = ((ax*ax+ay*ay)*(by-cy) + (bx*bx+by*by)*(cy-ay) + (cx*cx+cy*cy)*(ay-by)) / d
    uy = ((ax*ax+ay*ay)*(cx-bx) + (bx*bx+by*by)*(ax-cx) + (cx*cx+cy*cy)*(bx-ax)) / d
    return math.hypot(ux - ax, uy - ay)

# ---------- random legal ring pair ----------
def random_ring_pair(r):
    """two ring disks whose actual arcs on dD overlap nontrivially, arcs essential."""
    for _ in range(400):
        t1 = rng.uniform(0.10, math.asin(r) * 0.995)
        t2 = rng.uniform(0.10, math.asin(r) * 0.995)
        lo, hi = abs(t1 - t2), min(t1 + t2, 2 * math.pi - t1 - t2)
        if hi <= lo:
            continue
        g = rng.uniform(lo, min(hi, lo + 0.6 * (hi - lo) + 1e-9))
        a1, a2 = rho_of(t1, r), rho_of(t2, r)
        if a1 <= 0 or a2 <= 0:
            continue
        p1 = np.array([a1, 0.0])
        p2 = np.array([a2 * math.cos(g), a2 * math.sin(g)])
        va, vb, m = crossings(p1, p2, r)
        if va is None:
            continue
        if np.linalg.norm(p1 - p2) > 2 * r - 1e-12:
            continue
        return p1, p2, t1, t2, g
    return None

P("=" * 78)
P("L1  |v_out| >= 1 for arcs that overlap (o >= 0).  3400 random pairs at r in [0.30,0.38]")
worst = 1e9; bad = 0; n = 0
for _ in range(3400):
    r = rng.uniform(0.30, 0.38)
    got = random_ring_pair(r)
    if not got:
        continue
    p1, p2, t1, t2, g = got
    va, vb, m = crossings(p1, p2, r)
    vout = max([va, vb], key=lambda p: np.linalg.norm(p))
    vin = min([va, vb], key=lambda p: np.linalg.norm(p))
    o = t1 + t2 - g                      # arc overlap (rad)
    n += 1
    worst = min(worst, np.linalg.norm(vout) - 1.0)
    if np.linalg.norm(vout) < 1 - 1e-12:
        bad += 1
P("    samples=%d  min(|v_out|-1) = %+.3e  violations=%d  (o in [%.1e,%.3f])"
  % (n, worst, bad, 0.0, 0.0))

P("    control N1 (arcs disjoint, o<0): |v_out|>=1 must NOT be forced")
n1 = 0; n1bad = 0; worst1 = 1e9
for _ in range(3000):
    r = rng.uniform(0.30, 0.38)
    t1 = rng.uniform(0.12, math.asin(r) * 0.99)
    t2 = rng.uniform(0.12, math.asin(r) * 0.99)
    lo = abs(t1 - t2)
    g = lo * 0.5                          # arcs disjoint
    a1, a2 = rho_of(t1, r), rho_of(t2, r)
    if a1 <= 0 or a2 <= 0 or g <= 1e-9:
        continue
    p1 = np.array([a1, 0.0]); p2 = np.array([a2 * math.cos(g), a2 * math.sin(g)])
    if np.linalg.norm(p1 - p2) > 2 * r:
        continue
    va, vb, m = crossings(p1, p2, r)
    if va is None:
        continue
    vout = max([va, vb], key=lambda p: np.linalg.norm(p))
    n1 += 1
    worst1 = min(worst1, np.linalg.norm(vout) - 1.0)
    if np.linalg.norm(vout) < 1:
        n1bad += 1
P("    samples=%d  min(|v_out|-1) = %+.3e  violations=%d  (expected > 0)" % (n1, worst1, n1bad))

P("=" * 78)
P("L2a/L2b/L2c on the same random pairs: h with |h| + r < 1 (strictly interior)")
cnt = {"a": 0, "b": 0, "c_side": 0, "c_bad": 0}
maxviol_a = 0.0; maxviol_b = 0.0; maxviol_c = 0.0
n2 = 0
for _ in range(6000):
    r = rng.uniform(0.30, 0.38)
    got = random_ring_pair(r)
    if not got:
        continue
    p1, p2, t1, t2, g = got
    va, vb, m = crossings(p1, p2, r)
    vout = max([va, vb], key=lambda p: np.linalg.norm(p))
    vin = min([va, vb], key=lambda p: np.linalg.norm(p))
    # random strictly interior hub
    ang = rng.uniform(0, 2 * math.pi); rad = rng.uniform(0, 1 - r - 1e-6)
    h = np.array([rad * math.cos(ang), rad * math.sin(ang)])
    # side of M: sign of (h-M).(v_in-M)
    side_in = float(np.dot(h - m, vin - m))
    # v+ = crossing on h's side of M
    vplus = va if float(np.dot(h - m, va - m)) > 0 else vb
    vminus = vb if vplus is va else va
    R = circum_R(h, p1, p2)
    # L2a: R <= r  <=>  h in B(v+,r) and h not in int B(v-,r)
    lhs = (R <= r + 1e-12)
    rhs = (np.linalg.norm(h - vplus) <= r + 1e-12) and (np.linalg.norm(h - vminus) >= r - 1e-12)
    if lhs != rhs:
        maxviol_a = max(maxviol_a, abs(R - r))
        cnt["a"] += 1
    # L2b: R <= r => |h - vin| <= r
    if R <= r + 1e-12 and np.linalg.norm(h - vin) > r + 1e-12:
        cnt["b"] += 1
        maxviol_b = max(maxviol_b, np.linalg.norm(h - vin) - r)
    # L2c: side_in > 0 => (R <= r <=> |h-vin| <= r)
    if side_in > 0:
        cnt["c_side"] += 1
        if (R <= r + 1e-12) != (np.linalg.norm(h - vin) <= r + 1e-12):
            cnt["c_bad"] += 1
            maxviol_c = max(maxviol_c, abs(np.linalg.norm(h - vin) - r))
    n2 += 1
P("    samples=%d" % n2)
P("    L2a mismatches            : %d  (worst |R-r| = %.2e)" % (cnt["a"], maxviol_a))
P("    L2b violations (R<=r but tip far): %d  (worst excess = %.2e)" % (cnt["b"], maxviol_b))
P("    L2c samples with tip on h's side: %d ; mismatches: %d (worst = %.2e)"
  % (cnt["c_side"], cnt["c_bad"], maxviol_c))

P("    control N2 (h NOT strictly interior, |h| + r > 1): L2b may fail -- count violations")
n3 = 0; n3bad = 0; worst3 = 0.0
for _ in range(6000):
    r = rng.uniform(0.30, 0.38)
    got = random_ring_pair(r)
    if not got:
        continue
    p1, p2, t1, t2, g = got
    va, vb, m = crossings(p1, p2, r)
    vout = max([va, vb], key=lambda p: np.linalg.norm(p))
    vin = min([va, vb], key=lambda p: np.linalg.norm(p))
    ang = rng.uniform(0, 2 * math.pi); rad = rng.uniform(1.0, 1.2)
    h = np.array([rad * math.cos(ang), rad * math.sin(ang)])
    R = circum_R(h, p1, p2)
    n3 += 1
    if R <= r + 1e-12 and np.linalg.norm(h - vin) > r + 1e-12:
        n3bad += 1
        worst3 = max(worst3, np.linalg.norm(h - vin) - r)
P("    samples=%d violations=%d (worst excess %.2e)  -> strict interiority is needed"
  % (n3, n3bad, worst3))

P("=" * 78)
P("L2b sharpness: how often is the implication tight / how large is the slack?")
slacks = []
prec = {"both": 0, "R_le_r": 0}
for _ in range(20000):
    r = rng.uniform(0.30, 0.38)
    got = random_ring_pair(r)
    if not got:
        continue
    p1, p2, t1, t2, g = got
    va, vb, m = crossings(p1, p2, r)
    vin = min([va, vb], key=lambda p: np.linalg.norm(p))
    ang = rng.uniform(0, 2 * math.pi); rad = rng.uniform(0, 1 - r - 1e-9)
    h = np.array([rad * math.cos(ang), rad * math.sin(ang)])
    R = circum_R(h, p1, p2)
    if R <= r:
        prec["R_le_r"] += 1
        slacks.append(r - np.linalg.norm(h - vin))
    if R <= r and np.linalg.norm(h - vin) <= r:
        prec["both"] += 1
slacks = np.array(slacks) if slacks else np.array([0.0])
P("    #(R<=r)=%d  #(both)=%d  tip-slack min/med = %.4f / %.4f (sample, not a bound)"
  % (prec["R_le_r"], prec["both"], slacks.min(), float(np.median(slacks))))

with open(os.path.join(OUT, "verify_crossing_tip.txt"), "w", encoding="utf-8") as f:
    f.write("\n".join(lines) + "\n")
