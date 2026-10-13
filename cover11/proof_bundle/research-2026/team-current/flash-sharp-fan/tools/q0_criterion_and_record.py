# -*- coding: utf-8 -*-
"""Own instrument: validation of the q=0 finite criterion + record data.

Criterion (Theorem in SHARP-FAN-Q0.md), for configurations whose clipped Voronoi
cellulation is the q=0 two-fan:
   D covered  <=>  (A) the nine arcs cover dD
                /\ (B) every ring-ring fan triangle (h_j,c_k,c_{k+1}) has circumradius <= r
                /\ (C) the two hub-hub triangles (h1,h2,c_u), (h1,h2,c_v) have circumradius <= r
and (B) <=> (B_tip): |h_j - v_k| <= r  (v_k = inner crossing of dD-B(c_k),dD-B(c_{k+1})).

Independent covering check: dense sampling of D (grid) + dense sampling of dD.
"""
import math, os, random, json
import numpy as np
from scipy.spatial import Delaunay

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, os.pardir, "out")
os.makedirs(OUT, exist_ok=True)
rng = random.Random(11)
lines = []
def P(s=""):
    lines.append(s); print(s)

def rho_of(t, r):
    return math.cos(t) - math.sqrt(max(0.0, r * r - math.sin(t) ** 2))

def random_ledger(r, slack=True):
    """returns (t[9], gamma[9], centres[9]) legal: arcs essential, cyclic, cover dD."""
    tmax = math.asin(r)
    for _ in range(400):
        t = [rng.uniform(0.80 * tmax, 0.995 * tmax) for _ in range(9)]
        S = sum(t)
        if S < math.pi:
            continue
        need = 2 * S - 2 * math.pi                      # = sum o
        w = [rng.random() for _ in range(9)]
        sw = sum(w); o = [need * x / sw for x in w]
        gam = [t[i] + t[(i + 1) % 9] - o[i] for i in range(9)]
        if min(gam) <= 1e-9:
            continue
        if min(2 * t[i] - o[(i - 1) % 9] - o[i] for i in range(9)) <= 1e-9:
            continue
        centres = []
        phi = rng.uniform(0, 2 * math.pi)
        for i in range(9):
            a = rho_of(t[i], r)
            centres.append(np.array([a * math.cos(phi), a * math.sin(phi)]))
            phi += gam[i]
        return t, o, gam, centres
    return None

def fan_structure(C, ring, hub):
    """checks the q=0 two-fan Delaunay structure; returns (ok, info)."""
    tri = Delaunay(C)
    simp = tri.simplices
    if len(simp) != 11:
        return False, {"reason": "n_tri=%d" % len(simp), "tri": simp}
    edges = set()
    for s in simp:
        for k in range(3):
            edges.add(tuple(sorted((int(s[k]), int(s[(k + 1) % 3])))))
    ring_set, hub_set = set(ring), set(hub)
    rr = [e for e in edges if e[0] in ring_set and e[1] in ring_set]
    if len(rr) != 9:
        return False, {"reason": "ring_ring_edges=%d" % len(rr), "tri": simp}
    hh = [e for e in edges if e[0] in hub_set and e[1] in hub_set]
    if len(hh) != 1:
        return False, {"reason": "hub_hub_edges=%d" % len(hh), "tri": simp}
    # ring cyclic order from geometry
    arg = {i: math.atan2(C[i][1], C[i][0]) for i in ring}
    order = sorted(ring, key=lambda i: arg[i])
    pos = {c: k for k, c in enumerate(order)}
    def gd(i, j):
        d = abs(pos[i] - pos[j]) % 9
        return min(d, 9 - d)
    if any(gd(*e) != 1 for e in rr):
        return False, {"reason": "non-consecutive ring chord", "tri": simp}
    blocks = {}
    for h in hub:
        nb = [j for e in edges if h in e for j in (e[0], e[1]) if j != h and j in ring_set]
        ps = sorted(pos[j] for j in nb)
        blocks[h] = ps
        m = len(ps)
        # cyclic contiguity: all but at most one cyclic step equal 1, and the run is proper
        steps = [(ps[(i + 1) % m] - ps[i]) % 9 for i in range(m)]
        if steps.count(1) < m - 1 or m == 9:
            return False, {"reason": "hub %d neighbours not cyclically contiguous" % h, "tri": simp}
    # transitions = ring cells adjacent to both hubs
    nb1 = set(j for e in edges if hub[0] in e for j in e if j in ring_set)
    nb2 = set(j for e in edges if hub[1] in e for j in e if j in ring_set)
    trans = sorted(nb1 & nb2, key=lambda i: pos[i])
    if len(trans) != 2:
        return False, {"reason": "transitions=%s" % trans, "tri": simp}
    # every triangle contains a hub, and the 9 fan triangles are the ring-ring edges
    for s in simp:
        if not any(int(i) in hub_set for i in s):
            return False, {"reason": "ring-only triangle", "tri": simp}
    return True, {"order": order, "pos": pos, "tri": simp, "edges": edges,
                  "trans": trans, "blocks": blocks, "hh": hh[0]}

def circum_info(C, s):
    a, b, c = (C[int(i)] for i in s)
    d = 2 * (a[0]*(b[1]-c[1]) + b[0]*(c[1]-a[1]) + c[0]*(a[1]-b[1]))
    if abs(d) < 1e-15:
        return float("inf"), np.array([0.0, 0.0])
    ux = ((a[0]**2+a[1]**2)*(b[1]-c[1]) + (b[0]**2+b[1]**2)*(c[1]-a[1]) + (c[0]**2+c[1]**2)*(a[1]-b[1]))/d
    uy = ((a[0]**2+a[1]**2)*(c[0]-b[0]) + (b[0]**2+b[1]**2)*(a[0]-c[0]) + (c[0]**2+c[1]**2)*(b[0]-a[0]))/d
    o = np.array([ux, uy])
    return float(np.linalg.norm(o - a)), o

def covered_by_sampling(C, R, n=420, nphi=2000):
    """independent covering test: cartesian grid in D + polar grid on dD."""
    bad = None
    xs = np.linspace(-1, 1, n)
    gx, gy = np.meshgrid(xs, xs)
    mask = gx**2 + gy**2 <= 1.0
    pts = np.stack([gx[mask], gy[mask]], axis=1)
    d = np.min(np.linalg.norm(pts[:, None, :] - C[None, :, :], axis=2), axis=1)
    worst = float(d.max())
    ph = np.linspace(0, 2*np.pi, nphi, endpoint=False)
    bd = np.stack([np.cos(ph), np.sin(ph)], axis=1)
    db = np.min(np.linalg.norm(bd[:, None, :] - C[None, :, :], axis=2), axis=1)
    worst_b = float(db.max())
    return worst, worst_b

def inner_crossing(c1, c2, R):
    d = np.linalg.norm(c2 - c1)
    m = (c1 + c2) / 2
    h2 = R * R - d * d / 4
    if h2 <= 0:
        return m
    hh = math.sqrt(h2)
    perp = np.array([-(c2 - c1)[1], (c2 - c1)[0]]) / d
    a, b = m + hh * perp, m - hh * perp
    return a if np.linalg.norm(a) < np.linalg.norm(b) else b

# =====================================================================
P("=" * 78)
P("PART 1: finite criterion (Lemma 3) vs independent sampling, random configurations")
P("  general form: D covered <=> [every Delaunay circumcentre inside D has R <= r] AND [dD covered]")
P("  fan form: specialised to (A)+(B)+(C) when the q=0 two-fan structure holds")
P("=" * 78)
stats = {"n": 0, "agree": 0, "disagree": 0, "fan": 0, "fan_agree": 0,
         "fan_disagree": 0, "BvsTip": 0, "BvsTip_bad": 0, "no_ledger": 0, "near_tie": 0,
         "no_fan": 0, "hub_not_interior": 0}
worst_disagree = None
worst_fan = None
for trial in range(600):
    R = rng.uniform(0.33, 0.385)
    got = random_ledger(R)
    if not got:
        stats["no_ledger"] += 1
        continue
    t, o, gam, ring_centres = got
    ring = list(range(9))
    hub = [9, 10]
    hs = []
    for _ in range(2):
        ang = rng.uniform(0, 2*math.pi)
        rad = rng.uniform(0.0, max(0.02, 1.02 - R))     # mostly interior, a few outside
        hs.append(np.array([rad*math.cos(ang), rad*math.sin(ang)]))
    C = np.array(ring_centres + hs)
    tri = Delaunay(C)
    # general Lemma 3 test
    gen = True
    for s in tri.simplices:
        rr, cc = circum_info(C, s)
        if np.linalg.norm(cc) < 1.0 and rr > R + 1e-12:
            gen = False
            break
    wmax, wmaxb = covered_by_sampling(C, R)
    if abs(wmax - R) < 4e-3 or abs(wmaxb - R) < 4e-3:
        stats["near_tie"] += 1
        continue                                        # near-tie: sampling not decisive
    sampled = (wmax <= R + 1e-6) and (wmaxb <= R + 1e-6)
    stats["n"] += 1
    if gen == sampled:
        stats["agree"] += 1
    else:
        stats["disagree"] += 1
        if worst_disagree is None:
            worst_disagree = (gen, sampled, wmax, wmaxb, R)
    # fan specialisation
    ok, info = fan_structure(C, ring, hub)
    if not ok:
        stats["no_fan"] += 1
        continue
    stats["fan"] += 1
    if any(C[j] @ C[j] > (1 - R)**2 for j in hub):
        stats["hub_not_interior"] += 1
        continue                                        # branch requires |h|+r<1
    A, B, Cc, tip_ok = True, True, True, True
    for s in tri.simplices:
        s = [int(x) for x in s]
        hset = [i for i in s if i in hub]
        rs = [i for i in s if i in ring]
        rr_, _ = circum_info(C, s)
        if len(hset) == 2:
            Cc = Cc and (rr_ <= R + 1e-12)
        else:
            B = B and (rr_ <= R + 1e-12)
            i, j = rs
            d = (info["pos"][i] - info["pos"][j]) % 9
            if min(d, 9 - d) == 1:
                v = inner_crossing(C[i], C[j], R)
                ok_tip = np.linalg.norm(C[hset[0]] - v) <= R + 1e-12
                tip_ok = tip_ok and ok_tip
    stats["BvsTip"] += 1
    if tip_ok != B:
        stats["BvsTip_bad"] += 1
    crit = A and B and Cc
    if crit == sampled:
        stats["fan_agree"] += 1
    else:
        stats["fan_disagree"] += 1
        if worst_fan is None:
            worst_fan = (crit, sampled, B, Cc, wmax, R)
P("  configurations tested          : %d ; general criterion agree=%d disagree=%d"
  % (stats["n"], stats["agree"], stats["disagree"]))
P("  fan-class configurations       : %d ; criterion agree=%d disagree=%d"
  % (stats["fan"], stats["fan_agree"], stats["fan_disagree"]))
P("  (B) vs (B_tip) on fan-class    : %d tests, mismatches=%d"
  % (stats["BvsTip"], stats["BvsTip_bad"]))
P("  drops: ledger-gen failed=%d ; sampling near-tie=%d ; not fan=%d ; hub not interior=%d"
  % (stats["no_ledger"], stats["near_tie"], stats["no_fan"], stats["hub_not_interior"]))
if worst_disagree:
    P("  first general disagreement: criterion=%s sampling=%s (grid %.6f, boundary %.6f, R=%.5f)"
      % worst_disagree)
if worst_fan:
    P("  first fan disagreement: crit=%s sampling=%s B=%s C=%s (grid %.6f, R=%.5f)" % worst_fan)

# =====================================================================
P("=" * 78)
P("PART 2: the record configuration -- finite system data")
P("=" * 78)
ROOT = os.path.abspath(os.path.join(HERE, os.pardir, os.pardir, os.pardir, os.pardir))
with open(os.path.join(ROOT, "n11", "upper", "certified_object.json"), "r", encoding="utf-8") as f:
    obj = json.load(f)
C = np.array([[int(a) / 1e17, int(b) / 1e17] for a, b in obj["centers_scaled_1e17"]])
R = 0.379983853119838689722261606136093214308718956152215317048319
mod = np.array([np.hypot(*c) for c in C])
ring = [i for i in range(11) if mod[i] + R >= 1]
hub = [i for i in range(11) if mod[i] + R < 1]
ok, info = fan_structure(C, ring, hub)
P("  fan structure holds: %s ; transitions %s ; blocks %s ; hub-hub %s"
  % (ok, info["trans"], info["blocks"], info["hh"]))
order, pos = info["order"], info["pos"]
P("  cyclic ring order: %s" % order)
# tips
tip = {}
for k, i in enumerate(order):
    j = order[(k + 1) % 9]
    tip[(i, j)] = (inner_crossing(C[i], C[j], R), k)
# rings/arcs/hubs tightness
P("  %.4s %-6s %-9s %-9s %-9s %-9s" % ("pair", "hub", "circR-r", "tipdist-r", "|tip|", "a*="))
a_star = min(mod[i] for i in ring) - R
for s in info["tri"]:
    s = [int(x) for x in s]
    hs = [i for i in s if i in hub]
    rs = [i for i in s if i in ring]
    rr, o = circum_info(C, s)
    if len(hs) == 2:
        P("  hub-hub %s : circR-r=%+.3e  (transition rings %s)" % ((hs, rs), rr - R, rs))
    else:
        i, j = rs
        v, k = tip[(i, j)] if (i, j) in tip else tip[(j, i)]
        P("  %-9s hub %-2d circR-r=%+.3e  tipdist-r=%+.3e  |tip|=%.6f  a*=%.6f"
          % ((i, j), hs[0], rr - R, np.linalg.norm(C[hs[0]] - v) - R, np.linalg.norm(v), a_star))
n_tight_circ = sum(1 for s in info["tri"] if abs(circum_info(C, [int(x) for x in s])[0] - R) < 1e-9)
n_tight_tip = 0; n_t = 0
for (i, j), (v, k) in tip.items():
    n_t += 1
    hs = [h for h in hub if abs(np.linalg.norm(C[h] - v) - R) < 1e-9]
    n_tight_tip += 1 if hs else 0
P("  tight Voronoi vertices: %d/11 ; tips exactly on their hub circle: %d/9" % (n_tight_circ, n_tight_tip))
# hub-free necessary condition: MEC of the two contiguous tip blocks
def mec(pts):
    pts = np.array(pts); best = 1e9; n = len(pts)
    for i in range(n):
        for j in range(i+1, n):
            m = (pts[i]+pts[j])/2; rr = np.linalg.norm(pts[i]-pts[j])/2
            if all(np.linalg.norm(p-m) <= rr+1e-12 for p in pts):
                best = min(best, rr)
    for i in range(n):
        for j in range(i+1, n):
            for k in range(j+1, n):
                a, b, c = pts[i], pts[j], pts[k]
                d = 2*(a[0]*(b[1]-c[1])+b[0]*(c[1]-a[1])+c[0]*(a[1]-b[1]))
                if abs(d) < 1e-18: continue
                ux = ((a@a)*(b[1]-c[1])+(b@b)*(c[1]-a[1])+(c@c)*(a[1]-b[1]))/d
                uy = ((a@a)*(c[0]-b[0])+(b@b)*(a[0]-c[0])+(c@c)*(b[0]-a[0]))/d
                m = np.array([ux, uy]); rr = np.linalg.norm(m-a)
                if all(np.linalg.norm(p-m) <= rr+1e-12 for p in pts):
                    best = min(best, rr)
    return best
def block_tips(pos_list, order, tip):
    """tips of the ring-ring fan edges inside a cyclic block of ring positions."""
    m = len(pos_list)
    start = next(i for i in range(m) if (pos_list[i] - 1) % 9 not in pos_list)
    cyc = [pos_list[(start + k) % m] for k in range(m)]
    out = []
    for k in range(m - 1):
        i = order[cyc[k]]; j = order[cyc[k + 1]]
        out.append(tip[(i, j)][0] if (i, j) in tip else tip[(j, i)][0])
    return out

for h in hub:
    blk = sorted(info["blocks"][h])
    pts = block_tips(blk, order, tip)
    P("  hub %d: block %s ; #tips=%d ; MEC(tips)=%.6f (r=%.6f) ; hub |h|=%.6f ; max tip dist=%.6f"
      % (h, blk, len(pts), mec(pts), R, mod[h], max(np.linalg.norm(C[h]-x) for x in pts)))
P("  a* = %.6f  (min_k |c_k| - r) ; min |tip| = %.6f"
  % (a_star, min(np.linalg.norm(v) for v, k in tip.values())))

with open(os.path.join(OUT, "q0_criterion_and_record.txt"), "w", encoding="utf-8") as f:
    f.write("\n".join(lines) + "\n")
