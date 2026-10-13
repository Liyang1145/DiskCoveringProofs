"""step1_geom.py -- independent geometry reconstruction at the NEW root + old/new comparison.

Outputs logs/step1_geom.txt and evidence/step1_geom.json
"""
import json, sys
from pathlib import Path
import itertools
import mpmath as mp
import numpy as np

mp.mp.dps = 60
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom import new_geom, centers_from, old_geom_centers, norm, dist, circumcenter, voronoi_vertices

OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

g = new_geom()
C = centers_from(g)
W("== n14 geometry at NEW stationary root (coordinates given by Lead, no re-solve) ==")
W("r  = %s" % mp.nstr(g["r"], 40))
W("z  = %s" % mp.nstr(g["z"], 40))
W("c  = %s" % mp.nstr(g["c"], 40))
W("a  = %s" % mp.nstr(g["a"], 40))
W("b  = %s" % mp.nstr(g["b"], 40))
W("d  = %s   (1-sqrt(r^2-c^2))" % mp.nstr(g["d"], 40))
W("s  = %s   (sqrt(1-r^2))" % mp.nstr(g["s"], 40))
W("t  = %s" % mp.nstr(g["t"], 40))
W("")
W("### sites |c| and radius r")
for i, p in enumerate(C):
    W("  %2d: (%s, %s) |c|=%s  r=|c|:%s" % (i, mp.nstr(p[0], 20), mp.nstr(p[1], 20),
                                            mp.nstr(norm(p), 20), mp.nstr(g["r"] - norm(p), 4)))
# cross-check against Lead's published numbers
lead = json.loads((Path(__file__).resolve().parents[3] / "lead/n14-actual-vertices-numeric.json").read_text(encoding="utf-8"))
lc = [tuple(mp.mpf(str(x)) for x in p) for p in lead["centers"]]
W("")
W("### center-order cross-check vs Lead n14-actual-vertices-numeric.json (max coord diff)")
W("   max |C_mine - C_lead| = %s" % mp.nstr(max(dist(C[i], lc[i]) for i in range(14)), 6))
perm = []
for i in range(14):
    perm.append(min(range(14), key=lambda j: dist(C[i], lc[j])))
W("   identity permutation? %s" % (perm == list(range(14))))

# ---- boundary arcs and anchors
R = g["r"]
active = [i for i, p in enumerate(C) if norm(p) + R >= 1 - mp.mpf("1e-30")]
inactive = [i for i in range(14) if i not in active]
W("")
W("### boundary-active / inactive at new root")
W("   active (|c|+r>=1) : %s  n=%d" % (active, len(active)))
W("   inactive          : %s" % inactive)
W("   |c|+r for active  : %s" % [mp.nstr(norm(C[i]) + R, 20) for i in active])

# arc endpoints on S^1 for each active site
eps = []
for i in active:
    ci = C[i]; rr = norm(ci)
    m = (1 + rr * rr - R * R) / (2 * rr)
    psi = mp.acos(m); phi = mp.atan2(ci[1], ci[0])
    eps.append(((phi - psi) % (2 * mp.pi), i))
    eps.append(((phi + psi) % (2 * mp.pi), i))
eps.sort(key=lambda z: z[0])

def cluster_cyclic(items, tol):
    """group items with angle gaps < tol cyclically"""
    groups = [[items[0]]]
    for a, i in items[1:]:
        if a - groups[-1][-1][0] < tol:
            groups[-1].append((a, i))
        else:
            groups.append([(a, i)])
    # cyclic merge first/last
    if len(groups) > 1 and (groups[0][0][0] + 2 * mp.pi - groups[-1][-1][0]) < tol:
        groups[0] = groups[-1] + groups[0]
        groups.pop()
    return groups

gr = cluster_cyclic(eps, mp.mpf("1e-25"))
W("")
W("### arc-endpoint clusters: n=%d sizes=%s" % (len(gr), [len(x) for x in gr]))
anchors, owners = [], []
for cl in gr:
    # circular mean
    xs = sum(mp.cos(a) for a, _ in cl); ys = sum(mp.sin(a) for a, _ in cl)
    ang = mp.atan2(ys, xs)
    sites = sorted({i for _, i in cl})
    anchors.append((mp.cos(ang), mp.sin(ang)))
    owners.append(sites)
    W("   ang=%s sites=%s  ||anchor-site|-r| max=%s" % (
        mp.nstr(ang * 180 / mp.pi, 12), sites,
        mp.nstr(max(abs(dist((mp.cos(ang), mp.sin(ang)), C[s2]) - R) for s2 in sites), 4)))
order = sorted(range(len(anchors)), key=lambda k: mp.atan2(anchors[k][1], anchors[k][0]) % (2 * mp.pi))
anchors = [anchors[k] for k in order]; owners = [owners[k] for k in order]
W("   cyclic anchor angles(deg): %s" % [float(mp.atan2(a[1], a[0]) * 180 / mp.pi) % 360 for a in anchors])
W("   owners (cyclic)          : %s" % owners)
ang = [mp.atan2(a[1], a[0]) % (2 * mp.pi) for a in anchors]
gaps = [(ang[(k + 1) % len(ang)] - ang[k]) % (2 * mp.pi) for k in range(len(ang))]
L = 2 * mp.asin(R)
W("   L* = 2asin(r*) = %s  (deg %s)" % (mp.nstr(L, 30), mp.nstr(L * 180 / mp.pi, 20)))
W("   gaps(deg) = %s" % [mp.nstr(x * 180 / mp.pi, 12) for x in gaps])
W("   gaps - L* = %s" % [mp.nstr(x - L, 6) for x in gaps])
W("   cap-active gaps (gap>=L*) : %s" % [k for k in range(len(gaps)) if gaps[k] >= L - mp.mpf("1e-25")])
W("   max gap<=L*: %s ; 10L*-2pi = %s ; 4L*<pi: %s ; 5L*<pi: %s ; 3L*<pi: %s" % (
    max(gaps) <= L, mp.nstr(10 * L - 2 * mp.pi, 20), 4 * L < mp.pi, 5 * L < mp.pi, 3 * L < mp.pi))

# ---- Voronoi vertices in D
V = voronoi_vertices(C)
W("")
W("### Voronoi vertices in closed D: n=%d" % len(V))
W("   (all listed with |u|, circumradius, slack margin = min_other_dist - R_tri)")
for v in sorted(V, key=lambda z: z["tri"]):
    W("   tri%-16s u=(%s, %s) |u|=%s Rtri=%s Rtri-r*=%s margin=%s %s" % (
        str(tuple(v["tri"])), mp.nstr(v["u"][0], 18), mp.nstr(v["u"][1], 18),
        mp.nstr(v["absu"], 18), mp.nstr(v["R"], 20), mp.nstr(v["R"] - R, 6),
        mp.nstr(v["slack_margin"], 6),
        "TIGHT" if abs(v["R"] - R) < mp.mpf("1e-14") else "**SLACK**"))
tight = [v for v in V if abs(v["R"] - R) < mp.mpf("1e-14")]
slack = [v for v in V if not (abs(v["R"] - R) < mp.mpf("1e-14"))]
W("   counts: tight=%d slack=%d" % (len(tight), len(slack)))
W("   tight triples: %s" % sorted(tuple(v["tri"]) for v in tight))
W("   slack triples: %s" % [(tuple(v["tri"]), mp.nstr(v["R"], 12)) for v in slack])

# compare with Lead list
lead_tight = sorted(tuple(x["sites"]) for x in lead["tight"])
mine_tight = sorted(tuple(v["tri"]) for v in tight)
W("")
W("### vs Lead tight list : identical set? %s" % (lead_tight == mine_tight))
if lead_tight != mine_tight:
    W("   only mine : %s" % [t for t in mine_tight if t not in lead_tight])
    W("   only lead : %s" % [t for t in lead_tight if t not in mine_tight])
W("### vs Lead 'actual' full list (16) : identical? %s" % (sorted(tuple(x["sites"]) for x in lead["actual"]) == sorted(tuple(v["tri"]) for v in V)))

# ---- old root comparison for the 16 triples that the OLD portrait called vertices
C_old, R_old, th_old = old_geom_centers()
W("")
W("### OLD (nonstationary) root comparison -- leading-order check only")
W("   old refined R  = %s" % mp.nstr(R_old, 30))
W("   new r*         = %s" % mp.nstr(R, 30))
W("   R_new - R_old  = %s" % mp.nstr(R - R_old, 6))
W("   old th(5)=z_old = %s ; new z = %s ; diff = %s" % (mp.nstr(th_old[5], 25), mp.nstr(g["z"], 25), mp.nstr(g["z"] - th_old[5], 6)))
W("   old th(2)=c_old = %s ; new c = %s ; diff = %s" % (mp.nstr(th_old[2], 25), mp.nstr(g["c"], 25), mp.nstr(g["c"] - th_old[2], 6)))

data = dict(
    r=mp.nstr(R, 50), z=mp.nstr(g["z"], 50), c=mp.nstr(g["c"], 50),
    a=mp.nstr(g["a"], 50), b=mp.nstr(g["b"], 50), d=mp.nstr(g["d"], 50), s=mp.nstr(g["s"], 50), t=mp.nstr(g["t"], 50),
    centers=[[mp.nstr(p[0], 30), mp.nstr(p[1], 30)] for p in C],
    active=active, inactive=inactive,
    anchors_deg=[float(mp.atan2(a[1], a[0]) * 180 / mp.pi) % 360 for a in anchors],
    anchor_owners=owners,
    gaps_deg=[float(x * 180 / mp.pi) for x in gaps],
    cap_active=[k for k in range(len(gaps)) if gaps[k] >= L - mp.mpf("1e-25")],
    L=mp.nstr(L, 40), defect=mp.nstr(10 * L - 2 * mp.pi, 40),
    tight=[dict(sites=list(v["tri"]), q=[mp.nstr(v["u"][0], 30), mp.nstr(v["u"][1], 30)], radius=mp.nstr(v["R"], 30)) for v in sorted(tight, key=lambda z: z["tri"])],
    slack=[dict(sites=list(v["tri"]), q=[mp.nstr(v["u"][0], 30), mp.nstr(v["u"][1], 30)], radius=mp.nstr(v["R"], 30)) for v in sorted(slack, key=lambda z: z["tri"])],
)
(HERE.parent / "logs").mkdir(exist_ok=True)
(HERE.parent / "evidence").mkdir(exist_ok=True)
(HERE.parent / "logs/step1_geom.txt").write_text("\n".join(OUT), encoding="utf-8")
(HERE.parent / "evidence/step1_geom.json").write_text(json.dumps(data, indent=1), encoding="utf-8")
print("\nwrote logs/step1_geom.txt evidence/step1_geom.json")
