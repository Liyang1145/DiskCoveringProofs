# -*- coding: utf-8 -*-
"""P2 (v2): true refined dual graph of the saved certified object + q0 class comparison.

Sites 0..10 (from certified_object.json, exact integers/1e17).
Faces  = Delaunay triangles containing at least one hub.
Leaves = the 9 boundary switches (ring-ring edges).
Dual graph: face-face across shared site-pair; leaf-face across ring-ring edge.
Class = sorted (deg_face1, deg_face2) of the two hub faces.
Compare with lead/q0_graphs.json entries.
"""
import os, sys, json
import mpmath as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fan_core import load_object, classify, HERE

mp.mp.dps = 60
OUT = os.path.join(HERE, os.pardir, "out")
LEAD = os.path.abspath(os.path.join(HERE, os.pardir, os.pardir, "lead"))
lines = []
def P(s=""):
    lines.append(s); print(s)

C, R, mp = load_object()
ring, hub, mod = classify(C, R)
ring = sorted(ring); hub = sorted(hub)
P("ring %s hub %s" % (ring, hub))


def circum(h, i, j):
    ax, ay = C[h]; bx, by = C[i]; cx, cy = C[j]
    d = 2*(ax*(by-cy) + bx*(cy-ay) + cx*(ay-by))
    if abs(d) < mp.mpf(10)**-55:
        return None, None
    a2 = ax*ax+ay*ay; b2 = bx*bx+by*by; c2 = cx*cx+cy*cy
    ux = (a2*(by-cy)+b2*(cy-ay)+c2*(ay-by))/d
    uy = (a2*(cx-bx)+b2*(ax-cx)+c2*(bx-ax))/d
    return (ux, uy), mp.sqrt((ux-ax)**2+(uy-ay)**2)


# enumerate ALL triangles whose circumcentre is inside D and lists the nearest sites
P("")
P("all triangles (hub, i, j) with circumcentre inside D (candidate Voronoi vertices):")
tris = []
for h in hub:
    for ki in range(len(ring)):
        for kj in range(ki+1, len(ring)):
            i = ring[ki]; j = ring[kj]
            p, rr = circum(h, i, j)
            if p is None:
                continue
            nrm = mp.sqrt(p[0]**2+p[1]**2)
            if nrm >= 1:
                continue
            tris.append((h, i, j, p, rr, nrm))
tris.sort(key=lambda z: (z[0], z[1], z[2]))
for h, i, j, p, rr, nrm in tris:
    P("   hub %d ring(%2d,%2d)  R_circ-R=%+.9f  |p|=%.9f  arg=%+.9f"
      % (h, i, j, rr-R, nrm, mp.atan2(p[1], p[0])))

# which of the 9 ring-ring pairs appear?
pairs = {}
for h, i, j, p, rr, nrm in tris:
    pairs.setdefault((i, j), []).append((h, rr, p))
P("")
P("ring-ring pairs with an inside circumcentre:")
for (i, j), v in sorted(pairs.items()):
    P("   (%2d,%2d): hubs %s" % (i, j, [(h, mp.nstr(rr-R, 5)) for h, rr, p in v]))

# --- true Delaunay via scipy for a cross-check
import numpy as np
Pts = np.array([[float(c[0]), float(c[1])] for c in C])
from scipy.spatial import Delaunay
tri = Delaunay(Pts)
P("")
P("scipy Delaunay simplices (n=%d):" % len(tri.simplices))
for s in tri.simplices:
    P("   %s  hubs=%s" % (list(map(int, s)), [int(x) for x in s if int(x) in hub]))

# --- build the refined dual graph
faces = []
for s in tri.simplices:
    s = tuple(sorted(int(x) for x in s))
    faces.append(s)
idx = {f: k for k, f in enumerate(faces)}
adj = {k: set() for k in range(len(faces))}
for k, f in enumerate(faces):
    for l in range(k+1, len(faces)):
        g = faces[l]
        if len(set(f) & set(g)) == 2:
            adj[k].add(l); adj[l].add(k)
leaves = []
for k, f in enumerate(faces):
    hubs_in = [x for x in f if x in hub]
    rs = [x for x in f if x in ring]
    if len(hubs_in) == 1 and len(rs) == 2:
        leaves.append((k, tuple(sorted(rs))))
leaf_of = {}
for k, pr in leaves:
    leaf_of[pr] = k
hubface = {}
for k, f in enumerate(faces):
    hs = [x for x in f if x in hub]
    if len(hs) == 2:
        hubface.setdefault(tuple(hs), []).append(k)
P("")
P("face count %d, hub faces %s" % (len(faces), hubface))
deg = {h: [] for h in hub}
for h in hub:
    # degree of the hub face = number of incident dual edges (internal + leaf)
    for k in hubface[tuple(sorted(hub))]:
        d_ff = len(adj[k])
        hs = [x for x in faces[k] if x in hub]
        own_ring = [x for x in faces[k] if x in ring]
        d_leaf = len(own_ring) if len(own_ring) == 2 else 0
        deg[h].append((k, d_ff, d_leaf, d_ff+d_leaf))
P("hub-face degrees:")
for h in hub:
    P("   hub %d: %s" % (h, deg[h]))

# --- compare with lead/q0_graphs.json
P("")
gp = os.path.join(LEAD, "q0_graphs.json")
if os.path.exists(gp):
    with open(gp, "r", encoding="utf-8-sig") as f:
        g = json.load(f)
    P("lead/q0_graphs.json entries:")
    for e in g:
        P("   start=%s span=%s  nfaces=%d nedges=%d" % (e['start'], e['span'],
                                                        len(e['faces']), len(e['edges'])))
        # hub degrees inside this graph model
        f9 = [f for f in e['facelist']] if 'facelist' in e else []
    # the file's faces are ring-labelled 0..8 with hubs 9,10 per entry.start in the comment
    for e in g:
        faces = [tuple(f) for f in e['faces']]
        ehub = {}
        for k, f in enumerate(faces):
            hs = [x for x in f if x >= 9]
            if hs:
                ehub.setdefault(tuple(hs), []).append(k)
        P("   entry start=%s: hub-face index groups %s" % (e['start'], {k: v for k, v in ehub.items()}))

# how many graph-isomorphism classes of the (6,7)-degree type exist? compute degrees
P("")
P("lead q0_graphs.json: hub-face dual degrees computed from the 'faces' + shared-edge rule:")
for e in g:
    faces = [tuple(f) for f in e['faces']]
    adjg = {k: set() for k in range(len(faces))}
    for k in range(len(faces)):
        for l in range(k+1, len(faces)):
            if len(set(faces[k]) & set(faces[l])) == 2:
                adjg[k].add(l)
    rows = []
    for k, f in enumerate(faces):
        hh = [x for x in f if x >= 9]
        rr = [x for x in f if x < 9]
        if len(hh) == 2:
            rows.append((tuple(hh), k, len(adjg[k]), 0))
        else:
            rows.append((tuple(hh), k, len(adjg[k]), len(rr) if len(rr) == 2 else 0))
    P("   start=%s : %s" % (e['start'], rows))

with open(os.path.join(OUT, "p2_dual_graph.txt"), "w", encoding="utf-8") as f:
    f.write("\n".join(lines) + "\n")
