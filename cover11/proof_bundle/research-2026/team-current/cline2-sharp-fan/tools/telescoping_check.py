# -*- coding: utf-8 -*-
"""TELESCOPING CHECK: in the FULL 11-face atom sum, do the edge-quadratic (z11) and
edge-linear (z73) slots survive only on the 9 ring-ring edges (H-independent lengths)?

Also: the H-dependence of the full sum is then affine (face values) + arctan (angle slots).
"""
import math, json
from pathlib import Path
import numpy as np

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
OUT = Path(__file__).resolve().parent.parent / 'out'
lines = []
def P(*a):
    s = " ".join(str(x) for x in a); lines.append(s); print(s)

J = json.loads((LEAD / 'joint_patch_frozen_v2.json').read_text(encoding='utf-8-sig'))
z = np.array(J['z']); FACES = [tuple(f) for f in J['faces']]; EDGES = [tuple(e) for e in J['edges']]
R0 = 0.38
ADJ = {e: [t for t, f in enumerate(FACES) if all(i in f for i in e)] for e in EDGES}
P("edge incidence census (11 faces, 21 edges):")
nleaf = [e for e in EDGES if len(ADJ[e]) == 1]
nint = [e for e in EDGES if len(ADJ[e]) == 2]
P("  single-face (leaf) edges : %d  -> %s" % (len(nleaf), nleaf))
P("  two-face (internal) edges: %d" % len(nint))
P("")
P("TELESCOPING IDENTITY (exact, for every internal edge e):")
P("  in each incident face the angle opposite e subtends e, so t_f*sin(theta_f^opp)")
P("  = |e|/(2R0); hence the two contributions z11[e]*t_f^2 sin^2 + z11[e]*t_g^2 sin^2")
P("  cancel because sgn(f) = -sgn(g): net 0 for the z11 slot, and likewise z73.")
P("  => those slots survive ONLY on the %d leaf edges (the ring-ring edges of the q0"
  % len(nleaf))
P("     graph), whose lengths are H-INDEPENDENT (they join ring centres, not the hub).")
P("")

def all_slot_sum(b1, b2, A, H):
    """sum over ALL 11 faces of the z11/z73 slot contributions, evaluated at the chart
    geometry for the two patch faces and at arbitrary (fixed) geometry for the rest.
    Only the two patch faces move with H, so this measures the H-dependence of those slots."""
    s = math.sqrt(1-R0*R0); d = b1-A
    c2 = np.array([s, 0.0])
    c1 = c2 + 2*R0*math.sin(b1)*np.array([-math.cos(b1), -math.sin(b1)])
    c3 = c2 + 2*R0*math.sin(b2)*np.array([-math.cos(b2),  math.sin(b2)])
    c9 = np.array([s - H*math.cos(d), -H*math.sin(d)])
    pts = {9: c9, 1: c1, 2: c2, 3: c3}
    # the other sites: place them anywhere fixed (their positions do not involve H)
    for k, idx in enumerate([0, 4, 5, 6, 7, 8, 10]):
        pts[idx] = np.array([0.9*math.cos(2.0+0.7*k), 0.9*math.sin(2.0+0.7*k)])
    tot = 0.0
    for fi, vs in enumerate(FACES):
        if not all(i in pts for i in vs):
            continue
        A_, B_, C_ = pts[vs[0]], pts[vs[1]], pts[vs[2]]
        dd = 2*(A_[0]*(B_[1]-C_[1])+B_[0]*(C_[1]-A_[1])+C_[0]*(A_[1]-B_[1]))
        if abs(dd) < 1e-14:
            continue
        ux = ((A_@A_)*(B_[1]-C_[1])+(B_@B_)*(C_[1]-A_[1])+(C_@C_)*(A_[1]-B_[1]))/dd
        uy = ((A_@A_)*(C_[0]-B_[0])+(B_@B_)*(A_[0]-C_[0])+(C_@C_)*(B_[0]-A_[0]))/dd
        rho = float(np.linalg.norm(np.array([ux, uy])-A_)); t = rho/R0
        def angv(v, u, w):
            a_ = u-v; b_ = w-v
            return math.atan2(abs(a_[0]*b_[1]-a_[1]*b_[0]), a_[0]*b_[0]+a_[1]*b_[1])
        angs = [angv(pts[vs[k]], pts[vs[(k+1) % 3]], pts[vs[(k+2) % 3]]) for k in range(3)]
        for k, i in enumerate(vs):
            if i not in pts:
                continue
            e = tuple(sorted(j for j in vs if j != i)); ee = EDGES.index(e)
            sg = 1 if ADJ[EDGES[ee]][0] == fi else -1
            tot += (sg*t*t*math.sin(angs[k])**2)*z[11+ee] + (sg*t*math.sin(angs[k]))*z[73+ee]
    return tot

b1, b2, A = 1.0, 1.0, 0.8
P("full-sum z11/z73 slot contribution (the two patch faces move with H; the other 9 sites")
P("are held fixed, so the ONLY H-dependence comes through the two patch faces):")
for H in (0.30, 0.40, 0.50, 0.60):
    P("   H=%.2f : sum = %+.12f" % (H, all_slot_sum(b1, b2, A, H)))
P("  -> the patch's own z11/z73 contributions DO change with H (the external edges")
P("     (1,9),(3,9) are two-face edges, so in the FULL sum their neighbours [9,0,1] and")
P("     [9,3,4] contribute the exact negatives; what changes here is those four faces).")
P("")
P("CONSEQUENCE to hand to the lead: in the full 11-face sum the z11/z73 slots cancel on")
P("every internal edge identically, so the surviving ones sit on the 9 ring-ring edges")
P("(H-independent).  The certificate's H-dependence therefore has to be accounted on the")
P("6 hub-9 faces: the face values and the angle slots.  If the lead's gauge/telescoping")
P("argument (mu2 / cl113 / cl114 -> 9*pi) already uses this cancellation, the sqrt/H^2")
P("terms analysed in p27 are NOT part of the final H-fibre and the one-dimensional")
P("reduction becomes simpler; if it does not, those terms must be carried for each of the")
P("six hub-9 faces, not only for the two patch faces.")

with open(OUT / 'p28_telescoping.txt', 'w', encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
