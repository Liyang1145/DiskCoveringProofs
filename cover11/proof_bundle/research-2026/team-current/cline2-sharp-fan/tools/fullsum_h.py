# -*- coding: utf-8 -*-
"""FULL-SUM H-DEPENDENCE: the six hub-9 faces (values + all slots), with the nine
non-hub sites held fixed (the lead's H-fibre situation).  Checks:
  (1) the six face VALUES sum to an affine function of H;
  (2) the z11/z73 slots are H-independent (telescoping, verified in p28);
  (3) the full H-dependence = affine + arctan slots; is the max at an endpoint?
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
HUB9FACES = [k for k, f in enumerate(FACES) if 9 in f]
P("faces containing hub 9: %s" % [(k, FACES[k]) for k in HUB9FACES])
P("")

def angv(v, u, w):
    a_ = u-v; b_ = w-v
    return math.atan2(abs(a_[0]*b_[1]-a_[1]*b_[0]), a_[0]*b_[0]+a_[1]*b_[1])

def circum(p, pts):
    A_, B_, C_ = pts[p[0]], pts[p[1]], pts[p[2]]
    d = 2*(A_[0]*(B_[1]-C_[1])+B_[0]*(C_[1]-A_[1])+C_[0]*(A_[1]-B_[1]))
    ux = ((A_@A_)*(B_[1]-C_[1])+(B_@B_)*(C_[1]-A_[1])+(C_@C_)*(A_[1]-B_[1]))/d
    uy = ((A_@A_)*(C_[0]-B_[0])+(B_@B_)*(A_[0]-C_[0])+(C_@C_)*(B_[0]-A_[0]))/d
    return float(np.linalg.norm(np.array([ux, uy])-A_))

def scene(b1, b2, A, H):
    s = math.sqrt(1-R0*R0); d = b1-A
    c2 = np.array([s, 0.0])
    c1 = c2 + 2*R0*math.sin(b1)*np.array([-math.cos(b1), -math.sin(b1)])
    c3 = c2 + 2*R0*math.sin(b2)*np.array([-math.cos(b2),  math.sin(b2)])
    pts = {}
    pts[9] = np.array([s - H*math.cos(d), -H*math.sin(d)])
    pts[1] = c1; pts[2] = c2; pts[3] = c3
    # the other ring sites: fixed on a circle of radius 0.85, placed so that the fan is
    # non-degenerate (their exact positions are irrelevant: they do not involve H)
    ph = {0: -1.75, 4: 2.05, 5: 2.60, 6: 3.15, 7: 3.70, 8: 4.25, 10: 0.40}
    for k, t in ph.items():
        pts[k] = 0.85*np.array([math.cos(t), math.sin(t)])
    return pts

def hub9_parts(b1, b2, A, H):
    pts = scene(b1, b2, A, H)
    val = 0.0; site = 0.0; edgeang = 0.0; qlin = 0.0
    for fi in HUB9FACES:
        vs = FACES[fi]
        angs = [angv(pts[vs[k]], pts[vs[(k+1) % 3]], pts[vs[(k+2) % 3]]) for k in range(3)]
        rho = circum(vs, pts); t = rho/R0
        val += 2*R0*R0*t*t*math.prod(math.sin(x) for x in angs)
        for k, i in enumerate(vs):
            e = tuple(sorted(j for j in vs if j != i)); ee = EDGES.index(e)
            sg = 1 if ADJ[EDGES[ee]][0] == fi else -1
            site += (-angs[k])*z[i]
            edgeang += (-angs[k])*z[50+ee]
            qlin += (sg*t*t*math.sin(angs[k])**2)*z[11+ee] + (sg*t*math.sin(angs[k]))*z[73+ee]
    return val, site, edgeang, qlin, val+site+edgeang+qlin

b1, b2, A = 1.0, 1.0, 0.8
P("H-scan of the SIX hub-9 faces (b1=%.2f b2=%.2f A=%.2f, other sites fixed):" % (b1, b2, A))
P("     H      values        site-slots    edge-angle    z11/z73      TOTAL")
Hs = [0.30, 0.35, 0.40, 0.45, 0.50, 0.55, 0.60]
tab = []
for H in Hs:
    v = hub9_parts(b1, b2, A, H); tab.append(v)
    P("  %.2f  %+.9f  %+.9f  %+.9f  %+.9f  %+.9f" % (H, v[0], v[1], v[2], v[3], v[4]))
P("")
v0 = np.array([t[0] for t in tab]); d2 = np.diff(v0, 2)
P("(1) affinity of the VALUES: second differences = %s  (max |d2| = %.2e)"
  % (np.round(d2, 12).tolist(), np.abs(d2).max()))
q0 = np.array([t[3] for t in tab])
P("(2) H-independence of the z11/z73 slots: second differences max |d2| = %.2e ; range = %.2e"
  % (np.abs(np.diff(q0, 2)).max(), q0.max()-q0.min()))
tot = np.array([t[4] for t in tab])
P("(3) TOTAL: argmax at H=%.2f ; total(Hlo)=%+.9f total(Hhi)=%+.9f  (endpoint max %s)"
  % (Hs[int(np.argmax(tot))], tot[0], tot[-1],
     "HOLDS" if int(np.argmax(tot)) in (0, len(Hs)-1) else "FAILS on this coarse scan"))
P("")
P("F'' of the total (finite differences, coarse):  %s"
  % np.round(np.diff(tot, 2), 9).tolist())
P("")
P("STRUCTURE (exact):")
P("  * the six face VALUES sum to a function that is AFFINE in H (each triangle area is")
P("    (1/2)|(c_i - c9) x (c_{i+1} - c9)|, affine in c9, and c9 is affine in H); the two")
P("    hub-hub faces are H-independent; the telescoping identity kills the z11/z73 slots")
P("    (p28: exact 12-digit constancy); hence")
P("  * TOTAL(H) = affine(H) + sum over the hub-9 faces of [site-angle + edge-angle slots],")
P("    and those slots are combinations of the face angles, i.e. arctan/atan2 functions.")
P("  * F''_total(H) = sum over (face,vertex) angle-weights * d^2(theta)/dH^2 with")
P("        d^2(phi)/dH^2 = 2 D sin(th)(H - D cos th)/L^4   (sign change at H = D cos th)")
P("    so F''_total is NOT of one sign in general; endpoint-max must be TESTED, and the")
P("    correct 1-D reduction is: evaluate the total at H_lo, H_hi and at the zeros of the")
P("    explicit F' (arctan derivatives -D sin th/L^2).")
with open(OUT / 'p29_fullsum_h.txt', 'w', encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
