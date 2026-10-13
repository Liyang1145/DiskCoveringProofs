# -*- coding: utf-8 -*-
"""debug: term-by-term comparison of direct atom evaluation vs the closed form."""
import math, json
from pathlib import Path
import numpy as np

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
J = json.loads((LEAD / 'joint_patch_frozen_v2.json').read_text(encoding='utf-8-sig'))
z = np.array(J['z']); FACES = [tuple(f) for f in J['faces']]; EDGES = [tuple(e) for e in J['edges']]
R0 = 0.38
ADJ = {e: [t for t, f in enumerate(FACES) if all(i in f for i in e)] for e in EDGES}
f1 = FACES.index((9, 1, 2)); f2 = FACES.index((9, 2, 3))
E = lambda tri: EDGES.index(tuple(sorted(tri)))
e12, e92, e91, e23, e93 = E((1, 2)), E((2, 9)), E((1, 9)), E((2, 3)), E((3, 9))
P = lambda *a: print(*a)

def geom(rr, b1, b2, A, H):
    s = math.sqrt(1-rr*rr); d = b1-A
    c2 = np.array([s, 0.0])
    c1 = c2 + 2*rr*math.sin(b1)*np.array([-math.cos(b1), -math.sin(b1)])
    c3 = c2 + 2*rr*math.sin(b2)*np.array([-math.cos(b2),  math.sin(b2)])
    c9 = np.array([s - H*math.cos(d), -H*math.sin(d)])
    return c1, c2, c3, c9

def angv(v, u, w):
    a_ = u-v; b_ = w-v
    return math.atan2(abs(a_[0]*b_[1]-a_[1]*b_[0]), a_[0]*b_[0]+a_[1]*b_[1])

def face_data(fi, pts):
    vs = FACES[fi]
    angs = [angv(pts[vs[k]], pts[vs[(k+1) % 3]], pts[vs[(k+2) % 3]]) for k in range(3)]
    A_, B_, C_ = pts[vs[0]], pts[vs[1]], pts[vs[2]]
    d = 2*(A_[0]*(B_[1]-C_[1])+B_[0]*(C_[1]-A_[1])+C_[0]*(A_[1]-B_[1]))
    ux = ((A_@A_)*(B_[1]-C_[1])+(B_@B_)*(C_[1]-A_[1])+(C_@C_)*(A_[1]-B_[1]))/d
    uy = ((A_@A_)*(C_[0]-B_[0])+(B_@B_)*(A_[0]-C_[0])+(C_@C_)*(B_[0]-A_[0]))/d
    rho = float(np.linalg.norm(np.array([ux, uy])-A_))
    return vs, angs, rho

def direct(rr, b1, b2, A, H, verbose=False):
    c1, c2, c3, c9 = geom(rr, b1, b2, A, H)
    pts = {9: c9, 1: c1, 2: c2, 3: c3}
    tot = 0.0
    for fi in (f1, f2):
        vs, angs, rho = face_data(fi, pts)
        t = rho/rr
        aa = angs
        val = 2*R0*R0*t*t*math.prod(math.sin(x) for x in aa)
        dot = 0.0
        det = []
        for k, i in enumerate(vs):
            e = tuple(sorted(j for j in vs if j != i)); ee = EDGES.index(e)
            sg = 1 if ADJ[EDGES[ee]][0] == fi else -1
            s_site = -aa[k]*z[i]; s_edge = -aa[k]*z[50+ee]
            s_q = sg*t*t*math.sin(aa[k])**2*z[11+ee]; s_l = sg*t*math.sin(aa[k])*z[73+ee]
            dot += s_site + s_edge + s_q + s_l
            det.append((vs[k], "%.6f" % aa[k], ee, e, sg, s_site, s_edge, s_q, s_l))
        tot += val + dot
        if verbose:
            P("   face %d %s t=%.9f rho=%.9f val=%.9f dot=%.9f" % (fi, vs, t, rho, val, dot))
            for d in det:
                P("      site %2d ang=%.6f edge %2d %s sgn=%+d  site %+.9f edang %+.9f q %+.9f lin %+.9f"
                  % (d[0], float(d[1]), d[2], d[3], d[4], d[5], d[6], d[7], d[8]))
    return tot

def closed(rr, b1, b2, A, H, verbose=False):
    Z9, Z1, Z2, Z3 = z[9], z[1], z[2], z[3]
    Zang = lambda e: z[50+e]; Zq = lambda e: z[11+e]; Zlin = lambda e: z[73+e]
    s1 = 1 if ADJ[EDGES[e92]][0] == f1 else -1
    s2 = 1 if ADJ[EDGES[e92]][0] == f2 else -1
    sge91 = 1 if ADJ[EDGES[e91]][0] == f1 else -1
    sge93 = 1 if ADJ[EDGES[e93]][0] == f2 else -1
    al1 = (Z1 + Zang(e92)) - (Z9 + Zang(e12))
    al2 = (Z3 + Zang(e92)) - (Z9 + Zang(e23))
    be1 = sge91*Zq(e91)/(4*rr*rr); ga1 = sge91*Zlin(e91)/(2*rr)
    be2 = sge93*Zq(e93)/(4*rr*rr); ga2 = sge93*Zlin(e93)/(2*rr)
    BB = b1+b2-A
    lam0 = rr*(math.sin(b1)*math.sin(A) + math.sin(b2)*math.sin(BB))
    C0 = (-(Z1 + Zang(e92))*(math.pi-A) - (Z3 + Zang(e92))*(math.pi-BB)
          - (A+BB)*Z2 - A*Zang(e91) - BB*Zang(e93)
          + s1*(math.sin(b1)**2*Zq(e12) + math.sin(b1)*Zlin(e12))
          + s2*(math.sin(b2)**2*Zq(e23) + math.sin(b2)*Zlin(e23)))
    D1 = 2*rr*math.sin(b1); D2 = 2*rr*math.sin(b2)
    L1 = math.hypot(H - D1*math.cos(A), D1*math.sin(A))
    L2 = math.hypot(H - D2*math.cos(BB), D2*math.sin(BB))
    ph1 = math.atan2(D1*math.sin(A), H - D1*math.cos(A))
    ph2 = math.atan2(D2*math.sin(BB), H - D2*math.cos(BB))
    parts = dict(C0=C0, lam0H=lam0*H, a1ph1=al1*ph1, a2ph2=al2*ph2,
                 be1L1sq=be1*L1*L1, ga1L1=ga1*L1, be2L2sq=be2*L2*L2, ga2L2=ga2*L2)
    if verbose:
        for k, v in parts.items():
            P("      %-8s %+.9f" % (k, v))
    return sum(parts.values()), parts, dict(s1=s1, s2=s2, sge91=sge91, sge93=sge93,
                                            al1=al1, al2=al2, be1=be1, ga1=ga1, be2=be2, ga2=ga2)

rr, b1, b2, A, H = 0.38, 1.0, 1.0, 0.8, 0.45
print("=== b1=%.2f b2=%.2f A=%.2f H=%.3f ===" % (b1, b2, A, H))
d = direct(rr, b1, b2, A, H, verbose=True)
c, parts, co = closed(rr, b1, b2, A, H, verbose=True)
print("direct = %.10f ; closed = %.10f ; diff = %+.3e" % (d, c, d-c))
print("signs: s1=%+d s2=%+d sge91=%+d sge93=%+d" % (co['s1'], co['s2'], co['sge91'], co['sge93']))
print("coeffs: al1=%+.9f al2=%+.9f be1=%+.9f ga1=%+.9f be2=%+.9f ga2=%+.9f"
      % (co['al1'], co['al2'], co['be1'], co['ga1'], co['be2'], co['ga2']))
print()
print("edge indices: e12=%d e92=%d e91=%d e23=%d e93=%d" % (e12, e92, e91, e23, e93))
print("z[50+ee] for the five edges:", [z[50+e] for e in (e12, e92, e91, e23, e93)])
print("z[11+ee]:", [z[11+e] for e in (e12, e92, e91, e23, e93)])
print("z[73+ee]:", [z[73+e] for e in (e12, e92, e91, e23, e93)])
