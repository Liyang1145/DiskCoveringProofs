# -*- coding: utf-8 -*-
"""H-DEPENDENCE OF THE TWO FACE ATOMS (own files only).

Task: with the chart of lead/DEGENERATE-SECTOR-HUB-PATCH.md and the atom formula of
lead/exchange_middle_inward_dual.py (lines 13-25), derive the exact H-dependence of
   F(H) := atom(face1) + atom(face2),   face1=[9,1,2], face2=[9,2,3],
at fixed b1,b2,A, and give F'(H), F''(H) with all coefficients general and signed.

This script (1) proves the two structural facts symbolically, (2) re-derives F(H) by
MIRRORING the lead's atom code exactly (so the comparison is against the same formula),
(3) checks F', F'' against finite differences, (4) TESTS the sign conditions on the z
that is on disk (lead/middle_inward_exchange_history.json) — testing, not assuming.
"""
import os, sys, math, json
from pathlib import Path
import numpy as np
import sympy as sp
import mpmath as mp

mp.mp.dps = 40
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
OUT = Path(__file__).resolve().parent.parent / 'out'
lines = []
def P(*args):
    s = " ".join(str(a) for a in args)
    lines.append(s); print(s)

P("="*78)
P("PART A — structure of the two face atoms (symbolic)")
P("="*78)
r, b1, b2, A, H = sp.symbols('r b1 b2 A H', positive=True)
B = b1 + b2 - A
D1 = 2*r*sp.sin(b1); D2 = 2*r*sp.sin(b2)
L1sq = H**2 + D1**2 - 2*H*D1*sp.cos(A)
L2sq = H**2 + D2**2 - 2*H*D2*sp.cos(B)
L1 = sp.sqrt(L1sq); L2 = sp.sqrt(L2sq)
phi1 = sp.atan2(D1*sp.sin(A), H - D1*sp.cos(A))
phi2 = sp.atan2(D2*sp.sin(B), H - D2*sp.cos(B))
psi1 = sp.pi - A - phi1; psi2 = sp.pi - B - phi2
t1 = L1/(2*r*sp.sin(A)); t2 = L2/(2*r*sp.sin(B))
s1, s2 = sp.symbols('s1 s2')          # edge signs for the SHARED edge (9,2)

P("A1. face VALUES are LINEAR in H:")
v1 = 2*(r*t1)**2*sp.sin(phi1)*sp.sin(psi1)*sp.sin(A)
v2 = 2*(r*t2)**2*sp.sin(phi2)*sp.sin(psi2)*sp.sin(B)
P("   v1 - r H sin(b1) sin(A) :", sp.simplify(sp.expand_trig(sp.simplify(v1 - r*H*sp.sin(b1)*sp.sin(A)))))
P("   v2 - r H sin(b2) sin(B) :", sp.simplify(sp.expand_trig(sp.simplify(v2 - r*H*sp.sin(b2)*sp.sin(B)))))
P("   (equivalently v_j = area of face j = D_j H sin(theta_j)/2)")
P("")
P("A2. SHARED-EDGE CANCELLATION  (the edge (9,2), side length H in BOTH faces):")
P("   the slot contributions for edge e are  sgn*t^2*sin^2(opposite angle)  and")
P("   sgn*t*sin(opposite angle); the angles opposite e are psi1 (face1) and psi2 (face2).")
P("   law of sines: 2*rho_j*sin(psi_j) = H  =>  t_j sin(psi_j) = H/(2r):")
P("      t1 sin(psi1) - H/(2r) =", sp.simplify(sp.expand_trig(sp.simplify(t1*sp.sin(psi1) - H/(2*r)))))
P("      t2 sin(psi2) - H/(2r) =", sp.simplify(sp.expand_trig(sp.simplify(t2*sp.sin(psi2) - H/(2*r)))))
P("   => with the two faces getting opposite signs (adj[e][0] convention, s2 = -s1):")
P("      z11[e92] coefficient: s1 t1^2 sin^2psi1 + s2 t2^2 sin^2psi2 = (s1+s2)(H/2r)^2 = 0")
P("      z73[e92] coefficient: s1 t1 sinpsi1    + s2 t2 sinpsi2    = (s1+s2)(H/2r)  = 0")
P("")
P("A3. the other edge slots are CONSTANT in H (t_j sin(phi_j) = sin b_j):")
P("   t1 sin(phi1) - sin(b1) :", sp.simplify(sp.expand_trig(sp.simplify(t1*sp.sin(phi1) - sp.sin(b1)))))
P("   t2 sin(phi2) - sin(b2) :", sp.simplify(sp.expand_trig(sp.simplify(t2*sp.sin(phi2) - sp.sin(b2)))))
P("A4. the A/B-opposite edges give the only sqrt terms: t1 sinA = L1/(2r), t1^2 sin^2A = L1^2/(4r^2)")
P("")
P("A5. derivatives (used below):")
P("   dphi1/dH = -D1 sinA / L1^2      d2phi1/dH^2 = 2 D1 sinA (H - D1 cosA)/L1^4")
P("   d(L1)/dH = (H - D1 cosA)/L1     d2(L1)/dH^2 = D1^2 sin^2A / L1^3   (>0 : sqrt is convex)")
P("   check d2(L1):", sp.simplify(sp.diff(sp.diff(L1, H), H) - D1**2*sp.sin(A)**2/L1**3))

P("")
P("="*78)
P("PART B — the explicit univariate objective and its derivatives")
P("="*78)
zdoc = r"""
  F(H) = C0 + lam0 H + a1 phi1 + a2 phi2 + b1s L1^2 + g1 L1 + b2s L2^2 + g2 L2

  lam0 = r ( sin b1 sin A + sin b2 sin B )                > 0 always
  a1   = (Z_1 + Zang[e12]) - (Z_9 + Zang[e12])            ... general, signed
  a2   = (Z_3 + Zang[e92]) - (Z_9 + Zang[e23])
  b1s  = s1 Zq[e91] / (4 r^2)        g1 = s1 Zlin[e91] / (2 r)
  b2s  = s2 Zq[e93] / (4 r^2)        g2 = s2 Zlin[e93] / (2 r)
  C0   = -(Z_1+Zang[e92])(pi-A) - (Z_3+Zang[e92])(pi-B) - (A+B) Z_2
         - A Zang[e91] - B Zang[e93]
         + s1[ sin^2b1 Zq[e12] + sin b1 Zlin[e12] ]
         + s2[ sin^2b2 Zq[e23] + sin b2 Zlin[e23] ]
  (Z_ = site-angle multipliers, Zang = edge-angle, Zq = edge-quadratic, Zlin = edge-linear;
   s1 = -s2 = the shared-edge sign; the shared-edge z11/z73 slots cancel exactly.)
"""
P(zdoc)
P("with  z_1 := a1, z_2 := a2, beta_j := b_j^s, gamma_j := g_j :")
P("  F'  = lam0 - z_1 D1 sinA/L1^2 - z_2 D2 sinB/L2^2")
P("        + 2 beta_1 (H - D1 cosA) + 2 beta_2 (H - D2 cosB)")
P("        + gamma_1 (H - D1 cosA)/L1 + gamma_2 (H - D2 cosB)/L2")
P("  F'' = 2(beta_1+beta_2) + sum_j [ 2 z_j (H - D_j cos th_j) D_j sin th_j / L_j^4")
P("                                     + gamma_j D_j^2 sin^2 th_j / L_j^3 ]")
P("      (th_1 = A, th_2 = B)")
P("")
P("SIGN-FREE BOUND (proved):  L_j^2 = (H - D_j cos th_j)^2 + D_j^2 sin^2 th_j >= D_j^2 sin^2 th_j")
P("  so L_j >= D_j sin th_j on the WHOLE H-fiber and |H - D_j cos th_j| <= L_j, hence")
P("     |F'' - 2(beta_1+beta_2)| <= 2|z_1|/(D1 sinA)^2 + 2|z_2|/(D2 sinB)^2")
P("                                 + |gamma_1|/(D1 sinA) + |gamma_2|/(D2 sinB) =: M")
P("  CONVEXITY CRITERION 2(beta_1+beta_2) >= M  =>  F'' >= 0  =>  max_H F = max(F(Hlo),F(Hhi))")
P("  CONCAVITY CRITERION 2(beta_1+beta_2) <= -M  =>  F'' <= 0  =>  F' has <=1 zero;")
P("     max over the fiber is at Hlo, Hhi or the unique critical point.")
P("  Both are SUFFICIENT and fully sign-free (no individual sign assumed).")
P("")
P("NO BLANKET MONOTONICITY: F' is a sum of lam0 > 0, of two terms each with a single")
P("minimum at H = D_j cos th_j (the arctan terms, whose derivative has the definite sign")
P("of -z_j but is non-monotone in H), of two linear terms and of two terms whose derivative")
P("has the fixed sign of gamma_j.  None of these dominates in general; the two criteria")
P("above are the only unconditional conclusions, and they must be TESTED on the actual z.")

# ---------------------------------------------------------------- mirror of the atom code
P("")
P("="*78)
P("PART C — verification against the lead's atom code (mirrored exactly)")
P("="*78)
src = (LEAD / 'propose_middle_sector_inward_dual.py').read_text()
marker = '\nK=len(factors);arows=[]'
assert src.count(marker) == 1
ns = {'__file__': str(LEAD / 'propose_middle_sector_inward_dual.py')}
exec(src.split(marker)[0], ns)
NS = ns['ns']
FACES = [tuple(f) for f in NS['faces']]
EDGES = [tuple(e) for e in NS['edges']]
ADJ = {e: [t for t, f in enumerate(FACES) if all(i in f for i in e)] for e in EDGES}
Rc = 0.38                      # code normalization constant (== lead's R)
P("faces %d, edges %d" % (len(FACES), len(EDGES)))

def find_face(tri):
    for k, f in enumerate(FACES):
        if set(f) == set(tri):
            return k
    return None
f1 = find_face((9, 1, 2)); f2 = find_face((9, 2, 3))
P("face [9,1,2] index %s, vertex order %s" % (f1, FACES[f1] if f1 is not None else None))
P("face [9,2,3] index %s, vertex order %s" % (f2, FACES[f2] if f2 is not None else None))

def atom_face(fi, x):
    """verbatim mirror of the fi<11 branch of lead atom()."""
    m = np.zeros(121)
    a, b, t = x
    aa = [a, b, math.pi - a - b]
    sn = np.sin(aa)
    v = 2*Rc*Rc*t*t*float(np.prod(sn))
    for k, i in enumerate(FACES[fi]):
        e = tuple(sorted(j for j in FACES[fi] if j != i))
        ee = EDGES.index(e)
        sgn = 1 if ADJ[e][0] == fi else -1
        m[i] -= aa[k]
        m[50+ee] -= aa[k]
        m[11+ee] += sgn*t*t*sn[k]**2
        m[73+ee] += sgn*t*sn[k]
    return float(v), m

def geometry(rr, bb1, bb2, AA, HH):
    s = math.sqrt(1-rr*rr)
    dl = bb1 - AA
    c2 = np.array([s, 0.0])
    c1 = c2 + 2*rr*math.sin(bb1)*np.array([-math.cos(bb1), -math.sin(bb1)])
    c3 = c2 + 2*rr*math.sin(bb2)*np.array([-math.cos(bb2),  math.sin(bb2)])
    c9 = np.array([s - HH*math.cos(dl), -HH*math.sin(dl)])
    def ang(u, v, w):
        a_ = u - v; b_ = w - v
        return math.atan2(abs(a_[0]*b_[1]-a_[1]*b_[0]), a_[0]*b_[0]+a_[1]*b_[1])
    A1 = ang(c1, c2, c9)          # angle at c2 in face1
    B1 = ang(c9, c2, c3)          # angle at c2 in face2
    def circum(p, q, u):
        d = np.linalg.norm(u-p); Hh = np.linalg.norm(u-q)
        L = np.linalg.norm(p-q)
        return L*Hh*d/(4*0.5*abs((q-p)[0]*(u-p)[1]-(q-p)[1]*(u-p)[0]))
    rho1 = circum(c1, c2, c9); rho2 = circum(c2, c3, c9)
    return dict(c1=c1, c2=c2, c3=c3, c9=c9, A1=A1, B1=B1, rho1=rho1, rho2=rho2, s=s, dl=dl)

def angles_in_order(fi, geo):
    """angles at FACES[fi][0], [1], [2] in the code's vertex order."""
    pts = {9: geo['c9'], 1: geo['c1'], 2: geo['c2'], 3: geo['c3']}
    return [ang_vertex(pts[j], pts[FACES[fi][(k+1) % 3]], pts[FACES[fi][(k+2) % 3]])
            for k, j in enumerate(FACES[fi])]

def ang_vertex(v, u, w):
    a_ = u - v; b_ = w - v
    return math.atan2(abs(a_[0]*b_[1]-a_[1]*b_[0]), a_[0]*b_[0]+a_[1]*b_[1])

def F_direct(rr, bb1, bb2, AA, HH, z):
    g = geometry(rr, bb1, bb2, AA, HH)
    tot = 0.0
    for fi, rho in ((f1, g['rho1']), (f2, g['rho2'])):
        angs = angles_in_order(fi, g)
        t = rho/rr                       # t = rho / (disk radius)
        v, m = atom_face(fi, (angs[0], angs[1], t))
        tot += v + float(m @ z)
    return tot, g

def F_closed(rr, bb1, bb2, AA, HH, z):
    """the derived closed form, with the coefficients extracted from z."""
    D1 = 2*rr*math.sin(bb1); D2 = 2*rr*math.sin(bb2)
    BB = bb1 + bb2 - AA
    L1sq = HH*HH + D1*D1 - 2*HH*D1*math.cos(AA)
    L2sq = HH*HH + D2*D2 - 2*HH*D2*math.cos(BB)
    L1 = math.sqrt(L1sq); L2 = math.sqrt(L2sq)
    def ei(tri):
        return EDGES.index(tuple(sorted(tri)))
    e12, e92, e91 = ei((1, 2)), ei((9, 2)), ei((9, 1))
    e23, e93 = ei((2, 3)), ei((9, 3))
    def sgn(fi, e):
        return 1 if ADJ[EDGES[e]][0] == fi else -1
    s_1 = sgn(f1, e92); s_2 = sgn(f2, e92)
    Z_9, Z_1, Z_2, Z_3 = z[9], z[1], z[2], z[3]
    Zang = lambda e: z[50+e]; Zq = lambda e: z[11+e]; Zlin = lambda e: z[73+e]
    a1 = (Z_1 + Zang(e92)) - (Z_9 + Zang(e12))
    a2 = (Z_3 + Zang(e92)) - (Z_9 + Zang(e23))
    be1 = s_1*Zq(e91)/(4*rr*rr); ga1 = s_1*Zlin(e91)/(2*rr)
    be2 = s_2*Zq(e93)/(4*rr*rr); ga2 = s_2*Zlin(e93)/(2*rr)
    C0 = (-(Z_1 + Zang(e92))*(math.pi - AA) - (Z_3 + Zang(e92))*(math.pi - BB)
          - (AA + BB)*Z_2 - AA*Zang(e91) - BB*Zang(e93)
          + s_1*(math.sin(bb1)**2*Zq(e12) + math.sin(bb1)*Zlin(e12))
          + s_2*(math.sin(bb2)**2*Zq(e23) + math.sin(bb2)*Zlin(e23)))
    lam0 = rr*(math.sin(bb1)*math.sin(AA) + math.sin(bb2)*math.sin(BB))
    phi1 = math.atan2(D1*math.sin(AA), HH - D1*math.cos(AA))
    phi2 = math.atan2(D2*math.sin(BB), HH - D2*math.cos(BB))
    return (C0 + lam0*HH + a1*phi1 + a2*phi2 + be1*L1sq + ga1*L1 + be2*L2sq + ga2*L2,
            dict(lam0=lam0, a1=a1, a2=a2, be1=be1, be2=be2, ga1=ga1, ga2=ga2,
                 C0=C0, D1=D1, D2=D2, L1=L1, L2=L2, ph1=phi1, ph2=phi2,
                 s1=s_1, s2=s_2, e12=e12, e92=e92, e91=e91, e23=e23, e93=e93))

hist = json.loads((LEAD / 'middle_inward_exchange_history.json').read_text())
row = min(hist, key=lambda q: q['continuous_numeric'])
z = np.array(row['z'])
P("z loaded: len=%d (round %s, continuous_numeric=%s)" % (len(z), row.get('roundno', '?'),
                                                           row['continuous_numeric']))
P("")
P("compare F_direct (keys' code, mirrored) with F_closed (derived) at 4 fixed points:")
for (rr, bb1, bb2, AA, HH) in [(0.38, 0.9, 1.1, 0.7, 0.4),
                               (0.38, 0.6, 0.6, 0.6, 0.35),
                               (0.38, 1.2, 0.8, 0.9, 0.43),
                               (0.375, 0.5, 1.0, 0.35, 0.25)]:
    fd, g = F_direct(rr, bb1, bb2, AA, HH, z)
    fc, co = F_closed(rr, bb1, bb2, AA, HH, z)
    P("  r=%s b1=%s b2=%s A=%s H=%s : direct=%.12f closed=%.12f diff=%+.2e  (rho1=%.6f rho2=%.6f)"
      % (rr, bb1, bb2, AA, HH, fd, fc, fd-fc, g['rho1'], g['rho2']))

P("")
P("derivative check (central differences vs the analytic formulas) at (0.38,0.9,1.1,0.7):")
rr, bb1, bb2, AA = 0.38, 0.9, 1.1, 0.7
HH = 0.45
fd, g = F_direct(rr, bb1, bb2, AA, HH, z)
_, co = F_closed(rr, bb1, bb2, AA, HH, z)
h = 1e-5
dd = (F_closed(rr, bb1, bb2, AA, HH+h, z)[0] - F_closed(rr, bb1, bb2, AA, HH-h, z)[0])/(2*h)
d2d = (F_closed(rr, bb1, bb2, AA, HH+h, z)[0] - 2*fd + F_closed(rr, bb1, bb2, AA, HH-h, z)[0])/(h*h)
F1p = (co['lam0'] - co['a1']*co['D1']*math.sin(AA)/co['L1']**2
       - co['a2']*co['D2']*math.sin(bb1+bb2-AA)/co['L2']**2
       + 2*co['be1']*(HH - co['D1']*math.cos(AA)) + 2*co['be2']*(HH - co['D2']*math.cos(bb1+bb2-AA))
       + co['ga1']*(HH - co['D1']*math.cos(AA))/co['L1']
       + co['ga2']*(HH - co['D2']*math.cos(bb1+bb2-AA))/co['L2'])
F2p = (2*(co['be1']+co['be2'])
       + 2*co['a1']*co['D1']*math.sin(AA)*(HH - co['D1']*math.cos(AA))/co['L1']**4
       + 2*co['a2']*co['D2']*math.sin(bb1+bb2-AA)*(HH - co['D2']*math.cos(bb1+bb2-AA))/co['L2']**4
       + co['ga1']*co['D1']**2*math.sin(AA)**2/co['L1']**3
       + co['ga2']*co['D2']**2*math.sin(bb1+bb2-AA)**2/co['L2']**3)
P("  F'(numeric) = %+.10f   F'(analytic) = %+.10f   diff = %+.2e" % (dd, F1p, dd-F1p))
P("  F''(numeric)= %+.10f   F''(analytic)= %+.10f   diff = %+.2e" % (d2d, F2p, d2d-F2p))

P("")
P("="*78)
P("PART D — TESTING the sign conditions on the on-disk z (not assumed)")
P("="*78)
P("%-28s %14s %14s" % ("coefficient", "value", ""))
P("  lam0 (must be > 0)      %+.8f" % co['lam0'])
for nm in ('a1', 'a2', 'be1', 'be2', 'ga1', 'ga2'):
    P("  %-23s %+.8f" % (nm, co[nm]))
P("  s1=%+d s2=%+d  (shared-edge signs, sum %+d)" % (co['s1'], co['s2'], co['s1']+co['s2']))
def Mbound(co, bb1, bb2, AA):
    BB = bb1+bb2-AA
    D1, D2 = co['D1'], co['D2']
    return (2*abs(co['a1'])/(D1*math.sin(AA))**2 + 2*abs(co['a2'])/(D2*math.sin(BB))**2
            + abs(co['ga1'])/(D1*math.sin(AA)) + abs(co['ga2'])/(D2*math.sin(BB)))
M = Mbound(co, bb1, bb2, AA)
P("  2(be1+be2) = %+.8f ; M = %+.8f  =>  convexity criterion (2(beta sum) >= M): %s"
  % (2*(co['be1']+co['be2']), M, 2*(co['be1']+co['be2']) >= M))
P("  concavity criterion (2(beta sum) <= -M): %s" % (2*(co['be1']+co['be2']) <= -M))
P("  => for THIS z and THIS (b1,b2,A) the sign-free criteria are %s;"
  % ("conclusive (convex: endpoint max)" if 2*(co['be1']+co['be2']) >= M else
     ("conclusive (concave)" if 2*(co['be1']+co['be2']) <= -M else "NOT conclusive")))
P("     then the H-max is settled by evaluating F at the fiber endpoints only.")
P("     The verdict is per-(b1,b2,A); it is not uniform in the patch variables.")

with open(OUT / 'p25_h_dependence.txt', 'w', encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
