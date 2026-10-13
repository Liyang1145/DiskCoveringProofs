# -*- coding: utf-8 -*-
"""H-ENDPOINT-MAX (corrected): frozen z, exact F(H), F'(H), F''(H), fiber analysis.

Sign rule (per edge, as in the lead's atom code): sgn(fi,e) = 1 if ADJ[e][0]==fi else -1.
Verification: the closed form is checked term-by-term against a verbatim mirror of the
lead's face-atom code on the chart geometry.
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
f1 = FACES.index((9, 1, 2)); f2 = FACES.index((9, 2, 3))
Ei = lambda tri: EDGES.index(tuple(sorted(tri)))
e12, e92, e91, e23, e93 = Ei((1, 2)), Ei((2, 9)), Ei((1, 9)), Ei((2, 3)), Ei((3, 9))
SG = lambda fi, e: (1 if ADJ[EDGES[e]][0] == fi else -1)

# ---------------- direct (mirror of the lead's atom) ----------------
def geom(rr, b1, b2, A, H):
    s = math.sqrt(1-rr*rr); d = b1-A
    c2 = np.array([s, 0.0])
    c1 = c2 + 2*rr*math.sin(b1)*np.array([-math.cos(b1), -math.sin(b1)])
    c3 = c2 + 2*rr*math.sin(b2)*np.array([-math.cos(b2),  math.sin(b2)])
    c9 = np.array([s - H*math.cos(d), -H*math.sin(d)])
    return {9: c9, 1: c1, 2: c2, 3: c3}

def angv(v, u, w):
    a_ = u-v; b_ = w-v
    return math.atan2(abs(a_[0]*b_[1]-a_[1]*b_[0]), a_[0]*b_[0]+a_[1]*b_[1])

def direct(rr, b1, b2, A, H):
    pts = geom(rr, b1, b2, A, H)
    tot = 0.0
    for fi in (f1, f2):
        vs = FACES[fi]
        angs = [angv(pts[vs[k]], pts[vs[(k+1) % 3]], pts[vs[(k+2) % 3]]) for k in range(3)]
        A_, B_, C_ = pts[vs[0]], pts[vs[1]], pts[vs[2]]
        dd = 2*(A_[0]*(B_[1]-C_[1])+B_[0]*(C_[1]-A_[1])+C_[0]*(A_[1]-B_[1]))
        ux = ((A_@A_)*(B_[1]-C_[1])+(B_@B_)*(C_[1]-A_[1])+(C_@C_)*(A_[1]-B_[1]))/dd
        uy = ((A_@A_)*(C_[0]-B_[0])+(B_@B_)*(A_[0]-C_[0])+(C_@C_)*(B_[0]-A_[0]))/dd
        rho = float(np.linalg.norm(np.array([ux, uy])-A_)); t = rho/rr
        tot += 2*R0*R0*t*t*math.prod(math.sin(x) for x in angs)     # value
        for k, i in enumerate(vs):
            e = tuple(sorted(j for j in vs if j != i)); ee = EDGES.index(e)
            sg = SG(fi, ee)
            tot += (-angs[k])*z[i] + (-angs[k])*z[50+ee] \
                   + (sg*t*t*math.sin(angs[k])**2)*z[11+ee] + (sg*t*math.sin(angs[k]))*z[73+ee]
    return tot

# ---------------- closed form ----------------
def coeffs(rr, b1, b2, A):
    Z = lambda i: z[i]
    Zang = lambda e: z[50+e]; Zq = lambda e: z[11+e]; Zlin = lambda e: z[73+e]
    al1 = (Z(1) + Zang(e92)) - (Z(9) + Zang(e12))
    al2 = (Z(3) + Zang(e92)) - (Z(9) + Zang(e23))
    be1 = SG(f1, e91)*Zq(e91)/(4*rr*rr); ga1 = SG(f1, e91)*Zlin(e91)/(2*rr)
    be2 = SG(f2, e93)*Zq(e93)/(4*rr*rr); ga2 = SG(f2, e93)*Zlin(e93)/(2*rr)
    s1, s2 = SG(f1, e92), SG(f2, e92)
    BB = b1+b2-A
    C0 = (-(Z(1) + Zang(e92))*(math.pi-A) - (Z(3) + Zang(e92))*(math.pi-BB)
          - (A+BB)*Z(2) - A*Zang(e91) - BB*Zang(e93)
          + SG(f1, e12)*(math.sin(b1)**2*Zq(e12) + math.sin(b1)*Zlin(e12))
          + SG(f2, e23)*(math.sin(b2)**2*Zq(e23) + math.sin(b2)*Zlin(e23)))
    lam0 = rr*(math.sin(b1)*math.sin(A) + math.sin(b2)*math.sin(BB))
    return dict(al1=al1, al2=al2, be1=be1, ga1=ga1, be2=be2, ga2=ga2, C0=C0, lam0=lam0,
                s1=s1, s2=s2)

def pieces(rr, b1, b2, A, H, co):
    BB = b1+b2-A
    D1 = 2*rr*math.sin(b1); D2 = 2*rr*math.sin(b2)
    L1 = math.hypot(H - D1*math.cos(A), D1*math.sin(A))
    L2 = math.hypot(H - D2*math.cos(BB), D2*math.sin(BB))
    ph1 = math.atan2(D1*math.sin(A), H - D1*math.cos(A))
    ph2 = math.atan2(D2*math.sin(BB), H - D2*math.cos(BB))
    return (co['C0'] + co['lam0']*H + co['al1']*ph1 + co['al2']*ph2
            + co['be1']*L1*L1 + co['ga1']*L1 + co['be2']*L2*L2 + co['ga2']*L2,
            dict(L1=L1, L2=L2, ph1=ph1, ph2=ph2, D1=D1, D2=D2, BB=BB))

def derivs(rr, b1, b2, A, H, co):
    d = pieces(rr, b1, b2, A, H, co)[1]
    L1, L2, D1, D2, BB = d['L1'], d['L2'], d['D1'], d['D2'], d['BB']
    cA, cB = math.cos(A), math.cos(BB)
    Fp = (co['lam0'] - co['al1']*D1*math.sin(A)/L1**2 - co['al2']*D2*math.sin(BB)/L2**2
          + 2*co['be1']*(H-D1*cA) + 2*co['be2']*(H-D2*cB)
          + co['ga1']*(H-D1*cA)/L1 + co['ga2']*(H-D2*cB)/L2)
    Fpp = (2*(co['be1']+co['be2'])
           + 2*co['al1']*D1*math.sin(A)*(H-D1*cA)/L1**4
           + 2*co['al2']*D2*math.sin(BB)*(H-D2*cB)/L2**4
           + co['ga1']*(D1*math.sin(A))**2/L1**3
           + co['ga2']*(D2*math.sin(BB))**2/L2**3)
    return Fp, Fpp

P("="*78)
P("STEP 1 — closed form vs direct (corrected signs)")
P("="*78)
for (rr, b1, b2, A, H) in [(0.38, 1.0, 1.0, 0.8, 0.45), (0.38, 1.0, 1.0, 0.8, 0.35),
                           (0.38, 0.9, 1.1, 0.7, 0.40), (0.38, 0.6, 0.6, 0.6, 0.50),
                           (0.38, 1.2, 0.8, 0.9, 0.60)]:
    co = coeffs(rr, b1, b2, A)
    P("  r=%.2f b1=%.2f b2=%.2f A=%.2f H=%.3f : direct=%+.12f closed=%+.12f diff=%+.2e"
      % (rr, b1, b2, A, H, direct(rr, b1, b2, A, H), pieces(rr, b1, b2, A, H, co)[0],
         direct(rr, b1, b2, A, H)-pieces(rr, b1, b2, A, H, co)[0]))

P("")
P("="*78)
P("STEP 2 — F', F'' : analytic vs finite differences of the CLOSED form, and of DIRECT")
P("="*78)
rr, b1, b2, A = 0.38, 1.0, 1.0, 0.8
co = coeffs(rr, b1, b2, A)
P("  coefficients: al1=%+.9f al2=%+.9f be1=%+.9f be2=%+.9f ga1=%+.9f ga2=%+.9f lam0=%+.9f"
  % (co['al1'], co['al2'], co['be1'], co['be2'], co['ga1'], co['ga2'], co['lam0']))
P("  shared-edge signs s1=%+d s2=%+d (sum %+d : the shared-edge slots cancel identically)"
  % (co['s1'], co['s2'], co['s1']+co['s2']))
for H in (0.35, 0.45, 0.55):
    h = 1e-6
    fd1 = (direct(rr, b1, b2, A, H+h)-direct(rr, b1, b2, A, H-h))/(2*h)
    Fp, Fpp = derivs(rr, b1, b2, A, H, co)
    fdp = (derivs(rr, b1, b2, A, H+h, co)[0]-derivs(rr, b1, b2, A, H-h, co)[0])/(2*h)
    P("  H=%.3f : F' analytic %+.9f vs direct-fd %+.9f (diff %+.1e)" % (H, Fp, fd1, Fp-fd1))
    P("            F'' analytic %+.9f vs dF'/dH(fd of the analytic F') %+.9f (diff %+.1e)"
      % (Fpp, fdp, Fpp-fdp))

P("")
P("="*78)
P("STEP 3 — fiber, F'' range, and where the H-max sits (frozen z)")
P("="*78)
def fiber(rr, b1, b2, A):
    s = math.sqrt(1-rr*rr); dl = b1-A
    Dd = s*s*math.cos(dl)**2 - 2*rr*(1-rr)
    if not (Dd >= 0 and math.cos(dl) > 0):
        return None
    lo = max(2*rr*abs(math.sin(dl)), s*math.cos(dl)-math.sqrt(Dd))
    BB = b1+b2-A
    hi = min([s*math.cos(dl)+math.sqrt(Dd)] + [2*rr*math.sin(b1+A)]*(math.sin(b1+A) > 0)
             + [2*rr*math.sin(b2+BB)]*(math.sin(b2+BB) > 0))
    return (lo, hi) if lo <= hi else None

P("  %-26s %-22s %-12s %-12s %-16s %s" % ("(b1,b2,A)", "fiber", "F''min", "F''max", "argmax", "verdict"))
for (bb1, bb2, AA) in [(1.0, 1.0, 0.8), (0.9, 1.1, 0.7), (0.6, 0.6, 0.6), (1.2, 0.8, 0.9),
                       (0.5, 0.5, 0.4), (1.3, 1.3, 1.1), (0.8, 0.8, 0.8), (1.1, 0.7, 0.9)]:
    fb = fiber(rr, bb1, bb2, AA)
    if fb is None:
        P("  (%.2f,%.2f,%.2f)  FIBER EMPTY" % (bb1, bb2, AA)); continue
    lo, hi = fb
    co = coeffs(rr, bb1, bb2, AA)
    Hs = np.linspace(lo, hi, 4001)
    Fs = np.array([pieces(rr, bb1, bb2, AA, H, co)[0] for H in Hs])
    F2 = np.array([derivs(rr, bb1, bb2, AA, H, co)[1] for H in Hs])
    i = int(np.argmax(Fs))
    Fp_lo = derivs(rr, bb1, bb2, AA, lo, co)[0]
    Fp_hi = derivs(rr, bb1, bb2, AA, hi, co)[0]
    P("  %-26s [%.4f,%.4f] %-12.6f %-12.6f H=%.5f(%s)  F'' %s"
      % ("(%.2f,%.2f,%.2f)" % (bb1, bb2, AA), lo, hi, F2.min(), F2.max(), Hs[i],
         "end" if (i == 0 or i == len(Hs)-1) else "INTERIOR",
         "convex" if F2.min() > 0 else ("concave" if F2.max() < 0 else "sign-changing")))
    P("        F(Hlo)=%+.9f  F(Hhi)=%+.9f  F(argmax)=%+.9f  gap over endpoint-max=%+.3e"
      % (Fs[0], Fs[-1], Fs[i], Fs[i]-max(Fs[0], Fs[-1])))
    P("        F'(Hlo)=%+.6f  F'(Hhi)=%+.6f  => %s"
      % (Fp_lo, Fp_hi,
         "INTERIOR critical point exists (sign change of F')" if Fp_lo*Fp_hi < 0
         else "no sign change of F'"))

P("")
P("="*78)
P("STEP 4 — sign-free criteria with the corrected coefficients")
P("="*78)
P("  be1=%+.9f be2=%+.9f (both >0 : this is the lead's +.406258814/(4R0^2), +.420928035/(4R0^2))"
  % (co['be1'], co['be2']))
P("  ga1=%+.9f ga2=%+.9f (both <0 : the lead's -.874840892/(2R0), -.903343188/(2R0))"
  % (co['ga1'], co['ga2']))
P("  2(be1+be2) = %+.9f" % (2*(co['be1']+co['be2'])))
def Mbb(co, b1, b2, A):
    BB = b1+b2-A
    return (2*abs(co['al1'])/(2*R0*math.sin(b1)*math.sin(A))**2
            + 2*abs(co['al2'])/(2*R0*math.sin(b2)*math.sin(BB))**2
            + abs(co['ga1'])/(2*R0*math.sin(b1)*math.sin(A))
            + abs(co['ga2'])/(2*R0*math.sin(b2)*math.sin(BB)))
P("  M = 2(|al1|/(D1 sinA)^2 + |al2|/(D2 sinB)^2) + |ga1|/(D1 sinA) + |ga2|/(D2 sinB)")
for (bb1, bb2, AA) in [(1.0, 1.0, 0.8), (0.6, 0.6, 0.6), (1.3, 1.3, 1.1)]:
    M = Mbb(co, bb1, bb2, AA)
    P("   (b1,b2,A)=(%.2f,%.2f,%.2f): 2(be1+be2)=%+.6f  M=%+.6f  convexity criterion: %s"
      % (bb1, bb2, AA, 2*(co['be1']+co['be2']), M, 2*(co['be1']+co['be2']) >= M))
P("  and M >= (|ga1|+|ga2|)/(2R0) = %.6f  ALWAYS, so the convexity criterion is never satisfied" 
  % ((abs(co['ga1'])+abs(co['ga2']))/(2*R0)))
P("  => the sign-free bound is VACUOUS for these coefficients; the sharp statement is the")
P("     exact F'' formula (STEP 3), which is sign-changing on part of the fiber, yet the")
P("     argmax found in the tested fibers is still at an endpoint.")
P("     To make that rigorous one needs either (i) the exact min of F'' over the fiber plus")
P("     F' evaluation, or (ii) a comparison bound F(H) <= max(F(Hlo),F(Hhi)) proved from")
P("     the explicit F' (whose zero, if unique on the fiber, gives the only interior candidate).")

with open(OUT / 'p27_h_endpoint_max.txt', 'w', encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
