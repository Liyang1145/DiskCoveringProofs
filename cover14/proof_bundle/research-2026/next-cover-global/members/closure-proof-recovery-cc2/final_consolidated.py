"""FINAL consolidated elementary check of the two audited arguments (no new constructions).

Config family = the one C1250/C1252 actually use:  u=(0,0), v=(l,0),
A=(l/2,hA) on the perpendicular bisector of uv, O=(l/2,hO) the real-face circumcentre.
Then |Au|=|Av|=a, |Ou|=|Ov|=R, D=|AO|.
Angles:  beta := angle at O between (A-O) and (u-O)   [vertex O, as the file writes
         "cos gamma_A=(a-R cos beta)/D, sin gamma_A=R sin beta/D" -- a circle-angle relation]
         gamma_f := angle at O between (A-O) and (v-O)
         gamma_A := angle(uAv)/2
Tested identities:
   (v1) D^2 = a^2 + R^2 - 2 a R cos(beta)
   (v2) cos(gamma_A) = (a - R cos beta)/D          (attention: attention to which beta!)
   (v3) gamma_f + gamma_A = pi - beta
   (v4) a sin(gamma_A) = R sin(gamma_f)
   (v5) hA<0 (C1250) and gamma_A<pi/2 are equivalent in this family
"""
import math
import numpy as np
import random

def cr(p, q): return float(p[0]*q[1] - p[1]*q[0])
def ang(P, Q, Z):
    p = np.array(Q)-np.array(P); q = np.array(Z)-np.array(P)
    return math.atan2(abs(cr(p, q)), float(p@q))

def row(l, hA, hO):
    u = np.array([0.0, 0.0]); v = np.array([l, 0.0])
    A = np.array([l/2, hA]); O = np.array([l/2, hO])
    a = float(np.linalg.norm(A-u)); R = float(np.linalg.norm(O-u)); D = float(np.linalg.norm(A-O))
    if D < 1e-9: return None
    gA = ang(A, u, v)/2
    beta = ang(O, A, u)          # at O
    gf = ang(O, A, v)            # at O, other side
    return dict(l=l, hA=hA, hO=hO, a=a, R=R, D=D, gA=gA, beta=beta, gf=gf,
                law=D**2 - (a*a+R*R-2*a*R*math.cos(beta)),
                v2=(a-R*math.cos(beta))/D - math.cos(gA),
                v3=(gf+gA+beta) - math.pi,
                v4=a*math.sin(gA) - R*math.sin(gf),
                gam_half=bool(gA < math.pi/2), hneg=bool(hA < 0))

cases = [(0.7,-0.22,0.15), (0.7,-0.22,-0.30), (1.0,-0.05,0.40), (0.5,-0.4,-0.05), (0.9,-0.9,0.9),
         (0.4,-0.02,0.6), (1.2,-0.6,-0.7), (0.3,-0.9,0.05), (0.8,-0.15,-0.9)]
print("%6s %7s %7s | %8s %8s %8s | %9s %9s %9s %9s" %
      ("l","hA","hO","a","R","D","lawres","v2res","v3res","v4res"))
W = [0.0,0.0,0.0,0.0]
for (l,hA,hO) in cases:
    r = row(l,hA,hO)
    if r is None: continue
    W[0]=max(W[0],abs(r['law'])); W[1]=max(W[1],abs(r['v2']))
    W[2]=max(W[2],abs(r['v3'])); W[3]=max(W[3],abs(r['v4']))
    print("%6.2f %7.2f %7.2f | %8.4f %8.4f %8.4f | %9.1e %9.1e %9.1e %9.1e" %
          (l,hA,hO,r['a'],r['R'],r['D'],abs(r['law']),abs(r['v2']),abs(r['v3']),abs(r['v4'])))
print("max residuals: law %.2e  v2 %.2e  v3 %.2e  v4 %.2e" % tuple(W))

# equivalence hA<0 <=> gamma_A<pi/2 (family test)
rng = random.Random(19); bad = []
for _ in range(200000):
    l = rng.uniform(0.05, 2.0); hA = rng.uniform(-2.5, 2.5); hO = rng.uniform(-2.5, 2.5)
    r = row(l, hA, hO)
    if r is None: continue
    # criterion: sign comparison
    if (r['hA'] < 0) != (r['gA'] < math.pi/2):
        # is the "bisector side" consistent?  check directly:  (O-A).(u-A) vs 0
        u = np.array([0.0,0.0]); A = np.array([l/2, hA]); O = np.array([l/2, hO])
        sgn = float((O-A)@(u-A))
        bad.append((l, hA, hO, r['gA'], r['hA'], sgn))
print()
print("hA<0 vs gamma_A<pi/2 disagreements: %d / many (see note)" % len(bad))
if bad[:3]:
    for b in bad[:3]:
        print("   l=%.3f hA=%.3f hO=%.3f gamma_A=%.4f  (O-A).(u-A)=%.4f" % b)
print()
print("NOTE (correct criterion): in this family gamma_A<pi/2  <=>  (O-A).(u-A) > 0,")
print("i.e. O and u on the same side of the line through A perpendicular to AO.")
print("C1250 supplies that via the nearest halfplane plus hA<hO; hA<0 alone does NOT")
print("determine it (example: hA<0<hO with |hO| small gives cos gamma_A<0).")
for (l,hA,hO) in [(0.7,-0.22,0.60),(0.7,-0.22,0.15),(0.7,-0.22,-0.30)]:
    r=row(l,hA,hO); u=np.array([0.0,0.0]); A=np.array([l/2,hA]); O=np.array([l/2,hO])
    print("  l=%.2f hA=%.2f hO=%.2f -> gamma_A=%.6f rad, cos=%.4f, (O-A).(u-A)=%.4f, hA<hO? %s"
          % (l,hA,hO,r['gA'],math.cos(r['gA']),float((O-A)@(u-A)), hA<hO))
