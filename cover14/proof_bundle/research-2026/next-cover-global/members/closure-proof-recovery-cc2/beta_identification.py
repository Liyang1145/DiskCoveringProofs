"""Which beta makes cos gamma_A = (a - R cos beta)/D exact?  Exact numeric test, both
configurations of the file, all quantities defined geometrically.

Convention: u=(0,0), v=(l,0), l>0, A=(l/2,hA) (A on the perpendicular bisector of uv, the
case C1250 uses), O=real face circumcentre.  a=|Au|=|Av|, R=|Ou|, D=|AO|.
Angles (all in [0,pi]):
   beta_mult = angle (u->v , u->O)            "paired angle at the site u"
   beta_face = angle (A->u , A->v) / 2 = gamma_A ... no: gamma_A is HALF that
   beta_AO   = angle (u->A , u->O)
   beta_atO  = angle (A->O , u->O)
"""
import math
import numpy as np

def test(l, hA, hO):
    u = np.array([0.0, 0.0]); v = np.array([l, 0.0])
    A = np.array([l/2, hA]); O = np.array([l/2, hO])
    a = float(np.linalg.norm(A-u)); a2 = float(np.linalg.norm(A-v))
    R = float(np.linalg.norm(O-u)); D = float(np.linalg.norm(A-O))
    assert abs(a-a2) < 1e-12
    def ang(P, Q, Z):     # angle at P between (Q-P) and (Z-P)
        p = np.array(Q)-np.array(P); q = np.array(Z)-np.array(P)
        return math.atan2(abs(p[0]*q[1]-p[1]*q[0]), float(p@q))
    beta_mult = ang(u, v, O)
    beta_AO = ang(u, A, O)
    beta_atO = ang(O, A, u)
    gmu = ang(A, u, v)/2
    return dict(l=l, hA=hA, hO=hO, a=a, R=R, D=D, gamma_A=gmu,
                beta_mult=beta_mult, beta_AO=beta_AO, beta_atO=beta_atO,
                cos_beta_mult=math.cos(beta_mult), cos_beta_AO=math.cos(beta_AO),
                cos_beta_atO=math.cos(beta_atO),
                cosg=math.cos(gmu),
                f_mult=(a - R*math.cos(beta_mult))/D,
                f_AO=(a - R*math.cos(beta_AO))/D,
                f_atO=(a - R*math.cos(beta_atO))/D,
                law_mult=math.sqrt(a*a+R*R-2*a*R*math.cos(beta_mult)) - D,
                law_AO=math.sqrt(a*a+R*R-2*a*R*math.cos(beta_AO)) - D,
                law_atO=math.sqrt(a*a+R*R-2*a*R*math.cos(beta_atO)) - D)

print("A on the perpendicular bisector (C1250 geometry), three candidate betas:")
print("%8s %8s %8s | %8s | %10s %10s %10s | law resid  mult/AO/atO" %
      ("l", "hA", "hO", "gamma_A", "f_mult", "f_AO", "f_atO"))
rows = [(0.7, -0.22, 0.15), (0.7, -0.22, -0.30), (1.0, -0.05, 0.40), (0.5, -0.4, -0.05), (0.9, -0.9, 0.9)]
for (l, hA, hO) in rows:
    r = test(l, hA, hO)
    print("%8.3f %8.3f %8.3f | %8.5f | %10.5f %10.5f %10.5f | %.1e %.1e %.1e" %
          (l, hA, hO, r['gamma_A'], r['f_mult'], r['f_AO'], r['f_atO'],
           r['law_mult'], r['law_AO'], r['law_atO']))
    print("      cos gamma_A = %.5f ; cos beta_mult=%.5f cos beta_AO=%.5f cos beta_atO=%.5f"
          % (r['cosg'], r['cos_beta_mult'], r['cos_beta_AO'], r['cos_beta_atO']))

print()
print("Interpretation test: which beta gives f == cos gamma_A exactly?")
okmult = okAO = okatO = 0
for l in (0.4, 0.6, 0.8, 1.0):
    for hA in (-0.05, -0.2, -0.5, -0.9):
        for hO in (-0.4, -0.1, 0.1, 0.5):
            r = test(l, hA, hO)
            if abs(r['f_mult']-r['cosg']) < 1e-12: okmult += 1
            if abs(r['f_AO']-r['cosg']) < 1e-12: okAO += 1
            if abs(r['f_atO']-r['cosg']) < 1e-12: okatO += 1
print("exact matches out of 64:  f(beta_mult)=cos gamma_A: %d ;  f(beta_AO): %d ;  f(beta_atO): %d"
      % (okmult, okAO, okatO))
print()
print("Law-of-cosines exact for which beta?  (D^2 = a^2+R^2-2aR cos beta)")
okmult = okAO = okatO = 0
for l in (0.4, 0.6, 0.8, 1.0):
    for hA in (-0.05, -0.2, -0.5, -0.9):
        for hO in (-0.4, -0.1, 0.1, 0.5):
            r = test(l, hA, hO)
            if abs(r['law_mult']) < 1e-12: okmult += 1
            if abs(r['law_AO']) < 1e-12: okAO += 1
            if abs(r['law_atO']) < 1e-12: okatO += 1
print("exact law matches out of 64:  beta_mult %d ; beta_AO %d ; beta_atO %d" % (okmult, okAO, okatO))
print()
print("Both are exact simultaneously only for beta_mult (the site-u paired angle, u->v and u->O).")
