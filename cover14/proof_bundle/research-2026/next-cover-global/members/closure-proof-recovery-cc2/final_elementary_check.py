"""FINAL elementary check, no new constructions beyond the audited formulas.

(1) beta = angle at the SITE u, beta = angle (uO,uA):  verify
        D^2 = a^2 + R^2 - 2 a R cos(beta)          (law of cosines in triangle uAO, angle at u)
        cos(gamma_A) = (a - R cos beta)/D
    in the exact configuration the file uses: u=(0,0), v on a ray, A=(l/2,hA) with hA<0,
    O=(l/2,hO) real face centre (|O-u|=R), a=|A-u|=|A-v|.
    Also: beta + gamma_f + gamma_A = pi, and sin(beta) = ... sanity.
(2) D1 redone correctly: legal sites |u|<=s and |Au|<=U built directly from the cone
    parametrisation (u = A - a(cos psi A + sin psi A_perp), psi >= acos k(a)), plus a
    fully independent parametrisation (sample sites in the disk cap directly).
(3) Short diagnostic of the E-section ray-order checks (print the offending configuration).
"""
import math, itertools, random
import numpy as np

print("=" * 96)
print("(1) BETA AT THE SITE u -- exact configuration of the file")
print("=" * 96)
l = 0.7
hO = 0.15          # real face circumcentre ordinate (may be negative)
hA = -0.22         # C1250: hA<0
u = np.array([0.0, 0.0]); v = np.array([l, 0.0])
A = np.array([l/2, hA]); O = np.array([l/2, hO])
a = float(np.linalg.norm(A-u)); a2 = float(np.linalg.norm(A-v))
R = float(np.linalg.norm(O-u)); R2 = float(np.linalg.norm(O-v))
D = float(np.linalg.norm(A-O))
print("a=|Au|=%.15f  |Av|=%.15f   R=|Ou|=%.15f  |Ov|=%.15f   D=|AO|=%.15f" % (a, a2, R, R2, D))
# angle at u in triangle (uA O): vectors u->A, u->O
cosbeta = float((O-u) @ (A-u))/(R*a)
D_from_law = math.sqrt(a*a + R*R - 2*a*R*cosbeta)
print("beta = angle(uA,uO) = %.15f rad ; cos beta = %.15f" % (math.acos(cosbeta), cosbeta))
print("D (direct)      = %.15f" % D)
print("sqrt(a^2+R^2-2aR cosbeta) = %.15f   residual = %.3e" % (D_from_law, D_from_law-D))
# angle at A:  2 gamma_A = angle uAv
wu = u-A; wv = v-A
angA = math.atan2(abs(wu[0]*wv[1]-wu[1]*wv[0]), float(wu@wv))
gammaA = angA/2
lhs = (a - R*cosbeta)/D
print("2 gamma_A = %.15f -> gamma_A = %.15f ; (a - R cos beta)/D = %.15f ; residual %.3e"
      % (angA, gammaA, lhs, lhs - math.cos(gammaA)))
print("gamma_A in (0,pi/2)? %s  (cos gamma_A = %.6f > 0)" % (0 < gammaA < math.pi/2, math.cos(gammaA)))
# gamma_f: angle at O between OA and Ov  (third face vertex is v in this edge restriction)
fix = float((A-O) @ (v-O))/(D*R2)
gamma_f = math.acos(max(-1, min(1, fix)))
# beta' was defined at u; the face triangle (u,v,O) has angle beta at u (u->v, u->O)
beta_face = math.acos(max(-1, min(1, float((v-u) @ (O-u))/(l*R))))
print("gamma_f = %.15f ; beta = %.15f ; gamma_f+gamma_A+beta = %.15f (pi = %.15f)"
      % (gamma_f, beta_face, gamma_f+gammaA+beta_face, math.pi))
print("R sin gamma_f = %.15f ; a sin gamma_A = %.15f" % (R*math.sin(gamma_f), a*math.sin(gammaA)))
print("NOTE: beta is a DIFFERENT angle from angle(uO,uA) unless v lies on the ray u->A;")
print("      in this file's boundary-edge restriction A is on the line through u,v, so they agree up to sign.")
# explicit check: is A on the line uv?  cross(v-u, A-u)
print("cross(v-u,A-u) = %.3e  (0 means A on line uv; file's restriction)" % float((v-u)[0]*(A-u)[1]-(v-u)[1]*(A-u)[0]))

print()
print("=" * 96)
print("(2) D1 redone: cos gamma >= k(a) with |u|,|v| <= s and |Au|,|Av| <= U")
print("=" * 96)
Um = 0.32; sm = math.sqrt(1-Um*Um)
rng = random.Random(101)
viol = 0; cnt = 0; worst = (9, None)
for _ in range(300000):
    aT = rng.uniform(1-sm, Um)
    kk = (aT*aT+Um*Um)/(2*aT)
    if kk > 1: continue                      # infeasible a
    # independent sampling: pick any site in the disk cap B(0,s) cap B(A,aT) directly
    A = np.array([1.0, 0.0])
    # sample points on circle(A,aT) then keep those with norm <= s
    th = rng.uniform(0, 2*math.pi)
    u = A + aT*np.array([math.cos(th), math.sin(th)])
    if np.linalg.norm(u) > sm + 1e-12: continue
    th2 = rng.uniform(0, 2*math.pi)
    v = A + aT*np.array([math.cos(th2), math.sin(th2)])
    if np.linalg.norm(v) > sm + 1e-12: continue
    a1 = float(np.linalg.norm(A-u)); a2 = float(np.linalg.norm(A-v))
    wu = u-A; wv = v-A
    ang = math.atan2(abs(wu[0]*wv[1]-wu[1]*wv[0]), float(wu@wv))
    gam = ang/2
    if gam > math.pi/2 + 1e-12: continue
    ka = (a1*a1+Um*Um)/(2*a1)
    cnt += 1
    slack = math.cos(gam) - ka
    if slack < worst[0]: worst = (slack, (a1, a2, gam, ka))
    if slack < -1e-12: viol += 1
print("samples=%d violations=%d  min slack=%.3e" % (cnt, viol, worst[0]))
print("worst (a1,a2,gamma,k(a)) = %s" % ("%.4f %.4f %.4f %.4f" % worst[1]))
# same but |Av| free in [0,U]
viol2 = 0; cnt2 = 0; worst2 = (9, None)
for _ in range(300000):
    a1 = rng.uniform(1-sm, Um); a2 = rng.uniform(1-sm, Um)
    A = np.array([1.0, 0.0])
    u = A + a1*np.array([math.cos(rng.uniform(0, 2*math.pi)), math.sin(rng.uniform(0, 2*math.pi))])
    v = A + a2*np.array([math.cos(rng.uniform(0, 2*math.pi)), math.sin(rng.uniform(0, 2*math.pi))])
    if np.linalg.norm(u) > sm+1e-12 or np.linalg.norm(v) > sm+1e-12: continue
    wu = u-A; wv = v-A
    ang = math.atan2(abs(wu[0]*wv[1]-wu[1]*wv[0]), float(wu@wv))
    gam = ang/2
    if gam > math.pi/2+1e-12: continue
    ka = (a1*a1+Um*Um)/(2*a1)
    cnt2 += 1
    slack = math.cos(gam)-ka
    if slack < worst2[0]: worst2 = (slack, (a1, a2, gam, ka))
    if slack < -1e-12: viol2 += 1
print("unequal-anchor variant: samples=%d violations=%d min slack=%.3e worst=%s"
      % (cnt2, viol2, worst2[0], "%.4f %.4f %.4f %.4f" % worst2[1]))
