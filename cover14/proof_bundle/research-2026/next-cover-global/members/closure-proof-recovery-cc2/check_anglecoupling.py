"""Numeric check of the (v) real-face angle coupling, plus saturation case.

Config (A at origin, bisector of uAv along +x, |A-u|=|A-v|=a, angle uAv=2g):
   A=(0,0), u=(a cos g, a sin g), v=(a cos g, -a sin g)
   O=(t,0) real circumcenter of u,v (t = a cos g - sqrt(R^2 - a^2 sin^2 g), inner branch)
   R=|O-u|, D=|A-O|=|t|, beta = angle at O between OA and Ou  -> law of cosines
   D^2 = a^2+R^2-2aR cos(beta)
Check cos(angle between Au and AO) == (a - R cos beta)/D  EXACTLY (all four faces/branches).
"""
import math

def cosbet_from_t(t, a, g, R):
    # vectors from O: A-O=(-t,0), u-O=(a cos g - t, a sin g)
    v1 = (-t, 0.0)
    v2 = (a*math.cos(g) - t, a*math.sin(g))
    n1 = math.hypot(*v1); n2 = math.hypot(*v2)
    assert abs(n1 - abs(t)) < 1e-12
    assert abs(n2 - R) < 1e-9, (n2, R)
    return (v1[0]*v2[0]+v1[1]*v2[1])/(n1*n2)

def check(a, g, branch):
    sg = math.sqrt(1 - a*a*math.sin(g)**2)  # R>= a sin g required
    t = a*math.cos(g) + branch*sg
    R = abs(math.hypot(a*math.cos(g)-t, a*math.sin(g)))
    D = abs(t)
    cb = cosbet_from_t(t, a, g, R)
    lhs = (a - R*cb)/D                      # file's formula
    # true cosine of angle between Au=(-a cos g,-a sin g) and AO=(-t,0)
    Au = (-a*math.cos(g), -a*math.sin(g)); AO = (-t, 0.0)
    true = (Au[0]*AO[0]+Au[1]*AO[1])/(a*D)
    # law of cosines residual of D^2 = a^2+R^2-2aR cb
    resid = D**2 - (a*a + R*R - 2*a*R*cb)
    return dict(a=a, g=g, branch=branch, t=t, R=R, D=D, cosbeta=cb, formula=lhs, true=true,
                diff=lhs-true, lawresid=resid)

print("--- general triangles: beta as ANGLE AT u (bisector-vertex), 2g = angle uAv ---")
for (a, g, br) in [(0.9, 0.5, -1), (0.9, 0.5, 1), (0.3, 0.9, -1), (0.99, 0.2, -1), (0.5, 1.2, 1)]:
    r = check(a, g, br)
    print({k: (round(v, 12) if isinstance(v, float) else v) for k, v in r.items()})

print()
print("--- saturated equality candidate (U=1/3): u=(-U,0), v=(U,0), A=(0,1) ---")
U = 1/3
pts = {'u': (-U, 0), 'v': (U, 0), 'A': (0, 1)}
a = math.dist(pts['u'], pts['A'])
# real face circle through u,v,A
# circumcenter of u,v,A:
import numpy as np
P = np.array([pts['u'], pts['v'], pts['A']], float)
M = 2*(P[1:] - P[0]); rhs = (P[1:]**2).sum(1) - (P[0]**2).sum()
O = np.linalg.solve(M, rhs)
R = float(np.linalg.norm(O - P[0])); D = float(np.linalg.norm(O - np.array([0, 1.0])))
gA = math.pi/2 + math.atan(2 * pts['A'][1] * 1)  # placeholder
# half-angle at A between Au and Av
Au = np.array(pts['u']) - np.array(pts['A']); Av = np.array(pts['v']) - np.array(pts['A'])
gamma = math.acos(Au @ Av / (np.linalg.norm(Au)*np.linalg.norm(Av))) / 2
ka = (a*a + U*U)/(2*a)
print("a=%.12f  R=%.12f  D=%.12f  O=%s" % (a, R, D, O))
print("gamma=%.12f  2gamma=%.12f   acos k(a)=%.12f   k(a)=%.12f" % (gamma, 2*gamma, math.acos(ka), ka))
print("cos gamma=%.15f   k(a)=%.15f   slack=%.3e" % (math.cos(gamma), ka, math.cos(gamma)-ka))
print("|u|=|v|=%.12f  s=%.12f   bound 2U/(1-U^2)=%.12f  <= s? %s" % (
    U, math.sqrt(1-U*U), 2*U/(1-U*U), 2*U/(1-U*U) <= math.sqrt(1-U*U)+1e-15))
# auxiliary claim: minimal max(|u|,|v|) over bisector orientation = 1+a^2-2a cos gamma
print("1+a^2-2a cos gamma = %.15f  vs |u|^2 = %.15f" % (1+a*a-2*a*math.cos(gamma), U*U))
print("D^2 vs a^2+R^2-2aR cosbeta (beta at u):", end=" ")
v1 = np.array(pts['A'])-O; v2 = np.array(pts['u'])-O
cb = v1@v2/(np.linalg.norm(v1)*np.linalg.norm(v2))
print(D*D - (a*a+R*R-2*a*R*cb), " cosbeta=", cb)
print("(a - R cosbeta)/D = %.15f   cos gamma = %.15f" % ((a-R*cb)/D, math.cos(gamma)))
