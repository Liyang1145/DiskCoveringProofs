# -*- coding: utf-8 -*-
"""Audit of lead/CARTESIAN-ANGLE-CANCELLATION.md and scoping of the radial/secant reduction.

Exact/symbolic checks only, plus a few spot evaluations (no grids).
 (1) hub offset convention: c9 = c2 + (-v,-t), i.e. the hub is at -(v,t) in the c2 frame
 (2) phi1 = theta1 + delta, phi2 = theta2 - delta  (rotation identity)
 (3) the exact cancellation (z3-z1) delta + a1 phi1 + a2 phi2 = a1 theta1 + a2 theta2
 (4) area identity: area1+area2 = r(sin^2 b1 + sin^2 b2) v + r(sin b2 cos b2 - sin b1 cos b1) t
 (5) Y1,Y2 > 0: exact proofs and margins
 (6) L_j <= 2r <= 0.76, radial derivative < 0, secant slopes m_j
 (7) theta_j in (0, pi - b_j): closed-form control of the atan2 terms
"""
import sympy as sp
lines = []
def P(*a):
    s = " ".join(str(x) for x in a); lines.append(s); print(s)

r, v, t, b1, b2, d = sp.symbols('r v t b1 b2 delta', real=True)
s_ = sp.sqrt(1-r**2)
D1, D2 = 2*r*sp.sin(b1), 2*r*sp.sin(b2)
A_, B_ = b1-d, b2+d
X1, Y1 = v - D1*sp.cos(b1), D1*sp.sin(b1) - t
X2, Y2 = v - D2*sp.cos(b2), D2*sp.sin(b2) + t
H = sp.sqrt(v**2+t**2)
P("(1) conventions: hub = c2 + (-v,-t); ring centres c1 = D1(-cos b1,-sin b1), c3 = D2(-cos b2,+sin b2)")
P("    direction hub->c2 is (v,t), angle delta; direction hub->c1 is (c1+ (v,t)) =")
P("      (v - D1 cos b1, D1 sin b1 - t)*(-1) reflected ... in fact |(X1,Y1)| = |hub - c1| :")
P("    |(X1,Y1)|^2 - |(v+D1cos b1, t+D1 sin b1)|^2 :",
  sp.simplify(sp.expand(X1**2+Y1**2 - ((v+D1*sp.cos(b1))**2 + (t+D1*sp.sin(b1))**2))))
P("    (both equal v^2+t^2+D1^2+2 v D1 cos b1 + 2 t D1 sin b1, i.e. L1^2 = H^2+D1^2-2 H D1 cos A")
P("     only after using A = b1-d and v = H cos d, t = H sin d; L1 is |hub - c1|.)")
P("")
P("(2) rotation identity: the direction hub->c1 has angle -theta1 with theta1 = atan2(Y1,X1),")
P("    so the angle at the hub between the rays to c1 and to c2 is delta + theta1 = phi1.")
P("    numeric spot checks (hub at -(v,t), legal wedge):")
import mpmath as mp
mp.mp.dps = 25
for (rr, bb1, bb2, dd, HH) in [('0.38','1.0','1.07','0.2','0.4'), ('0.379','1.105','1.069','0.03','0.5'),
                               ('0.38','1.1','1.07','-0.02','0.45'), ('0.375','0.7','1.0','0.1','0.35')]:
    R_ = mp.mpf(rr); B1 = mp.mpf(bb1); B2 = mp.mpf(bb2); D_ = mp.mpf(dd); h_ = mp.mpf(HH)
    DD1 = 2*R_*mp.sin(B1); DD2 = 2*R_*mp.sin(B2)
    vv = h_*mp.cos(D_); tt = h_*mp.sin(D_)
    c1 = mp.matrix([-DD1*mp.cos(B1), -DD1*mp.sin(B1)]); c3 = mp.matrix([-DD2*mp.cos(B2), DD2*mp.sin(B2)])
    hub = mp.matrix([-vv, -tt]); c2 = mp.matrix([0, 0])
    def ang(u, x):
        return mp.atan2(u[0]*x[1]-u[1]*x[0], u[0]*x[0]+u[1]*x[1])
    phi1 = ang(c1-hub, c2-hub); phi2 = ang(c2-hub, c3-hub)
    X1_, Y1_ = vv - DD1*mp.cos(B1), DD1*mp.sin(B1) - tt
    X2_, Y2_ = vv - DD2*mp.cos(B2), DD2*mp.sin(B2) + tt
    th1 = mp.atan2(Y1_, X1_); th2 = mp.atan2(Y2_, X2_)
    P("   r=%s b1=%s b2=%s delta=%s H=%s : phi1-(th1+d)=%s  phi2-(th2-d)=%s  Y1=%s Y2=%s"
      % (rr, bb1, bb2, dd, HH, mp.nstr(phi1-(th1+D_), 4), mp.nstr(phi2-(th2-D_), 4),
         mp.nstr(Y1_, 6), mp.nstr(Y2_, 6)))
P("")
P("(3) cancellation: a1 phi1 + a2 phi2 + (z3-z1) delta = a1 th1 + a2 th2 with a1=z1-z9, a2=z3-z9")
P("    substitution phi1=th1+d, phi2=th2-d gives LHS-RHS = (z3-z1)+(a1-a2) = (z3-z1)+(z1-z3) = 0  [exact]")
P("")
P("(4) area identity (symbolic):")
area1 = sp.Rational(1,2)*D1*(sp.sin(b1)*v - sp.cos(b1)*t)
area2 = sp.Rational(1,2)*D2*(sp.cos(b2)*t + sp.sin(b2)*v)
P("    area1+area2 - [r(sin^2 b1+sin^2 b2)v + r(sin b2 cos b2 - sin b1 cos b1)t] :",
  sp.simplify(sp.expand(area1+area2 - (r*(sp.sin(b1)**2+sp.sin(b2)**2)*v
                                     + r*(sp.sin(b2)*sp.cos(b2)-sp.sin(b1)*sp.cos(b1))*t))))
P("    (and area1 = D1 H sinA/2, area2 = D2 H sinB/2 as in the earlier rounds)")
P("")
P("(5) Y1 = 2r sin^2 b1 - H sin d ; Y2 = 2r sin^2 b2 + H sin d.  Margin proofs:")
P("    d >= 0: H sin d <= 2r sin(b1+A) sin d = 2r(sin^2 b1 - sin^2 A) => Y1 >= 2r sin^2 A > 0")
P("    d <  0: Y1 = 2r sin^2 b1 + H|sin d| > 0 immediately")
P("    d <= 0: H|sin d| <= 2r sin(b2+B)|sin d| = 2r(sin^2 b2 - sin^2 B) => Y2 >= 2r sin^2 B > 0")
P("    d >  0: Y2 = 2r sin^2 b2 + H sin d > 0 immediately")
P("    (uses the face caps H <= 2r sin(b1+A), H <= 2r sin(b2+B) and sin(X+Y)sin(X-Y)=sin^2X-sin^2Y)")
P("")
P("(6) radial terms and the secant bound:")
z16, z20, z78, z82 = sp.symbols('z16 z20 z78 z82', real=True)
R0 = sp.Rational(19,50)
z16v, z20v, z78v, z82v = mp.mpf('-0.405431351'), mp.mpf('0.400827103'), mp.mpf('0.870277865'), mp.mpf('-0.865255970')
beta1v = -z16v/(4*mp.mpf(R0)**2); gam1v = -z78v/(2*mp.mpf(R0))
beta2v = z20v/(4*mp.mpf(R0)**2); gam2v = z82v/(2*mp.mpf(R0))
P("    beta1 = %s  gamma1 = %s" % (mp.nstr(beta1v, 10), mp.nstr(gam1v, 10)))
P("    beta2 = %s  gamma2 = %s" % (mp.nstr(beta2v, 10), mp.nstr(gam2v, 10)))
P("    L_j <= 2r <= 0.76 (|hub-c_j| <= |hub-C_j| + |C_j-c_j| <= r + r, C_j = face circumcentre)")
P("    phi_j'(L) = 2 beta_j L + gamma_j, max at L = 0.76:")
P("      phi1'(0.76) = %s < 0 ; phi2'(0.76) = %s < 0"
  % (mp.nstr(2*beta1v*mp.mpf('0.76')+gam1v, 8), mp.nstr(2*beta2v*mp.mpf('0.76')+gam2v, 8)))
P("    convex secant on [0,0.76] with phi_j(0)=0:  beta_j L^2 + gamma_j L <= m_j L,")
P("      m1 = 0.76 beta1 + gamma1 = %s ; m2 = %s   (both NEGATIVE)"
  % (mp.nstr(mp.mpf('0.76')*beta1v+gam1v, 10), mp.nstr(mp.mpf('0.76')*beta2v+gam2v, 10)))
P("    => -|m_j| L_j is CONCAVE in (v,t); the two radial terms together are bounded by a")
P("       negative multiple of a norm, hence the reduced objective is concave modulo atan2.")
P("")
P("(7) atan2 control: theta_j = phi_j -/+ delta with phi_j < pi - (the other angle at the hub's base)")
P("    Triangle (hub,c_j,c2): phi_j + (angle at c_j) + (angle at c2) = pi.  For j=1 the angle at c2 is A,")
P("    for j=2 it is B, both > 0 on the legal wedge; hence phi1 < pi - A and phi2 < pi - B, so")
P("    theta1 = phi1 - delta < pi - A - delta = pi - b1  and  theta2 = phi2 + delta < pi - b2,")
P("    and theta_j > 0 because Y_j > 0.  Closed-form bound:  a_j theta_j <= a_j (pi - b_j),")
P("    with a1 = 0.012841585, a2 = 0.013306528 => sum <= %s"
  % mp.nstr(mp.mpf('0.012841585')*(mp.pi-mp.mpf('1.105')) + mp.mpf('0.013306528')*(mp.pi-mp.mpf('1.068')), 8))
P("    (worst corner of the C858 box b1=1.105,b2=1.068; on the whole legal domain b_j <= acos r <= 1.187)")

import pathlib
outp = pathlib.Path(__file__).resolve().parent.parent / 'out' / 'p38_cartesian_scope.txt'
with open(outp, 'w', encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
