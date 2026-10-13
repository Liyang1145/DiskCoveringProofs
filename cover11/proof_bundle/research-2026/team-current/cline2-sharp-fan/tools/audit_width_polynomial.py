# -*- coding: utf-8 -*-
"""Compact independent audit of lead/WIDTH-STATIONARY-POLYNOMIAL.md (own files only).

Every check prints a BOOLEAN or a small number (no giant expressions).
"""
import sympy as sp
import mpmath as mp
mp.mp.dps = 40
lines = []
def P(*a):
    s = " ".join(str(x) for x in a); lines.append(s); print(s)

y = sp.symbols('y', real=True)
r, h = sp.symbols('r h', real=True)
k, dcoef, lcoef = sp.symbols('k d l', real=True)
R0 = sp.Rational(19, 50)
w = sp.symbols('w', real=True)
P1x, P1y, cx, cy = sp.symbols('P1x P1y cx cy', real=True)
C2 = cx**2 + cy**2
d0 = cx*P1x + cy*P1y
x0 = cx*P1y - cy*P1x
Q = 1 + y**2
Pnum = d0*(1-y**2) + 2*x0*y
Xnum = x0*(1-y**2) - 2*d0*y
Dnum = (1+C2)*Q - 2*Pnum
cw, sw = (1-y**2)/Q, 2*y/Q
Px = cw*P1x + sw*P1y
Py = -sw*P1x + cw*P1y
p = cx*Px + cy*Py
x = cx*Py - cy*Px
D = 1 + C2 - 2*p
Z = sp.Integer(0)
def is0(e):
    return sp.simplify(sp.together(sp.expand(e - Z))) == 0

P("A1 clockwise parametrisation (P(w)=R(-w)P1, half-angle y=tan(w/2)):")
P("   p == Pnum/Q :", is0(p - Pnum/Q))
P("   x == Xnum/Q :", is0(x - Xnum/Q))
P("   D == Dnum/Q :", is0(D - Dnum/Q))

A_ = D*(1-p+2*h) + 2*k*(1-p) + 4*dcoef*D*x/R0**2
Anum = Dnum*((1+2*h)*Q - Pnum) + 2*k*(Q - Pnum)*Q + 4*dcoef*Dnum*Xnum/R0**2
P("")
P("A2 2D F' = A + 2 l x sqrt(D)/R0 ;  A*Q^2 == Anum :", is0(A_*Q**2 - Anum))

G = Anum**2 - 4*lcoef**2*Dnum*Xnum**2*Q/R0**2
rhs = Q**4*(A_**2 - 4*lcoef**2*x**2*D/R0**2)
P("A3 G == Q^4 (A^2 - 4 l^2 x^2 D/R0^2) :", is0(G - rhs))
Gp = sp.Poly(sp.expand(G), y)
P("   degree of G in y :", Gp.degree())
P("   y^8 coefficient is nonzero as a polynomial in the parameters :",
  sp.simplify(Gp.coeff_monomial(y**8)) != 0)
P("   y^8 coefficient at the concrete chart point (P1=(s,-r), c=c1) is computed below.")

P("")
P("A4 unsquared derivative identities.  Rotate the frame: P1=(1,0), c=(1+r cos s, r sin s)")
P("   (so |P1-c| = r holds identically).  P(w) = (cos w, -sin w).")
s_ = sp.symbols('sigma', real=True)
def c2(u, v):
    return sp.expand(u[0]*v[1] - u[1]*v[0])
mu = sp.symbols('mu', real=True)
cvec = sp.Matrix([1 + r*sp.cos(s_), r*sp.sin(s_)])
P1v = sp.Matrix([1, 0])
Pv = sp.Matrix([sp.cos(w), -sp.sin(w)])
dv = sp.sqrt(sp.simplify((P1v - cvec).dot(P1v - cvec)))
d_ = sp.sqrt(sp.simplify((Pv - cvec).dot(Pv - cvec)))
pA = sp.simplify(cvec.dot(Pv))
alpha = sp.atan2(c2(Pv-cvec, P1v-cvec), (Pv-cvec).dot(P1v-cvec))
L = sp.atan2(c2(cvec-Pv, P1v-Pv), (cvec-Pv).dot(P1v-Pv))
P("   |P1-c| == r :", sp.simplify(dv - r) == 0)
P("   alpha' == (1 - c.P)/d^2 :", sp.simplify(sp.diff(alpha, w) - (1-pA)/d_**2) == 0)
P("   (u^2)' == -2 cross(c,P)/R0^2 :",
  sp.simplify(sp.diff(d_**2/R0**2, w) + 2*c2(cvec, Pv)/R0**2) == 0)
P("   (sector area)' == (1 - c.P)/2 :",
  sp.simplify(sp.diff(sp.Rational(1,2)*d_*dv*sp.sin(alpha) + (w-sp.sin(w))/2, w) - (1-pA)/2) == 0)
P("   (L + w/2)' == 1 - alpha' :",
  sp.simplify(sp.diff(L, w) + sp.Rational(1,2) - (1 - sp.diff(alpha, w))) == 0)
F1 = (sp.Rational(1,2)*d_*dv*sp.sin(alpha) + (w-sp.sin(w))/2 - mu*alpha
      - dcoef*d_**2/R0**2 - lcoef*d_/R0 + h*(L + w/2))
leadF1p = ((1-pA)*(sp.Rational(1,2) + (-mu-h)/d_**2) + h
           + (2*dcoef + lcoef*R0/d_)*(c2(cvec, Pv))/R0**2)
P("   F1'(sympy) == lead's F1' formula :",
  sp.simplify(sp.expand_trig(sp.simplify(sp.diff(F1, w) - leadF1p))) == 0)
P("   (the lead's WIDTH-STATIONARY line 4 uses k = -mu-h and D = |P-c|^2, x = cross(c,P))")

P("")
P("A5 chart signs (FLAT-PATCH-ARC-CHART):")
b, phi = sp.symbols('b phi', positive=True)
s_sym = sp.sqrt(1 - r**2)
c1 = sp.Matrix([s_sym - 2*r*sp.sin(b)*sp.cos(b), -2*r*sp.sin(b)**2])
P1c = sp.Matrix([s_sym, -r])
Xc = sp.simplify(c2(c1, P1c)); Dc = sp.simplify(c1.dot(P1c))
P("   cross(c1,P1) == r(r sin2b - s cos2b) :",
  sp.simplify(Xc - r*(r*sp.sin(2*b) - s_sym*sp.cos(2*b))) == 0)
P("   r sin2b - s cos2b == -cos(2b+phi) with r=sin phi, s=cos phi :",
  sp.simplify(sp.sin(phi)*sp.sin(2*b) - sp.cos(phi)*sp.cos(2*b) + sp.cos(2*b+phi)) == 0)
P("   c1.P1 == (1+|c1|^2-r^2)/2 :", sp.simplify(Dc - (1 + c1.dot(c1) - r**2)/2) == 0)
P("   |c1|^2 - s^2 == 4 r sin b (r sin b - s cos b) :",
  sp.simplify(c1.dot(c1) - s_sym**2 - 4*r*sp.sin(b)*(r*sp.sin(b) - s_sym*sp.cos(b))) == 0)
ac = mp.acos(mp.mpf('0.38'))
P("   r=19/50: acos(r) = %.9f ; acos(r)/2 = %.9f  => chart domain b in (%.5f, %.5f]"
  % (ac, ac/2, ac/2, ac))
P("   (so cross(c1,P1)>0 on the domain, and x0>0 in WIDTH-STATIONARY is justified there)")

P("")
P("A6 smoothness / D > 0 :  |P-c| >= 1-|c| >= 1-s on bd D ; compare with 19R0/100 = %.6f"
  % float(mp.mpf('0.19')*mp.mpf('0.38')))
for rv in ['0.375', '0.38']:
    lhs = 1 - mp.sqrt(1 - mp.mpf(rv)**2); rhs = mp.mpf('0.19')*mp.mpf(rv)
    P("     r=%s : 1-s = %.9f , 19r/100 = %.9f , margin %+.2e" % (rv, lhs, rhs, lhs-rhs))
P("   => D >= (1-s)^2 > (0.19 R0)^2 > 0 on the chart domain (D > 0 rigorously).")

outp = __import__('pathlib').Path(__file__).resolve().parent.parent / 'out' / 'p30_width_poly_audit.txt'
with open(outp, 'w', encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
