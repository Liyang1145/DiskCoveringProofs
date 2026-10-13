# -*- coding: utf-8 -*-
"""verify_central_patch.py — IDENTITY VERIFICATION (no search, no optimisation).

Every claim that will be written into CENTRAL-PATCH-7-FACTOR.md is checked here:
either symbolically (sympy, exact rationals in r and the parameters) or at 50-digit
precision on a few fixed sample points (NOT random search, NOT an extremum).

Caliber: unit circle; 9+2 equal disks of radius r <= 19/50; all lengths in units of the
unit-circle radius; angles radians. Chart of the central patch:
    a = asin r,  P1 = (cos a, -sin a),  P2 = (cos a, sin a),  c2 = (cos a, 0).
"""
import sys
import mpmath as mp
import sympy as sp

mp.mp.dps = 50
lines = []
def P(*args):
    s = " ".join(str(a) for a in args)
    lines.append(s); print(s)

# ---------------------------------------------------------------- symbolic core
a, r, al, u = sp.symbols('a r alpha u', positive=True)
# exact identities in the SECTOR (intrinsic data alpha, u, v=1)
Q = (u - 1)**2 + 4*u*sp.sin(al/2)**2
L = sp.atan2(sp.sin(al), u - sp.cos(al))
T = sp.pi - al - L

P("SP1  Q = (u-1)^2 + 4u sin^2(alpha/2)   [law of cosines in the sector triangle]")
P("     check  u^2+1-2u cos(alpha) - Q = ",
  sp.simplify(u**2 + 1 - 2*u*sp.cos(al) - Q))
P("")
P("SP2  L+T+alpha = pi  [L=atan2(sin a, u-cos a), T=pi-alpha-L]  -> trivial")
P("     sin(alpha)/sin(L) = chord,  sin(L)/... : law of sines check")
chord = sp.sqrt(Q)
P("     sin(L)*chord - sin(al) = ", sp.simplify(sp.sin(L)*chord - sp.sin(al)))
P("     sin(T)*chord - sin(al) = ", sp.simplify(sp.sin(T)*chord - sp.sin(al)))

# Coordinates of c1 given (alpha,u) with v=1:  psi = a + w/2 + T, c1 = P1 - r(sin psi, cos psi)
P("")
P("-- verifying the closed forms c1 = P1 - r (sin psi1, cos psi1), psi1 = a+w/2+T ----")
wsym = sp.symbols('w', positive=True)          # w = sector arc width
psi = a + wsym/2 + T
P1x, P1y = sp.cos(a), -sp.sin(a)
c1x = P1x - r*sp.sin(psi)
c1y = P1y - r*sp.cos(psi)
P0x, P0y = sp.cos(a + wsym), -sp.sin(a + wsym)
# distance |c1-P1| should be r;  |c1-P0| should be r u  PROVIDED  sin(w/2)=r*sqrt(Q)/2
sub = {sp.sin(wsym/2): r*chord/2}
for expr, name, target in [
        ((c1x-P1x)**2 + (c1y-P1y)**2, "|c1-P1|^2", r**2),
        ((c1x-P0x)**2 + (c1y-P0y)**2, "|c1-P0|^2", r**2*u**2)]:
    d = sp.simplify(sp.expand_trig(sp.expand(expr)).subs(sp.sin(wsym/2)**2, (r*chord/2)**2))
    P("   %s - %s  =  %s" % (name, sp.simplify(target),
      sp.simplify(sp.expand(d - target).rewrite(sp.cos))))

# ---------------------------------------------------------------- numerics
P("")
P("="*78)
P("NUMERIC IDENTITY CHECKS (mpmath dps=50) on fixed sample points")
P("="*50)

def sector_geom(alpha, uu, rr):
    a_ = mp.asin(rr)
    Q_ = (uu-1)**2 + 4*uu*mp.sin(alpha/2)**2
    w_ = 2*mp.asin(rr*mp.sqrt(Q_)/2)
    L_ = mp.atan2(mp.sin(alpha), uu - mp.cos(alpha))
    T_ = mp.pi - alpha - L_
    return a_, Q_, w_, L_, T_

CASES = [(mp.mpf('0.3'), mp.mpf('0.6'), mp.mpf('0.32')),
         (mp.mpf('1.2'), mp.mpf('0.85'), mp.mpf('0.38')),
         (mp.mpf('2.2'), mp.mpf('0.5'), mp.mpf('0.36')),
         (mp.mpf('0.9'), mp.mpf('1.0'), mp.mpf('0.19'))]

for alpha, uu, rr in CASES:
    a_, Q_, w_, L_, T_ = sector_geom(alpha, uu, rr)
    P("")
    P("case alpha=%s u=%s r=%s :  w=%s L=%s T=%s" %
      (mp.nstr(alpha, 6), mp.nstr(uu, 6), mp.nstr(rr, 6),
       mp.nstr(w_, 12), mp.nstr(L_, 12), mp.nstr(T_, 12)))
    P1 = mp.matrix([mp.cos(a_), -mp.sin(a_)])
    P2 = mp.matrix([mp.cos(a_), mp.sin(a_)])
    c2 = mp.matrix([mp.cos(a_), 0])
    P0 = mp.matrix([mp.cos(a_+w_), -mp.sin(a_+w_)])
    psi = a_ + w_/2 + T_
    c1 = mp.matrix([mp.cos(a_) - rr*mp.sin(psi), -mp.sin(a_) - rr*mp.cos(psi)])
    P("   |c1-P1| - r            = %+.3e" % (mp.norm(c1-P1) - rr))
    P("   |c1-P0| - r*u          = %+.3e" % (mp.norm(c1-P0) - rr*uu))
    v1 = P0 - c1; v2 = P1 - c1
    ang = mp.atan2(v1[0]*v2[1]-v1[1]*v2[0], v1[0]*v2[0]+v1[1]*v2[1])
    P("   angle at c1 - alpha     = %+.3e" % (ang - alpha))
    # base angles
    w1v = P0 - P1; w2v = c1 - P1
    angP1 = mp.atan2(w1v[0]*w2v[1]-w1v[1]*w2v[0], w1v[0]*w2v[0]+w1v[1]*w2v[1])
    P("   angle at P1 - T         = %+.3e" % (angP1 - T_))
    # switch half-angle 2b1
    e1 = (c1-P1)/rr; e2 = (c2-P1)/rr
    two_b = mp.acos(max(mp.mpf(-1), min(mp.mpf(1), e1[0]*e2[0]+e1[1]*e2[1])))
    P("   geom 2b1                = %s ; pi-psi = %s ; diff = %+.3e"
      % (mp.nstr(two_b, 12), mp.nstr(mp.pi-psi, 12), two_b-(mp.pi-psi)))
    P("   |c1-c2| - 2 r sin b1    = %+.3e" % (mp.norm(c1-c2) - 2*rr*mp.sin(two_b/2)))
    # closure with degenerate sector 2 (L2=0, w2=2a)
    clo = T_ + 0 + two_b + (w_ + 2*a_)/2 - mp.pi
    P("   closure T1+L2+2b1+(w1+w2)/2-pi = %+.3e" % clo)
    # face constraint equivalence
    h9 = mp.matrix([mp.mpf('-0.10'), mp.mpf('0.05')])
    d12 = mp.norm(c1-c2); d2h = mp.norm(c2-h9); dh1 = mp.norm(h9-c1)
    cr = (c2-c1)[0]*(h9-c1)[1] - (c2-c1)[1]*(h9-c1)[0]
    rho = d12*d2h*dh1/(2*abs(cr))
    Ahat = mp.acos(max(mp.mpf(-1), min(mp.mpf(1),
                   ((c1-h9)[0]*(c2-h9)[0]+(c1-h9)[1]*(c2-h9)[1])/(dh1*d2h))))
    P("   rho1 - r                = %+.3e   (rho1/(r sin b1) = %s)"
      % (rho - rr, mp.nstr(rho/(rr*mp.sin(two_b/2)), 12)))
    P("   sin(Ahat) - sin(b1)     = %+.3e   Ahat=%s  b1=%s"
      % (mp.sin(Ahat) - mp.sin(two_b/2), mp.nstr(Ahat, 10), mp.nstr(two_b/2, 10)))
    P("   sign(rho1-r)*sign(sinAhat-sin b1) = %+d"
      % (mp.sign(rho-rr)*mp.sign(mp.sin(Ahat)-mp.sin(two_b/2))))
    # automatic hub/switch necessity
    P("   |P1-h9| - r            = %+.3e   (>=0 iff |h9| <= 1-r ; |h9|=%s)"
      % (mp.norm(P1-h9) - rr, mp.nstr(mp.norm(h9), 8)))
    hstar = (1-rr)*P1
    P("   |h*-P1| - r  at h*=(1-r)P1 = %+.3e ; |h*| - (1-r) = %+.3e"
      % (mp.norm(hstar-P1) - rr, mp.norm(hstar) - (1-rr)))

P("")
P("="*78)
P("SECTOR-2 (DEGENERATE) EXACT DATA at r = 19/50:")
rr = mp.mpf(19)/50
aa = mp.asin(rr)
P("   a = asin r = %s ; x = cos a = %s ; x^2+r^2-1 = %+.3e"
  % (mp.nstr(aa, 20), mp.nstr(mp.cos(aa), 20), mp.cos(aa)**2 + rr**2 - 1))
P("   P1=(%s,%s) P2=(%s,%s) c2=(%s,%s)"
  % (mp.nstr(mp.cos(aa), 18), mp.nstr(-mp.sin(aa), 18),
     mp.nstr(mp.cos(aa), 18), mp.nstr(mp.sin(aa), 18),
     mp.nstr(mp.cos(aa), 18), "0"))
P("   |P1-c2| - r = %+.3e ; |P1| - 1 = %+.3e" %
  (mp.norm(mp.matrix([mp.cos(aa), -mp.sin(aa)]) - mp.matrix([mp.cos(aa), 0])) - rr,
   mp.norm(mp.matrix([mp.cos(aa), -mp.sin(aa)])) - 1))
P("   w2 = 2a = %s ; u2=v2=1 ; alpha2=pi ; T2=L2=0" % mp.nstr(2*aa, 20))
P("   V_s2 = a - sin(2a)/2 = %s" % mp.nstr(aa - mp.sin(2*aa)/2, 20))
P("   1-r = %s  vs cos a = %s  (hub interiority is the stronger bound: %s)"
  % (mp.nstr(1-rr, 12), mp.nstr(mp.cos(aa), 12), 1-rr < mp.cos(aa)))

with open(__file__.replace('tools', 'out').replace('.py', '.txt').replace('verify_central_patch', 'p23_verify_patch'), 'w',
          encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
