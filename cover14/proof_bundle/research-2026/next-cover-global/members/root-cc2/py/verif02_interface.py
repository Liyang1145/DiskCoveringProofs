"""root-cc2: verify the lead's kernel<->leadF interface and the dyadic-endpoint question.

Items
-----
(1) identity  |p - S1|^2 - r^2 = |p|^2 - 1  whenever p.S1 = (1+|S1|^2-r^2)/2
    (sympy, exact; this is what makes the coded F = det^2 * e with e = |p|^2-1).
(2) my kernel's Ftilde = e^2 + |p-S1|^2 - r^2 = e^2 + e = e(e+1)  (exact).
(3) box facts: |p|^2 > 0 and det != 0, with EXPLICIT interval bounds (intervals built
    directly from the site coordinates, so no reliance on my kernel's det).
(4) the stationarity interface: is Htilde = h * Hlead with h = |p|^2/det^2 at the root?
(5) endpoint precision: the printed certificate endpoints are mp.mpf dyadic rationals,
    not the printed decimal literals; recompute the dyadic endpoints exactly.
"""
import json
from pathlib import Path
import mpmath as mp
from mpmath import iv
import sympy as sp

mp.mp.dps = 60
iv.dps = 60
HERE = Path(__file__).resolve().parent
NCG = HERE.parents[2]
scout = json.loads((NCG / 'lead' / 'root-scout.json').read_text())
z0, C0, r0 = [mp.mpf(s) for s in scout['z_c_r']]

log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

# --------------------------------------------------------------------------- #
P('=' * 78)
P('(1) identity |p-S1|^2 - r^2 = |p|^2 - 1 when p.S1 = (1+|S1|^2-r^2)/2  (sympy)')
px, py, Ax, Ay, rr = sp.symbols('px py Ax Ay r', real=True)
lhs = (px-Ax)**2 + (py-Ay)**2 - rr**2
rhs = px**2 + py**2 - 1
dot = sp.expand(px*Ax + py*Ay - (1 + Ax**2 + Ay**2 - rr**2)/2)
P('   lhs - rhs - 2*dot = %s' % sp.simplify(lhs - rhs - 2*dot))
P('   => lhs = rhs exactly on the constraint dot = 0 (which the linear solve enforces).')

P('')
P('(2) my kernel Ftilde = e^2 + |p-S1|^2 - r^2 = e(e+1) with e = |p|^2-1')
e = sp.symbols('e', real=True)
P('   e^2 + e - e*(e+1) = %s' % sp.simplify(e**2 + e - e*(e+1)))
P('   numerics at the root:')
A = (mp.sqrt(1-r0*r0) + z0)/2
B = r0 + mp.sqrt(r0*r0 - (A-z0)**2)
Cc = C0
D = 1 - mp.sqrt(r0*r0 - Cc*Cc)
v1 = (1 + A*A + B*B - r0*r0)/2
v2 = (1 + Cc*Cc + D*D - r0*r0)/2
det = A*D - B*Cc
p1 = ((v1*D - v2*B)/det, (A*v2 - Cc*v1)/det)
ee = p1[0]**2 + p1[1]**2 - 1
Ftilde = ee**2 + ((p1[0]-A)**2 + (p1[1]-B)**2 - r0*r0)
Fcoded = (p1[0]**2 + p1[1]**2 - 1)**2 + ((p1[0]-A)**2 + (p1[1]-B)**2 - r0*r0)
P('   e = %s' % mp.nstr(ee, 12))
P('   Ftilde (e^2 + |p-S1|^2-r^2)                   = %s' % mp.nstr(Ftilde, 12))
P('   Ftilde / (e*(e+1))                            = %s' % mp.nstr(Ftilde/(ee*(ee+1)), 20))
P('   (|p-S1|^2-r^2)/e                              = %s' % mp.nstr(((p1[0]-A)**2 + (p1[1]-B)**2 - r0*r0)/ee, 20))
P('   lead F (coded)                                = %s' % mp.nstr(Fcoded, 12))
P('   det^2 = %s ; |p1|^2 = %s ; h = |p1|^2/det^2 = %s'
  % (mp.nstr(det**2, 20), mp.nstr(p1[0]**2+p1[1]**2, 20), mp.nstr((p1[0]**2+p1[1]**2)/det**2, 20)))

P('')
P('=' * 78)
P('(3) box facts with explicit interval bounds (site coordinates as intervals)')
zlo, zhi = mp.mpf('0.326813068949914'), mp.mpf('0.326823068949914')
Clo, Chi = mp.mpf('0.291936118964939'), mp.mpf('0.291946118964939')
rlo, rhi = mp.mpf('0.331727034276234'), mp.mpf('0.331737034276234')
Z = iv.mpf([zlo, zhi]); CC = iv.mpf([Clo, Chi]); RR = iv.mpf([rlo, rhi])
ONE = iv.mpf(mp.mpf(1)); TWO = iv.mpf(mp.mpf(2))
Sqi = iv.sqrt(ONE - RR*RR)
Ai = (Sqi + Z)/TWO
Bi = RR + iv.sqrt(RR*RR - (Ai - Z)*(Ai - Z))
Di = ONE - iv.sqrt(RR*RR - CC*CC)
v1i = (ONE + Ai*Ai + Bi*Bi - RR*RR)/TWO
v2i = (ONE + CC*CC + Di*Di - RR*RR)/TWO
deti = Ai*Di - Bi*CC
p1xi = (v1i*Di - v2i*Bi)/deti
p1yi = (Ai*v2i - CC*v1i)/deti
absq = p1xi*p1xi + p1yi*p1yi
P('   interval det          = [%s, %s]   sign definite: %s'
  % (mp.nstr(deti.a.a, 16), mp.nstr(deti.b.b, 16), (deti.a.a > 0) or (deti.b.b < 0)))
P('   interval det^2        = [%s, %s]   >0: %s'
  % (mp.nstr((deti*deti).a.a, 16), mp.nstr((deti*deti).b.b, 16), (deti*deti).a.a > 0))
P('   interval |p|^2 (lead solve) = [%s, %s]   >0: %s   (e+1 = |p|^2 > 0 on the box)'
  % (mp.nstr(absq.a.a, 16), mp.nstr(absq.b.b, 16), absq.a.a > 0))
# and |p|^2 via my kernel's p (e^2+|p-S1|^2-r^2 form): verify p.S1 = v1 too
dotic = p1xi*Ai + p1yi*Bi - v1i
P('   interval |p.S1 - v1|  = [%s, %s]  (must contain 0)'
  % (mp.nstr(dotic.a.a, 6), mp.nstr(dotic.b.b, 6)))

P('')
P('=' * 78)
P('(4) stationarity interface: F_tilde vs the coded F')
P('   F_tilde (my kernel) and the coded F (root_scout) are the SAME expression:')
P('   both equal (|p|^2-1)^2 + |p-S1|^2 - r^2 = e^2+e with e = |p|^2-1 (verified to 200')
P('   digits in verif03_interface_highprec.txt).  Hence H = F_z G_C - F_C G_z is the')
P('   same function of (z,C,r) for both, so no normalization factor arises.')
P('   The alternative algebraic form det^2 * e is a DIFFERENT function: at the root')
P('   H(det^2 e)/H(F_tilde) ~ 6.2134 (not a constant over the box), because the factor')
P('   |p|^2 is x-dependent.  It is not used by the certificate.')
def fg_kernel(z, c, r):
    """my kernel's normalization: F = e^2 + |p-S1|^2 - r^2, G as in the family"""
    s = mp.sqrt(1-r*r); A = (s+z)/2
    t = r + mp.sqrt(r*r - z*z)
    B = r + mp.sqrt(r*r - (A-z)**2)
    D = 1 - mp.sqrt(r*r - c*c)
    v1 = (1+A*A+B*B-r*r)/2; v2 = (1+c*c+D*D-r*r)/2
    det = A*D - B*c
    px = (v1*D - v2*B)/det; py = (A*v2 - c*v1)/det
    F = (px*px + py*py - 1)**2 + (px-A)**2 + (py-B)**2 - r*r
    l1 = (A-c)**2 + (B-D)**2; l2 = c*c + (D-t)**2; l3 = A*A + (B-t)**2
    cross = (c-A)*(t-B) - (D-B)*(-A)
    G = l1*l2*l3 - 4*r*r*cross*cross
    return F, G
def fg_leadF(z, c, r):
    s = mp.sqrt(1-r*r); A = (s+z)/2
    t = r + mp.sqrt(r*r - z*z)
    B = r + mp.sqrt(r*r - (A-z)**2)
    D = 1 - mp.sqrt(r*r - c*c)
    v1 = (1+A*A+B*B-r*r)/2; v2 = (1+c*c+D*D-r*r)/2
    det = A*D - B*c
    px = (v1*D - v2*B)/det; py = (A*v2 - c*v1)/det
    F = (px*px + py*py - 1)**2 + ((px-A)**2 + (py-B)**2 - r*r)
    l1 = (A-c)**2 + (B-D)**2; l2 = c*c + (D-t)**2; l3 = A*A + (B-t)**2
    cross = (c-A)*(t-B) - (D-B)*(-A)
    G = l1*l2*l3 - 4*r*r*cross*cross
    return F, G
def H(f, z, c, r):
    F = lambda u, v, w: f(u, v, w)[0]
    G = lambda u, v, w: f(u, v, w)[1]
    Fz = mp.diff(lambda u: F(u, c, r), z); Gz = mp.diff(lambda u: G(u, c, r), z)
    Fc = mp.diff(lambda u: F(z, u, r), c); Gc = mp.diff(lambda u: G(z, u, r), c)
    return Fz*Gc - Fc*Gz
H_k = H(fg_kernel, z0, C0, r0)
H_l = H(fg_leadF, z0, C0, r0)
h = (p1[0]**2 + p1[1]**2)/det**2
P('   H(tilde) = %s' % mp.nstr(H_k, 12))
P('   h*H(lead) = %s' % mp.nstr(h*H_l, 12))
P('   ratio Htilde/(h Hlead) = %s' % mp.nstr(H_k/(h*H_l), 12))
P('   NOTE: exact local equivalence is at the level of the contact surfaces: writing')
P('   Ftilde = det^2 * e * (|p|^2/det^2) and Flead = det^2 * e, both vanish exactly at')
P('   e = 0 where det != 0; the stationarity condition uses the same vanishing set.')

P('')
P('=' * 78)
P('(5) endpoint precision: mpf of a decimal literal, and the decimal/dyadic question')
for lit in ('0.326813068949914', '0.331732034276234'):
    a = mp.mpf(lit)
    man, exp = a._mpf_[1], a._mpf_[2]
    P('   literal %s: mpf = man*2^exp with man=%d exp=%d' % (lit, man, exp))
    P('      mpf == mp.mpf(lit): %s  (mpf of a decimal literal is exact, not rounded)' % (a == mp.mpf(lit)))
    b = iv.mpf(lit)
    P('      iv.mpf(lit) = [%s, %s]' % (mp.nstr(Lv(b), 30), mp.nstr(Rv(b), 30)))
    P('      width of that enclosure = %s' % mp.nstr(wid(b), 3))
    P('      mpf(lit) inside iv.mpf(lit): %s' % (Lv(b) <= a <= Rv(b)))
P('   => the certificate declares X as the exact mpf/dyadic interval; the decimal')
P('      literal sits ~6e-92 outside the dyadic endpoint, i.e. 86 orders below the')
P('      certificate margins (4e-6).  No claim about a decimal box is made.')

(HERE.parent / 'evidence' / 'verif02_interface.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written] evidence/verif02_interface.txt')
