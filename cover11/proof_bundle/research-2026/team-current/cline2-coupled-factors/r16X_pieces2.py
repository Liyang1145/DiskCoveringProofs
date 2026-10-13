"""cline2-coupled-factors R16X: clean piecewise validation of G'' to locate the 0.066 gap."""
import sys, math
from pathlib import Path
from mpmath import iv
iv.dps = 30
sys.path.insert(0, str(Path(__file__).parent))
from r16S_g2_legal import RR, TWO

r, b1, b2, d0 = 0.375, 1.05, 1.05, 0.0
rr, b1i, b2i = iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2))
A0 = b1i-iv.mpf(repr(d0)); B0 = b2i+iv.mpf(repr(d0))
H0 = TWO*rr*iv.sin(TWO*b1i-iv.mpf(repr(d0)))
Hp0 = -TWO*rr*iv.cos(TWO*b1i-iv.mpf(repr(d0)))
k0 = rr*(iv.sin(b1i)*iv.sin(A0)+iv.sin(b2i)*iv.sin(B0))
k1 = rr*(-iv.sin(b1i)*iv.cos(A0)+iv.sin(b2i)*iv.cos(B0))
k2 = -rr*(iv.sin(b1i)*iv.sin(A0)+iv.sin(b2i)*iv.sin(B0))
hub_an = (-H0)*k0+TWO*Hp0*k1+H0*k2
print('HUB term')
print('  analytic H\'\'k + 2H\'k\' + Hk\'\' =', float(hub_an.a))


def H_of(d):
    return 2*r*math.sin(2*b1-d)


def k_of(d):
    A = b1-d; B = b2+d
    return r*(math.sin(b1)*math.sin(A)+math.sin(b2)*math.sin(B))


h = 1e-4
hub_fd = (H_of(d0+h)*k_of(d0+h)-2*H_of(d0)*k_of(d0)+H_of(d0-h)*k_of(d0-h))/(h*h)
print('  finite difference of H*k     =', hub_fd)
print('  gap =', hub_fd-float(hub_an.a))

print('\nON-FACE term')
e1_an = r*math.sin(A0)/RR
e1pp_an = -r*math.sin(b1-d0)/float(RR)
term_an = (2*(-0.405431351)*float(e1_an.a)+(-0.870277865))*e1pp_an \
    + 2*(-0.405431351)*(r*math.cos(b1-d0)/float(RR))**2
print('  analytic =', term_an)


def e1_of(d):
    return r*math.sin(b1-d)/float(RR)


e1_fd = (e1_of(d0+h)-2*e1_of(d0)+e1_of(d0-h))/(h*h)
print('  e1 FD =', e1_fd, ' vs analytic e1\'\' =', e1pp_an)
print('  term from FD =', (2*(-0.405431351)*e1_of(d0)+(-0.870277865))*e1_fd
      + 2*(-0.405431351)*((e1_of(d0+h)-e1_of(d0-h))/(2*h))**2)

print('\nOFF-FACE term')
BETA2, GAMMA2, ALPHA2 = -0.86525597, -0.86525597, 0.013306528
print('  (beta2 = z82 =', BETA2, '; gamma2 = z20 = 0.400827103, so the linear coeff is'
      ' 0.400827103 not -0.86525597 -- checking both)')


def off_of(d):
    A = b1-d; B = b2+d
    H = 2*r*math.sin(2*b1-d)
    Hp = -2*r*math.cos(2*b1-d)
    Y = 2*r*math.sin(b2)*math.sin(B)
    X = H-2*r*math.sin(b2)*math.cos(B)
    Q = X*X+Y*Y
    return math.sqrt(Q)/(2*float(RR)), X, Y, Q


e2_0, X0_, Y0_, Q0_ = off_of(d0)
e2p_fd = (off_of(d0+h)[0]-off_of(d0-h)[0])/(2*h)
e2pp_fd = (off_of(d0+h)[0]-2*e2_0+off_of(d0-h)[0])/(h*h)
print('  e2 =', e2_0, ' e2\' FD =', e2p_fd, ' e2\'\' FD =', e2pp_fd)
lin2 = 2*float(iv.mpf('0.400827103').a)*e2_0+float(iv.mpf('-0.86525597').a) \
    if False else 2*0.400827103*e2_0+(-0.86525597)
print('  2*beta2*e2 + gamma2 =', lin2)
print('  term = lin*e2\'\' + 2*beta2*(e2\')^2 =', lin2*e2pp_fd+2*BETA2*e2p_fd**2)
d2 = 2*r*math.sin(b2)*math.cos(b2+d0)
d1 = -2*r*math.cos(2*b1-d0)+2*r*math.sin(b2)*math.sin(b2+d0)
phi2p = (X0_*d2-Y0_*d1)/Q0_
print('  phi2\' =', phi2p, ' -> 2*alpha2*phi2\' =', 2*ALPHA2*phi2p)

print('\nTOTAL (mixed-up coefficients aside) and the FD reference')
print('  FD of full G\' = 0.3002587324154301')
print('  hub + on + off =', float(hub_an.a), '+',
      (2*(-0.405431351)*float(e1_an.a)+(-0.870277865))*e1pp_an
      + 2*(-0.405431351)*(r*math.cos(b1-d0)/float(RR))**2, '+',
      lin2*e2pp_fd+2*BETA2*e2p_fd**2+2*ALPHA2*phi2p)
