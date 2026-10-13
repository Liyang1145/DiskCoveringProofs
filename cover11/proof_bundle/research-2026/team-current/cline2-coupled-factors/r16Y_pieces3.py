"""cline2-coupled-factors R16Y: clean piecewise validation; correct coefficients.

quad(beta,gamma,e) = beta e^2 + gamma e with
   (beta1, gamma1) = (-z16, -z78) = (+0.405431351, -0.870277865)
   (beta2, gamma2) = ( z20,  z82) = (+0.400827103, -0.86525597)
so the LINEAR coefficient is the SECOND argument: gamma1 = -0.870277865 and
gamma2 = -0.86525597, while beta1 = +0.405431351, beta2 = +0.400827103.
"""
import sys, math
from pathlib import Path
R = 19/50
r, b1, b2, d0 = 0.375, 1.05, 1.05, 0.0
B1c, G1c = 0.405431351, -0.870277865
B2c, G2c = 0.400827103, -0.86525597
A1c, A2c = 0.012841585, 0.013306528

h = 1e-4


def H_of(d):
    return 2*r*math.sin(2*b1-d)


def k_of(d):
    A = b1-d; B = b2+d
    return r*(math.sin(b1)*math.sin(A)+math.sin(b2)*math.sin(B))


def e1_of(d):
    return r*math.sin(b1-d)/R


def off_of(d):
    A = b1-d; B = b2+d
    H = 2*r*math.sin(2*b1-d)
    Y = 2*r*math.sin(b2)*math.sin(B)
    X = H-2*r*math.sin(b2)*math.cos(B)
    Q = X*X+Y*Y
    return math.sqrt(Q)/(2*R), X, Y, Q, H


hub_an = (-H_of(d0))*k_of(d0)+2*(-2*r*math.cos(2*b1-d0))*\
    (r*(-math.sin(b1)*math.cos(b1-d0)+math.sin(b2)*math.cos(b2+d0))) \
    + H_of(d0)*(-r*(math.sin(b1)*math.sin(b1-d0)+math.sin(b2)*math.sin(b2+d0)))
hub_fd = (H_of(d0+h)*k_of(d0+h)-2*H_of(d0)*k_of(d0)+H_of(d0-h)*k_of(d0-h))/(h*h)
print('HUB term: analytic %.9f  FD %.9f  gap %.2e' % (hub_an, hub_fd, hub_fd-hub_an))

e1pp_an = -r*math.sin(b1-d0)/R
e1p = -r*math.cos(b1-d0)/R
on_an = (2*B1c*e1_of(d0)+G1c)*e1pp_an+2*B1c*e1p*e1p
e1_fd = (e1_of(d0+h)-2*e1_of(d0)+e1_of(d0-h))/(h*h)
on_fd = (2*B1c*e1_of(d0)+G1c)*e1_fd+2*B1c*((e1_of(d0+h)-e1_of(d0-h))/(2*h))**2
print('ON-face term: analytic %.9f  FD %.9f  gap %.2e' % (on_an, on_fd, on_fd-on_an))

e2_0, X0, Y0, Q0, H0 = off_of(d0)
e2p_fd = (off_of(d0+h)[0]-off_of(d0-h)[0])/(2*h)
e2pp_fd = (off_of(d0+h)[0]-2*e2_0+off_of(d0-h)[0])/(h*h)
lin = 2*B2c*e2_0+G2c
off_an = lin*e2pp_fd+2*B2c*e2p_fd**2
# phi2'
d2 = 2*r*math.sin(b2)*math.cos(b2+d0)
d1 = -2*r*math.cos(2*b1-d0)+2*r*math.sin(b2)*math.sin(b2+d0)
phi2p = (X0*d2-Y0*d1)/Q0
print('OFF-face term: lin*e2\'\' + 2 beta2 (e2\')^2 = %.9f' % off_an)
print('   + 2 a2 phi2\' = %.9f   -> off total %.9f' % (2*A2c*phi2p, off_an+2*A2c*phi2p))
print('   e2\' = %.9f  e2\'\' = %.9f  phi2\' = %.9f' % (e2p_fd, e2pp_fd, phi2p))

print('\nTOTAL: hub+on+off = %.9f' % (hub_an+on_an+off_an+2*A2c*phi2p))
print('FD of full G\'    = 0.3002587324')
print('my earlier analytic G\'\' = 0.36640683394183493')
print('difference of the two analytic totals = %.6f'
      % (0.36640683394183493-(hub_an+on_an+off_an+2*A2c*phi2p)))
