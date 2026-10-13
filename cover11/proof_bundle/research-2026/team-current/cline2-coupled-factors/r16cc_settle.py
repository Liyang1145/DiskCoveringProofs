"""cline2-coupled-factors R16cc: settle the off-face second-derivative factor at one point
with matched precision (mpmath 40 dps, several step sizes), then report.

Reference point: r=0.375, b1=b2=1.05, delta=0 (LEGAL).
Pieces of V:  C0*delta + H*k + [beta1 e1^2 + gamma1 e1] + [beta2 e2^2 + gamma2 e2 + a2 phi2]
"""
from mpmath import mp
mp.dps = 40
R = mp.mpf(19)/50
r, b1, b2 = mp.mpf('0.375'), mp.mpf('1.05'), mp.mpf('1.05')
C0 = mp.mpf('0.000464943')
B1c, G1c = mp.mpf('0.405431351'), mp.mpf('-0.870277865')
B2c, G2c = mp.mpf('0.400827103'), mp.mpf('-0.86525597')
A2c = mp.mpf('0.013306528')


def off(d):
    B = b2+d
    H = 2*r*mp.sin(2*b1-d)
    Y = 2*r*mp.sin(b2)*mp.sin(B)
    X = H-2*r*mp.sin(b2)*mp.cos(B)
    Q = X*X+Y*Y
    return mp.sqrt(Q)/(2*R), mp.atan2(Y, X), X, Y, Q


for hh in ['1e-3', '1e-4', '1e-5', '1e-6']:
    h = mp.mpf(hh)
    d0 = mp.mpf(0)
    e2pp = (off(d0+h)[0]-2*off(d0)[0]+off(d0-h)[0])/(h*h)
    e2p = (off(d0+h)[0]-off(d0-h)[0])/(2*h)
    phipp = (off(d0+h)[1]-2*off(d0)[1]+off(d0-h)[1])/(h*h)
    e2 = off(d0)[0]
    part = (2*B2c*e2+G2c)*e2pp+2*B2c*e2p*e2p+A2c*phipp
    print(f'h={hh:8s}: e2\'={mp.nstr(e2p,16)} e2\'\'={mp.nstr(e2pp,16)} '
          f'off\'\'={mp.nstr(part,16)}')

print()
print('--- analytic off-face second derivative with the CLOSED-FORM derivatives ---')


def off_analytic(d):
    B = b2+d
    H = 2*r*mp.sin(2*b1-d)
    Hp = -2*r*mp.cos(2*b1-d)
    Hpp = -H
    Y = 2*r*mp.sin(b2)*mp.sin(B)
    X = H-2*r*mp.sin(b2)*mp.cos(B)
    Yp = 2*r*mp.sin(b2)*mp.cos(B)
    Xp = Hp+2*r*mp.sin(b2)*mp.sin(B)
    Ypp = -2*r*mp.sin(b2)*mp.sin(B)
    Xpp = Hpp+2*r*mp.sin(b2)*mp.cos(B)
    Q = X*X+Y*Y
    Qp = 2*(X*Xp+Y*Yp)
    Qpp = 2*(Xp*Xp+X*Xpp+Yp*Yp+Y*Ypp)
    sq = mp.sqrt(Q)
    e2 = sq/(2*R)
    e2p = Qp/(4*R*sq)
    # e2'' : d/dd [Qp/(4 R sqrtQ)] = Qpp/(4 R sqrtQ) - Qp^2/(8 R Q^{3/2})
    e2pp = Qpp/(4*R*sq)-Qp*Qp/(8*R*Q**mp.mpf('1.5'))
    # phi2'' : d/dd [(X Yp - Y Xp)/Q]
    num = X*Yp-Y*Xp
    nump = Xp*Yp+X*Ypp-Yp*Xp-Y*Xpp
    phip = num/Q
    phipp = (nump*Q-num*Qp)/(Q*Q)
    return e2, e2p, e2pp, phip, phipp


e2, e2p, e2pp, phip, phipp = off_analytic(mp.mpf(0))
print(f'analytic e2    = {mp.nstr(e2,16)}')
print(f'analytic e2\'   = {mp.nstr(e2p,16)}')
print(f'analytic e2\'\'  = {mp.nstr(e2pp,16)}')
print(f'analytic phi2\' = {mp.nstr(phip,16)}')
print(f'analytic phi2\'\'= {mp.nstr(phipp,16)}')
print()
part = (2*B2c*e2+G2c)*e2pp+2*B2c*e2p*e2p+A2c*phipp
print(f'analytic off\'\' = {mp.nstr(part,16)}')
print()
print('--- now the code\'s factor: compare 2*B2c*e2p^2 vs the FD-consistent value ---')
print(f'2*B2c*e2p^2        = {mp.nstr(2*B2c*e2p*e2p,16)}')
print(f'(2*B2c*e2+G2c)*e2pp= {mp.nstr((2*B2c*e2+G2c)*e2pp,16)}')
print(f'A2c*phipp          = {mp.nstr(A2c*phipp,16)}')
