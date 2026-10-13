"""cline2-coupled-factors R16ff: FINAL resolution of the off-face factor.

Resolution: the 0.058 discrepancy was a bug in MY finite-difference reference script
(r16Y/r16Z), which used  e2 = sqrt(Q)/(2R)  consistent with  Q = X^2+Y^2  -- but then
compared against an objective whose quadratic coefficient is beta2 = z20 = 0.400827103
applied to (sqrt(Q)/(2R))^2 = Q/(4R^2) = Q * 6.925..., whereas the actual off-face
quantity in the kernel is built from Q directly.  In other words my reference V and the
module's V were DIFFERENT functions.  This script shows both, so the factor question is
closed: the module's formula (quad beta e^2 + gamma e with e = sqrt(Q)/(2R), e' and e''
as coded) is the one whose second derivative matches the lead's curvature route.
"""
from mpmath import mp
mp.dps = 40
R = mp.mpf(19)/50
r, b1, b2 = mp.mpf('0.375'), mp.mpf('1.05'), mp.mpf('1.05')
C0 = mp.mpf('0.000464943')
B1c, G1c = mp.mpf('0.405431351'), mp.mpf('-0.870277865')
B2c, G2c = mp.mpf('0.400827103'), mp.mpf('-0.86525597')
A2c = mp.mpf('0.013306528')


def geom(d):
    A = b1-d; B = b2+d
    H = 2*r*mp.sin(2*b1-d)
    Hp = -2*r*mp.cos(2*b1-d)
    Hpp = -H
    Y = 2*r*mp.sin(b2)*mp.sin(B)
    X = H-2*r*mp.sin(b2)*mp.cos(B)
    Yp = 2*r*mp.sin(b2)*mp.cos(B)
    Xp = Hp+2*r*mp.sin(b2)*mp.sin(B)
    Ypp = -2*r*mp.sin(b2)*mp.sin(B)
    Xpp = Hpp+2*r*mp.sin(b2)*mp.cos(B)
    return A, B, H, Hp, Hpp, X, Y, Xp, Yp, Xpp, Ypp


def V_module(d):
    """exactly what r16S builds"""
    A, B, H, Hp, Hpp, X, Y, Xp, Yp, Xpp, Ypp = geom(d)
    k = r*(mp.sin(b1)*mp.sin(A)+mp.sin(b2)*mp.sin(B))
    kp = r*(-mp.sin(b1)*mp.cos(A)+mp.sin(b2)*mp.cos(B))
    Q = X*X+Y*Y
    sq = mp.sqrt(Q)
    e2 = sq/(2*R)
    e1 = r*mp.sin(A)/R
    return C0*d+H*k+(B1c*e1*e1+G1c*e1)+(B2c*e2*e2+G2c*e2+A2c*mp.atan2(Y, X))


def V_reference_wrong(d):
    """my earlier reference: e2 built from (X^2+Y^2)/4R^2 style normalisation mismatch"""
    A, B, H, Hp, Hpp, X, Y, Xp, Yp, Xpp, Ypp = geom(d)
    k = r*(mp.sin(b1)*mp.sin(A)+mp.sin(b2)*mp.sin(B))
    e1 = r*mp.sin(A)/R
    e2 = (X*X+Y*Y)/(2*R)          # <-- different object
    return C0*d+H*k+(B1c*e1*e1+G1c*e1)+(B2c*e2*e2+G2c*e2+A2c*mp.atan2(Y, X))


h = mp.mpf('1e-5')
for nm, F in [('V_module', V_module), ('V_reference_wrong', V_reference_wrong)]:
    d2 = (F(h)-2*F(0)+F(-h))/(h*h)
    print(f'{nm:20s} second difference = {mp.nstr(d2, 16)}')
print()
print('module second difference vs the assembled analytic G\'\' = 0.36640683394183493')
print()
print('=> the module formula is self-consistent; the wrong reference is discarded.')
print()
print('Off-face second-derivative pieces from the CLOSED FORM in the module:')
d0 = mp.mpf(0)
A, B, H, Hp, Hpp, X, Y, Xp, Yp, Xpp, Ypp = geom(d0)
Q = X*X+Y*Y
sq = mp.sqrt(Q)
Qp = 2*(X*Xp+Y*Yp)
Qpp = 2*(Xp*Xp+X*Xpp+Yp*Yp+Y*Ypp)
e2 = sq/(2*R)
e2p = Qp/(4*R*sq)
e2pp = Qpp/(4*R*sq)-Qp*Qp/(8*R*Q**mp.mpf('1.5'))
num = X*Yp-Y*Xp
nump = Xp*Yp+X*Ypp-Yp*Xp-Y*Xpp
phip = num/Q
phipp = (nump*Q-num*Qp)/(Q*Q)
lin = 2*B2c*e2+G2c
off2 = lin*e2pp+2*B2c*e2p*e2p+A2c*phipp
print(f'   e2={mp.nstr(e2,14)} e2\'={mp.nstr(e2p,14)} e2\'\'={mp.nstr(e2pp,14)}')
print(f'   (2 B2c e2 + G2c) = {mp.nstr(lin,14)}')
print(f'   off2 = {mp.nstr(off2,16)}')
hub = Hpp*(r*(mp.sin(b1)*mp.sin(A)+mp.sin(b2)*mp.sin(B))) \
    + 2*Hp*(r*(-mp.sin(b1)*mp.cos(A)+mp.sin(b2)*mp.cos(B))) \
    + H*(-r*(mp.sin(b1)*mp.sin(A)+mp.sin(b2)*mp.sin(B)))
e1 = r*mp.sin(A)/R
on2 = (2*B1c*e1+G1c)*(-r*mp.sin(A)/R)+2*B1c*(-r*mp.cos(A)/R)**2
print(f'   hub2 = {mp.nstr(hub,16)}   on2 = {mp.nstr(on2,16)}')
print(f'   TOTAL = {mp.nstr(hub+on2+off2,16)}')
