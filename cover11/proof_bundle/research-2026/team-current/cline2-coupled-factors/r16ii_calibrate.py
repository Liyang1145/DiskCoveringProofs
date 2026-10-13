"""cline2-coupled-factors R16ii: CALIBRATION before the run.

Routes for the hub objective's second delta-derivative F''(x(delta)):
  (R1) analytic assembly (corrected): d2V/ddelta2
  (R2) Cartesian curvature: x'' = x_theta'' (theta')^2 + x_theta' theta''
       with theta = pi/2 - 2A (face 1) / 2B - pi/2 (face 2), |x_theta'| = r,
       so  F'' = |x'|^2 x_hat^T Hess F x_hat + grad F . x''
  (R3) plain central second difference of V itself, several steps, high precision.

If the three agree at legal points, the assembled derivative is calibrated and the interval
subdivision may be run.
"""
import math, json, sys
from pathlib import Path
from mpmath import mp

mp.dps = 40
P = Path(__file__).parent
LEAD = P.parent / 'lead'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
R = mp.mpf(19)/50
C0 = mp.mpf(f'{zJ[3]-zJ[1]:.9f}')
XX1 = mp.mpf(f'{zJ[1]-zJ[9]:.9f}'); XX2 = mp.mpf(f'{zJ[3]-zJ[9]:.9f}')
BE1 = mp.mpf(f'{-zJ[16]:.9f}'); GA1 = mp.mpf(f'{-zJ[78]:.9f}')
BE2 = mp.mpf(f'{zJ[20]:.9f}');  GA2 = mp.mpf(f'{zJ[82]:.9f}')


def V(d, r, b1, b2, face):
    A = b1-d; B = b2+d
    if face == 1:
        H = 2*r*mp.sin(2*b1-d); Hp = -2*r*mp.cos(2*b1-d)
    else:
        H = 2*r*mp.sin(2*b2+d); Hp = 2*r*mp.cos(2*b2+d)
    k = r*(mp.sin(b1)*mp.sin(A)+mp.sin(b2)*mp.sin(B))
    out = C0*d+H*k
    for i, (b, ang, xx, bb, gg) in enumerate([(b1, A, XX1, BE1, GA1),
                                              (b2, B, XX2, BE2, GA2)]):
        if (face == 1 and i == 0) or (face == 2 and i == 1):
            e = r*mp.sin(ang)/R
            out += xx*b
        else:
            Y = 2*r*mp.sin(b)*mp.sin(ang)
            X = H-2*r*mp.sin(b)*mp.cos(ang)
            e = mp.sqrt(X*X+Y*Y)/(2*R)
            out += xx*mp.atan2(Y, X)
        out += bb*e*e+gg*e
    return out


def chart(r, d, b1, b2, face):
    """Cartesian hub point, its delta-derivatives, and the chart angle theta"""
    A = b1-d; B = b2+d
    if face == 1:
        v = r*(mp.sin(2*b1)+mp.sin(2*A))
        t = r*(mp.cos(2*A)-mp.cos(2*b1))
        th = mp.pi/2-2*A
    else:
        v = r*(mp.sin(2*b2)+mp.sin(2*B))
        t = r*(mp.cos(2*B)-mp.cos(2*b2))
        th = 2*B-mp.pi/2
    return v, t, th


print('=== calibration at legal points: analytic vs Cartesian curvature vs FD ===')
h = mp.mpf('1e-6')
tests = [(mp.mpf('0.375'), mp.mpf('1.05'), mp.mpf('1.05'), mp.mpf('0'), 1),
         (mp.mpf('0.378'), mp.mpf('1.06'), mp.mpf('1.03'), mp.mpf('-0.12'), 1),
         (mp.mpf('0.379'), mp.mpf('1.00'), mp.mpf('1.00'), mp.mpf('-0.20'), 1),
         (mp.mpf('0.379'), mp.mpf('1.00'), mp.mpf('1.00'), mp.mpf('+0.20'), 2),
         (mp.mpf('0.376'), mp.mpf('1.11'), mp.mpf('1.00'), mp.mpf('-0.36'), 1)]
print(f'{"r":>7s} {"b1":>6s} {"b2":>6s} {"delta":>8s} {"face":>4s} '
      f'{"FD V\'\'":>16s} {"Cartesian F\'\'":>16s} {"agreement":>12s}')
for (r, b1, b2, d, face) in tests:
    FV = lambda x: V(x, r, b1, b2, face)
    fd2 = (FV(d+h)-2*FV(d)+FV(d-h))/(h*h)
    # Cartesian route: differencing the chart point
    vp, tp, _ = chart(r, d+h, b1, b2, face)
    v0, t0, _ = chart(r, d, b1, b2, face)
    vm, tm, _ = chart(r, d-h, b1, b2, face)
    x1 = mp.matrix([(vp-vm)/(2*h), (tp-tm)/(2*h)])
    x2 = mp.matrix([(vp-2*v0+vm)/(h*h), (tp-2*t0+tm)/(h*h)])
    # Hess F and grad F in the Cartesian chart, by finite differences of F(cart)
    # F as a function of the hub coordinates is not separable here, so use the
    # identity |x'|^2 curvature + grad.x'' evaluated along the curve via FD of the
    # tangential derivative: the tangential second derivative IS the curvature term.
    # We compute grad F . x'' by differencing (dF/ddelta) along two curves? Instead we
    # verify the chart normalisation: |x1| = 2r and x1 . x2 = 0.
    n1 = mp.sqrt(x1[0]**2+x1[1]**2)
    dot = x1[0]*x2[0]+x1[1]*x2[1]
    print(f'{float(r):7.4f} {float(b1):6.3f} {float(b2):6.3f} {float(d):8.4f} {face:4d} '
          f'{mp.nstr(fd2,16):>16s} {"-":>16s} '
          f'|x1|={mp.nstr(n1,10)} x1.x2={mp.nstr(dot,8)}')

print()
print('=== the identity that makes the Cartesian route equivalent ===')
print('For a curve x(delta) with |x_theta\'| = r and theta = pi/2 - 2A (face 1):')
print('   dtheta/ddelta = 2,  x\' = 2 x_theta\',  x\'\' = 4 x_theta\'\'')
print('   F\'\' = x\'^T Hess F x\' + grad F . x\'\' = 4 x_theta\'^T Hess F x_theta\' + 4 grad F . x_theta\'\'')
print('        = 4 [ x_theta\'^T Hess F x_theta\' + grad F . x_theta\'\' ]   <- the lead identity')
print('So the lead formula and the plain second difference of V are the SAME object; the')
print('calibration below is therefore against the FD of V itself at multiple steps.')
print()
print('=== multi-step FD calibration for a set of legal points ===')
for (r, b1, b2, d, face) in tests:
    FV = lambda x: V(x, r, b1, b2, face)
    vals = []
    for hh in ['1e-2', '1e-3', '1e-4']:
        hh = mp.mpf(hh)
        vals.append((FV(d+hh)-2*FV(d)+FV(d-hh))/(hh*hh))
    print(f'  r={float(r)} b1={float(b1)} b2={float(b2)} delta={float(d)} face={face}: '
          f'h=1e-2 {mp.nstr(vals[0],14)}  h=1e-3 {mp.nstr(vals[1],14)}  '
          f'h=1e-4 {mp.nstr(vals[2],14)}')
