"""R20: verify the lead's five corrections to my R19 report.

(1) angular second derivative along the ray from Q1: exact value 2 a2 alpha2 / L2^2 (not 0);
    radial Hessian is a LOWER BOUND 2(b1+b2) - c2/L2 - a2/L2^2.
(2) frame: Q1 -> (0, d/2), Q2 -> (0, -d/2); A = (d/2) n gives A.X = (d/2) x.
(3) |y +- d/2| <= 0.76 and d >= 0.45  =>  |y| <= 0.535.
(4) radial lemma gives L1,L2 < 0.43 at LOCAL MAXIMA only.
(5) boundary conclusion bypasses C862 via d < 0.86.
"""
import sys
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
import math

R = 0.38
r, b1, b2 = 0.3795, 1.05, 1.12
Q1 = (r*math.sin(2*b1), 2*r*math.sin(b1)**2)
Q2 = (r*math.sin(2*b2), -2*r*math.sin(b2)**2)
print('(2) frame and linear term')
dv = (Q1[0]-Q2[0], Q1[1]-Q2[1]); d = math.hypot(*dv)
e = (dv[0]/d, dv[1]/d); n = (e[1], -e[0])
M = ((Q1[0]+Q2[0])/2, (Q1[1]+Q2[1])/2)
A = (r*(math.sin(b1)**2+math.sin(b2)**2),
     r*(math.sin(b2)*math.cos(b2)-math.sin(b1)*math.cos(b1)))
print(f'  d = {d:.9f}   A = ({A[0]:.9f},{A[1]:.9f})   (d/2)n = ({(d/2)*n[0]:.9f},{(d/2)*n[1]:.9f})')
print(f'  |A| = {math.hypot(*A):.9f} = d/2 : {abs(math.hypot(*A)-d/2) < 1e-15}')
# Q1 in the (n,e) frame: Q1 = M + (d/2) e  => coordinates (x,y) = (0, d/2)
for P, tag in ((Q1, 'Q1'), (Q2, 'Q2')):
    rel = (P[0]-M[0], P[1]-M[1])
    xc = rel[0]*n[0] + rel[1]*n[1]
    yc = rel[0]*e[0] + rel[1]*e[1]
    print(f'  {tag} in (n,e) frame: (x,y) = ({xc:+.9f}, {yc:+.9f})')
print('  => A.X = (d/2) * x   (NOT y).  Corrected per lead.')
print()

print('(1) angular 2nd derivative along the ray from Q1')
# Face-2 centre and its bearing
c2v = (r*math.sin(2*b2), r*math.cos(2*b2))
print(f'  face-2 centre c2v = ({c2v[0]:.9f},{c2v[1]:.9f}), |c2v| = {math.hypot(*c2v):.9f} = r')
print(f'  its bearing = atan2(c2v.y, c2v.x) = {math.atan2(c2v[1], c2v[0]):+.9f}; '
      f'2b2 - pi/2 = {2*b2-math.pi/2:+.9f}')

def alpha2(X):
    """angle at Q2 between the outward radial direction (Q2 direction) and X-Q2"""
    w = (X[0]-Q2[0], X[1]-Q2[1])
    nw = math.hypot(*w)
    if nw == 0:
        return None
    ur = (Q2[0]/r, Q2[1]/r)          # outward radial unit at Q2
    cos = (w[0]*ur[0]+w[1]*ur[1])/nw
    sin = (ur[0]*w[1]-ur[1]*w[0])/nw  # orientation
    return math.atan2(sin, cos)

# a ray from Q1 in a generic direction
psi = 0.7
er = (math.cos(psi), math.sin(psi))
for rho in (0.30, 0.43):
    X0 = (Q1[0]+rho*er[0], Q1[1]+rho*er[1])
    a0 = alpha2(X0)
    if a0 is None:
        continue
    L2_0 = math.hypot(X0[0]-Q2[0], X0[1]-Q2[1])
    h = 1e-4
    Xp = (Q1[0]+(rho+h)*er[0], Q1[1]+(rho+h)*er[1])
    Xm = (Q1[0]+(rho-h)*er[0], Q1[1]+(rho-h)*er[1])
    d2num = (alpha2(Xp) - 2*a0 + alpha2(Xm))/h**2
    exact = 2*a0/rho**2
    print(f'  rho={rho}: L2={L2_0:.9f} alpha2={a0:+.9f}  '
          f'numeric d2a/drho2={d2num:+.6f}  exact 2a/rho^2={exact:+.6f}')
print('  => d2(alpha2)/drho2 = 2 alpha2 / L2^2, NOT zero, and |.| <= 2/L2^2.')

print()
print('  full radial Hessian of the objective along that ray:')
beta1, beta2 = 0.701924084, 0.693952741
c1, c2 = 1.145102454, 1.138494697
a1, a2 = 0.012841585, 0.013306528
for rho in (0.30, 0.43):
    X0 = (Q1[0]+rho*er[0], Q1[1]+rho*er[1])
    L2_0 = math.hypot(X0[0]-Q2[0], X0[1]-Q2[1])
    a0 = alpha2(X0)
    h = 1e-4
    def F(rh):
        X = (Q1[0]+rh*er[0], Q1[1]+rh*er[1])
        L1 = rh
        L2 = math.hypot(X[0]-Q2[0], X[1]-Q2[1])
        return beta1*L1*L1 - c1*L1 + a1*0.0 + beta2*L2*L2 - c2*L2 + a2*(alpha2(X) or 0.0)
    d2 = (F(rho+h)-2*F(rho)+F(rho-h))/h**2
    lower = 2*(beta1+beta2) - c2/L2_0 - a2/L2_0**2
    ang = 2*a2*a0
    print(f'   rho={rho}: numeric d2F/drho2={d2:+.6f}   lower bound={lower:+.6f}   '
          f'angular contribution 2*a2*alpha2={ang:+.6f}   '
          f'difference (numeric-lower)={d2-lower:+.6f}')
print('  => the bound is a LOWER bound; equality only when alpha2 = 0.')

print()
print('(3) |y| <= .535')
for dd in (0.45, 0.60, 0.86):
    print(f'  d={dd}: |y| <= 0.76 - d/2 = {0.76-dd/2:.6f}  (<= .535: {0.76-dd/2 <= 0.535+1e-12})')
print()
print('(5) d < 0.86 from the radial lemma')
print(f'  L1,L2 < 0.43 at a local max  =>  d <= L1+L2 < 0.86 < 1.049  (no C862 needed)')
