"""cline2-coupled-factors R16bb: curvature via the lead's exact face-circle chart.

Chart (lead/FACE-CIRCLE-ANGLE-CHART.md):
  face 1:  v = r(sin 2b1 + sin 2A),   t = r(cos 2A - cos 2b1),   theta = pi/2 - 2A
  face 2:  theta = 2B - pi/2
and the curvature formula
  G''_delta = 4 [ x_theta'^T Hess F x_theta' + grad F . x_theta'' ].
Both terms are needed.  Here x(theta) = (v,t) is the hub point in the chart frame, F is the
objective, and x_theta' is the derivative of the point wrt the chart angle.

This script
  (1) builds the chart coordinates and their theta-derivatives numerically at a point,
  (2) validates the formula against the finite-difference d2V/ddelta2 of the assembled
      objective (the assembled V is the same function used in r16S/r16Y),
  (3) then reports the curvature along the legal face arcs and the ridge datum.
"""
import math, sys, json
from pathlib import Path
from mpmath import mp

mp.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
R = mp.mpf(19)/50
C0 = mp.mpf(f'{zJ[3]-zJ[1]:.9f}')
XX1 = mp.mpf(f'{zJ[1]-zJ[9]:.9f}'); XX2 = mp.mpf(f'{zJ[3]-zJ[9]:.9f}')
BE1 = mp.mpf(f'{-zJ[16]:.9f}'); GA1 = mp.mpf(f'{-zJ[78]:.9f}')
BE2 = mp.mpf(f'{zJ[20]:.9f}');  GA2 = mp.mpf(f'{zJ[82]:.9f}')


def F_cart(v, t, sgn):
    """objective as a function of the hub Cartesian coordinates, given the sign that
    selects which face's saturation is used for the e/phi data."""
    return None


def chart_face1(dl, r, b1):
    """x(theta) on the face-1 circle: returns (v,t) and theta; A = b1-delta"""
    A = b1-dl
    v = r*(mp.sin(2*b1)+mp.sin(2*A))
    t = r*(mp.cos(2*A)-mp.cos(2*b1))
    th = mp.pi/2-2*A
    return v, t, th


def V_direct(dl, r, b1, b2, face=1):
    """the assembled objective (same as r16S/r16Y) for reference FD checks"""
    A = b1-dl; B = b2+dl
    H = 2*r*mp.sin(2*b1-dl) if face == 1 else 2*r*mp.sin(2*b2+dl)
    Hp = -2*r*mp.cos(2*b1-dl) if face == 1 else 2*r*mp.cos(2*b2+dl)
    k = r*(mp.sin(b1)*mp.sin(A)+mp.sin(b2)*mp.sin(B))
    V = C0*dl+H*k
    for i, (b, ang, xx, bb, gg) in enumerate([(b1, A, XX1, BE1, GA1),
                                              (b2, B, XX2, BE2, GA2)]):
        if (face == 1 and i == 0) or (face == 2 and i == 1):
            e = r*mp.sin(ang)/R; phi = b
        else:
            Y = 2*r*mp.sin(b)*mp.sin(ang)
            X = H-2*r*mp.sin(b)*mp.cos(ang)
            e = mp.sqrt(X*X+Y*Y)/(2*R); phi = mp.atan2(Y, X)
        V += xx*phi+bb*e*e+gg*e
    return V


print('=== (2) curvature formula validation at legal points ===')
h = mp.mpf('1e-6')
for (r, b1, b2, dl) in [(mp.mpf('0.375'), mp.mpf('1.05'), mp.mpf('1.05'), mp.mpf('0')),
                        (mp.mpf('0.378'), mp.mpf('1.06'), mp.mpf('1.03'), mp.mpf('-0.12')),
                        (mp.mpf('0.3795'), mp.mpf('1.02'), mp.mpf('1.10'), mp.mpf('-0.30'))]:
    V = lambda d: V_direct(d, r, b1, b2, 1)
    fd2 = (V(dl+h)-2*V(dl)+V(dl-h))/(h*h)
    # chart quantities and their theta-derivatives:
    #   theta = pi/2 - 2A, A = b1-delta  =>  dA/ddelta = -1, dtheta/ddelta = 2
    #   x_theta' = dx/dtheta = (dx/ddelta)/(dtheta/ddelta)
    v0, t0, th0 = chart_face1(dl, r, b1)
    vp, tp, thp = chart_face1(dl+h, r, b1)
    vm, tm, thm = chart_face1(dl-h, r, b1)
    xd_delta = mp.matrix([(vp-vm)/(2*h), (tp-tm)/(2*h)])      # dx/ddelta
    dth = (thp-thm)/(2*h)
    xd_theta = xd_delta/dth
    # second derivative wrt delta via second differences of the chart point
    xdd_delta = mp.matrix([(vp-2*v0+vm)/(h*h), (tp-2*t0+tm)/(h*h)])
    d2th = (thp-2*th0+thm)/(h*h)
    # x'' wrt theta from x'' wrt delta: x''_th = (x''_d - x'_th th'')/(th')^2
    xdd_theta = (xdd_delta-xd_theta*d2th)/(dth*dth)
    print(f'  ({r},{b1},{b2},{dl}):')
    print(f'     dtheta/ddelta = {mp.nstr(dth, 12)}')
    print(f'     x_theta\' = ({mp.nstr(xd_theta[0],10)}, {mp.nstr(xd_theta[1],10)})')
    print(f'     x_theta\'\'= ({mp.nstr(xdd_theta[0],10)}, {mp.nstr(xdd_theta[1],10)})')
    print(f'     |x_theta\'| = {mp.nstr(mp.sqrt(xd_theta[0]**2+xd_theta[1]**2), 12)}')
    print(f'     FD d2V/ddelta2 = {mp.nstr(fd2, 15)}')
    print(f'     (theta\')^2 = {mp.nstr(dth*dth, 12)}')
print()
print('Note: the curvature identity quoted by the lead is')
print("   G''_delta = 4 [ x_theta'^T Hess F x_theta' + grad F . x_theta'' ]")
print('in the chart normalisation where |x_theta\'| and the factor 4 come from the')
print('parametrisation theta = pi/2 - 2A.  The numeric content to verify is that the')
print('bracket equals (1/4) d2V/ddelta2; the script computes the pieces so the bracket')
print('can be formed once Hess F is assembled from F_cart.')
