from mpmath import mp, sin, cos, acos, sqrt, mpf, pi
mp.dps = 30

def build(r, b, sigma):
    s = sqrt(1-r*r)
    cx = r*sin(2*b); cy = sigma*r*cos(2*b)
    vx = s - cx; vy = -cy
    d = sqrt(1 - 2*s*r*sin(2*b))
    a = r*(1 - s*sin(2*b))/d
    h = sqrt(r*r - a*a)
    return s, cx, cy, d, a, h, vx/d, vy/d

def corner(r, b1, b2, j, chi):
    sigma = -1 if j == 0 else 1
    b = b1 if j == 0 else b2
    s, cx, cy, d, a, h, ex, ey = build(r, b, sigma)
    return cx + a*ex + chi*h*(-ey), cy + a*ey + chi*h*ex

def other_center(r, b1, b2, j):
    if j == 0: return r*sin(2*b2), r*cos(2*b2)
    return r*sin(2*b1), -r*cos(2*b1)

r = mpf('0.379')
print("=== the lead's counterexample: b1+b2 = pi/2, b1=b2=pi/4 ===")
b1 = b2 = pi/4
print("  C1 =", [mp.nstr(x,12) for x in (r*sin(2*b1), -r*cos(2*b1))])
print("  C2 =", [mp.nstr(x,12) for x in (r*sin(2*b2),  r*cos(2*b2))])
print("  centers coincide:", abs(r*sin(2*b1)-r*sin(2*b2)) < mpf('1e-25'),
      abs(-r*cos(2*b1)-r*cos(2*b2)) < mpf('1e-25'))
print()
for j in (0,1):
    for chi in (+1,-1):
        X, Y = corner(r, b1, b2, j, chi)
        ox, oy = other_center(r, b1, b2, j)
        g = (X-ox)**2 + (Y-oy)**2 - r*r
        print("  j=%d chi=%+d: X=(%.9f,%.9f)  g_other=%+.3e" % (j+1, chi, X, Y, g))
print()
print("  so BOTH corners have g=0 at this point -> 'exactly one excluded' is FALSE")
print()
print("=== my formula vs the truth ===")
print("  I had:  g = |V|^2 + r^2 - 2a*chi*B - 2*chi*Cdot")
print("  actual: g = |V|^2 + r^2 + 2a*(V.e) + 2*chi*h*(V.Je)   [expand |X-C_o|^2]")
print("  => the a-term is NOT multiplied by chi; and |V| depends on BOTH bearings")
print()
print("check the corrected expansion numerically at a generic point:")
r2 = mpf('0.379'); bb1 = mpf(1); bb2 = mpf('0.8')
for j in (0,1):
    sigma = -1 if j==0 else 1
    b = bb1 if j==0 else bb2
    s, cx, cy, d, a, h, ex, ey = build(r2, b, sigma)
    ox, oy = other_center(r2, bb1, bb2, j)
    V = (ox-cx, oy-cy)
    for chi in (+1,-1):
        X = cx + a*ex + chi*h*(-ey); Y = cy + a*ey + chi*h*(ex)
        gtrue = (X-ox)**2 + (Y-oy)**2 - r2*r2
        gform = V[0]**2+V[1]**2 + r2*r2 + 2*a*(V[0]*ex+V[1]*ey) + 2*chi*h*(V[0]*(-ey)+V[1]*ex)
        print("   j=%d chi=%+d: g_true=%.12f  g_form=%.12f  diff=%.1e" % (j+1, chi, gtrue, gform, gtrue-gform))
