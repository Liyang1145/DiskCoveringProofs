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

def gother(r, b1, b2, j, chi):
    X, Y = corner(r, b1, b2, j, chi)
    if j == 0: ox, oy = r*sin(2*b2), r*cos(2*b2)
    else:      ox, oy = r*sin(2*b1), -r*cos(2*b1)
    return (X-ox)**2 + (Y-oy)**2 - r*r

print("1. face centers coincide iff b1+b2 = pi/2:")
for (b1,b2) in [(pi/4,pi/4),(mpf('0.7'),pi/2-mpf('0.7')),(mpf('0.6'),pi/2-mpf('0.6')),(mpf('0.8'),mpf('0.8'))]:
    d = abs(r*sin(2*b1)-r*sin(2*b2)) + abs(-r*cos(2*b1)-r*cos(2*b2)) if False else None
    c1 = (r := mpf('0.379')) and (r*sin(2*b1), -r*cos(2*b1)); c2 = (r*sin(2*b2), r*cos(2*b2))
    gap = sqrt((c1[0]-c2[0])**2 + (c1[1]-c2[1])**2)
    print("   b1=%.4f b2=%.4f sum=%.6f : |C1-C2|=%.3e" % (b1,b2,b1+b2,gap))

print()
print("2. at b1+b2=pi/2 both corners have g=0 (verified); off it, strictly one sign each:")
for (b1,b2) in [(pi/4,pi/4),(mpf('0.75'),mpf('0.80')),(mpf('0.9'),mpf('0.7'))]:
    row = []
    for j in (0,1):
        gs = [gother(mpf('0.379'), b1, b2, j, chi) for chi in (+1,-1)]
        row.append((j+1, gs))
    print("   b1=%.3f b2=%.3f:" % (b1,b2), [(j, ["%+.2e"%g for g in gs]) for j,gs in row])

print()
print("3. my reported formula test: g = |V|^2 + r^2 - 2a*chi*B - 2*chi*Cdot vs exact |X-C_o|^2-r^2")
r = mpf('0.379'); b1 = mpf(1); b2 = mpf('0.8')
for j in (0,1):
    sigma = -1 if j==0 else 1
    b = b1 if j==0 else b2
    s, cx, cy, d, a, h, ex, ey = build(r, b, sigma)
    if j == 0: ox, oy = r*sin(2*b2), r*cos(2*b2)
    else:      ox, oy = r*sin(2*b1), -r*cos(2*b1)
    V = (ox-cx, oy-cy)
    for chi in (+1,-1):
        X, Y = corner(r, b1, b2, j, chi)
        gtrue = (X-ox)**2 + (Y-oy)**2 - r*r
        B = (-ey)*V[1] - ex*V[0]; Cdot = (-ey)*V[0] + ex*V[1]
        mine = V[0]**2+V[1]**2 + r*r - 2*a*chi*B - 2*chi*Cdot
        good = V[0]**2+V[1]**2 + r*r + 2*a*(V[0]*ex+V[1]*ey) + 2*chi*h*(V[0]*(-ey)+V[1]*ex)
        print("   j=%d chi=%+d: true=%.9f  mine=%.9f  corrected=%.9f" % (j+1, chi, gtrue, mine, good))
