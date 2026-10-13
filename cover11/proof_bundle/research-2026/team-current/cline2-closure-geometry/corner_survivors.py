from mpmath import mp, sin, cos, acos, sqrt, mpf, atan2
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

def tests(r, b1, b2, j, chi):
    X, Y = corner(r, b1, b2, j, chi)
    ox, oy = other_center(r, b1, b2, j)
    g = (X-ox)**2 + (Y-oy)**2 - r*r
    p1 = (cos(b1), sin(b1)); p2 = (cos(b2), -sin(b2))
    out = []
    for (p, b) in ((p1, b1), (p2, b2)):
        a = (X-p[0], Y-p[1]); tau = sqrt(a[0]**2+a[1]**2)
        dot = a[0]*p[0] + a[1]*p[1]
        cr = abs(a[0]*p[1] - a[1]*p[0])
        out.append((dot <= 0) and (cr <= tau*sin(b) + mpf('1e-25')))
    return g, out[0], out[1], X, Y

print("per (r,b1,b2): which corners pass BOTH the other-face test and the cone test?")
for rr in [mpf('0.379'), mpf('0.3795'), mpf('0.37999')]:
    blo = acos(rr)/2
    for (b1, b2) in [(mpf(1), mpf(1)), (mpf(1), mpf('0.8')), (mpf('0.8'), mpf(1)),
                     (mpf('0.8'), mpf('0.8')), (mpf('0.65'), mpf('0.65')), (mpf('0.65'), mpf(1))]:
        surv = []
        for j in (0, 1):
            for chi in (+1, -1):
                g, w1, w2, X, Y = tests(rr, b1, b2, j, chi)
                if g <= 0 and w1 and w2:
                    surv.append((j+1, chi, X, Y))
        print("  r=%s b1=%.4f b2=%.4f: %d survivors  %s"
              % (mp.nstr(rr, 7), b1, b2, len(surv),
                 [(j, chi) for j, chi, X, Y in surv]))
