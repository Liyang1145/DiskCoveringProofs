from mpmath import mp, sin, cos, acos, sqrt, pi, mpf
mp.dps = 30

def build(r, b, sigma):
    s = sqrt(1-r*r)
    cx = r*sin(2*b); cy = sigma*r*cos(2*b)
    vx = s - cx; vy = -cy
    d = sqrt(1 - 2*s*r*sin(2*b))
    a = r*(1 - s*sin(2*b))/d
    h = sqrt(r*r - a*a)
    return s, cx, cy, vx, vy, d, a, h

def gother(r, b1, b2, j, sgn):
    b = b1 if j == 0 else b2
    sigma = -1 if j == 0 else 1
    s, cx, cy, vx, vy, d, a, h = build(r, b, sigma)
    ex, ey = vx/d, vy/d
    X = cx + a*ex + sgn*h*(-ey); Y = cy + a*ey + sgn*h*(ex)
    if j == 0: c2x, c2y = r*sin(2*b2), r*cos(2*b2)
    else:      c2x, c2y = r*sin(2*b1), -r*cos(2*b1)
    return (X-c2x)**2 + (Y-c2y)**2 - r*r

print("test A: |Je.D| <= a on the domain?")
bad = 0; n = 0; mm = None
for rr in [mpf('0.379'), mpf('0.3795'), mpf('0.37999')]:
    blo = acos(rr)/2
    B = [blo+mpf('0.0005'), mpf('0.65'), mpf('0.8'), mpf('0.9'), mpf('0.95'), mpf(1)]
    for b1 in B:
        for b2 in B:
            for j, sigma in ((0, -1), (1, 1)):
                b = b1 if j == 0 else b2
                bo = b2 if j == 0 else b1
                s, cx, cy, vx, vy, d, a, h = build(rr, b, sigma)
                JeD = -2*rr*h*sin(bo)*(sin(b)+sigma*sin(bo))/d
                margin = a - abs(JeD)
                n += 1
                if mm is None or margin < mm[0]: mm = (margin, rr, b1, b2, j)
                if margin < 0: bad += 1
print("   holds:", n-bad, "/", n, " min margin %.3e at r=%s b1=%.3f b2=%.3f j=%d"
      % (mm[0], mp.nstr(mm[1], 7), mm[2], mm[3], mm[4]))

print()
print("test B: admitted sign rule  chi = -1  iff  Je.D < 0")
n = 0; bad = 0; deg = 0
for rr in [mpf('0.379'), mpf('0.37999')]:
    blo = acos(rr)/2
    B = [blo+mpf('0.0005'), mpf('0.65'), mpf('0.8'), mpf('0.9'), mpf(1)]
    for b1 in B:
        for b2 in B:
            for j, sigma in ((0, -1), (1, 1)):
                b = b1 if j == 0 else b2
                bo = b2 if j == 0 else b1
                s, cx, cy, vx, vy, d, a, h = build(rr, b, sigma)
                JeD = -2*rr*h*sin(bo)*(sin(b)+sigma*sin(bo))/d
                g1 = gother(rr, b1, b2, j, +1); g2 = gother(rr, b1, b2, j, -1)
                if abs(JeD) < mpf('1e-25'):
                    deg += 1
                    ok = (g2 <= g1 + mpf('1e-20'))
                elif JeD < 0:
                    ok = (g2 <= 0 <= g1)
                else:
                    ok = (g1 <= 0 <= g2)
                n += 1
                if not ok:
                    bad += 1
                    print("   FAIL r=%s b=%.3f bo=%.3f j=%d: JeD=%.3e g+=%.6f g-=%.6f"
                          % (mp.nstr(rr, 7), b, bo, j+1, JeD, g1, g2))
print("   rule holds:", n-bad, "/", n, " (JeD=0 cases:", deg, ")")
