from mpmath import mp, sin, cos, acos, sqrt, pi, mpf, atan2
mp.dps = 25

def corners(r, b, sigma):
    s = sqrt(1-r*r)
    cx = r*sin(2*b); cy = sigma*r*cos(2*b)
    vx = s - cx; vy = -cy
    d = sqrt(1 - 2*s*r*sin(2*b))
    a = r*(1 - s*sin(2*b))/d
    h2 = r*r - a*a
    if h2 < 0: return None
    h = sqrt(h2); ex = vx/d; ey = vy/d
    return [(sg, cx + a*ex + sg*h*(-ey), cy + a*ey + sg*h*ex) for sg in (+1, -1)], (d, a, h, ex, ey)

def status(r, b1, b2, j, sgn):
    b = b1 if j == 0 else b2
    sigma = -1 if j == 0 else 1
    res = corners(r, b, sigma)
    if res is None: return None
    cs, aux = res
    X, Y = [(x, y) for sg, x, y in cs if sg == sgn][0]
    s = sqrt(1-r*r)
    w1 = X*sin(b1) - Y*cos(b1)
    w2 = Y*cos(b2) + X*sin(b2)
    if j == 0:
        c2x, c2y = r*sin(2*b2), r*cos(2*b2)
    else:
        c2x, c2y = r*sin(2*b1), -r*cos(2*b1)
    goth = (X-c2x)**2 + (Y-c2y)**2 - r*r
    return w1, w2, goth, X, Y, aux

r = mpf('0.379')
print("per corner: wedge1, wedge2, g_other  (>0 = satisfied / excluded)")
for (b1, b2) in [(mpf(1), mpf(1)), (mpf(1), mpf('0.9')), (mpf('0.9'), mpf('1')), (mpf('0.7'), mpf('1'))]:
    print("b1=%.3f b2=%.3f" % (b1, b2))
    for j in (0, 1):
        for sgn in (+1, -1):
            st = status(r, b1, b2, j, sgn)
            if st is None: continue
            w1, w2, goth, X, Y, aux = st
            print("   j=%d sgn=%+d: w1=%+.6f w2=%+.6f g_oth=%+.6f  X=(%.5f,%.5f)"
                  % (j+1, sgn, w1, w2, goth, X, Y))
print()
print("(a/d) table:  a2 = a,  J e x D = -2 r h sin b_o (sin b_j + sigma sin b_o)/d")
for (b1, b2) in [(mpf(1), mpf(1)), (mpf(1), mpf('0.9')), (mpf('0.9'), mpf('1'))]:
    for j, sigma in ((0, -1), (1, 1)):
        b = b1 if j == 0 else b2; bo = b2 if j == 0 else b1
        res = corners(r, b, sigma)
        if res is None: continue
        cs, (d, a, h, ex, ey) = res
        JeD = -2*r*h*sin(bo)*(sin(b)+sigma*sin(bo))/d
        # verify numerically: Je = (-ey, ex); D = C_other - C
        cx = r*sin(2*b); cy = sigma*r*cos(2*b)
        if j == 0: c2x, c2y = r*sin(2*b2), r*cos(2*b2)
        else: c2x, c2y = r*sin(2*b1), -r*cos(2*b1)
        Je = (-ey, ex); D = (c2x-cx, c2y-cy)
        JeDn = Je[0]*D[1] - Je[1]*D[0]
        print("   j=%d b=%.3f bo=%.3f: Je.D=%.9f  formula=%.9f  a/d=%.6f  prediction: +1 admitted iff Je.D>a"
              % (j+1, b, bo, JeDn, JeD, a/d))
