from mpmath import mp, sin, cos, acos, sqrt, pi, mpf
mp.dps = 30

# EXACT RULE (derived):
#  a2 = a^2 - (Je x D)^2, with Je x D = -2rho h sin(b_o)(sin b_j + sigma sin b_o)/d
#  g_other(X_chi) = a2 - 2 a chi (Je x D)
#  => the admitted corner is  chi = -1  iff  Je x D < 0   [i.e. sin b_j > sin b_o]
#     (when Je x D = 0 both give a2 >= 0; the numerically observed admission is chi=-1)
#  Independently: a2 = r^2(1-s sin b_j)^2 (1 - s sin b_o)^2/(d^2 h^2) ... let's VERIFY

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

print("test A: is a2 = a^2 - (Je.D)^2 >= 0, i.e. |Je.D| <= a, on the whole domain?")
bad = 0; n = 0; minmargin = None
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
                if minmargin is None or margin < minmargin: minmargin = (margin, rr, b1, b2, j)
                if margin < 0: bad += 1
print("   |Je.D| <= a :", n-bad, "/", n, " min margin %.3e at r=%s b1=%.3f b2=%.3f j=%d" % (minmargin[0], mpn := mp.nstr(minmargin[1],7), minmargin[2], minmargin[3], minmargin[4]))

print()
print("test B: the admitted sign rule  chi = -1 iff Je.D < 0")
n = 0; bad = 0; degenerate = 0
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
                    degenerate += 1
                    ok = (g2 <= g1 + mpf('1e-20'))
                else:
                    ok = (g2 <= 0 <= g1) if JeD < 0 else (g1 <= 0 <= g2)
                n += 1
                if not ok:
                    bad += 1
                    print("   FAIL r=%s b=%.3f bo=%.3f j=%d: JeD=%.3e g+=%.6f g-=%.6f"
                          % (mp.nstr(rr,7), b, bo, j+1, JeD, g1, g2))
print("   rule holds:", n-bad, "/", n, "  (degenerate JeD=0 cases:", degenerate, ")")
