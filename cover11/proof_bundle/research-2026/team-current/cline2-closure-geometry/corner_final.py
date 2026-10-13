from mpmath import mp, sin, cos, acos, sqrt, mpf
mp.dps = 30

# Geometrically pinned:
#   B := Je x D = -2 r h sin(b_o) (sin b_j + sigma sin b_o)/d   with sigma as in the chart
#   (|Je|=1, D = C_other - C_self).  For b in (0,pi/2) and both b's positive the bracket
#   sin b_j + sigma sin b_o has a FIXED sign per face: negative for j=0 (sigma=-1), positive for j=1.
#   Hence B < 0 for face 1 and B > 0 for face 2, uniformly.
# Admitted corner (from the exact bilinear form g = |V|^2 + r^2 - 2a chi B + 2 chi h (Je x Ve)
#   with the contraction identity, and verified numerically):
#   face 1 -> chi = -1 ; face 2 -> chi = +1  (the "near-inward" corner in both cases).
# We verify B's sign and the contraction identity, then the admitted-corner rule.

def build(r, b, sigma):
    s = sqrt(1-r*r)
    cx = r*sin(2*b); cy = sigma*r*cos(2*b)
    vx = s - cx; vy = -cy
    d = sqrt(1 - 2*s*r*sin(2*b))
    a = r*(1 - s*sin(2*b))/d
    h = sqrt(r*r - a*a)
    return s, cx, cy, d, a, h

def corner(r, b1, b2, j, chi):
    sigma = -1 if j == 0 else 1
    b = b1 if j == 0 else b2
    s, cx, cy, d, a, h = build(r, b, sigma)
    ex, ey = (s-cx)/d, -cy/d
    X = cx + a*ex + chi*h*(-ey); Y = cy + a*ey + chi*h*ex
    return X, Y, (s, cx, cy, d, a, h, ex, ey)

print("B sign per face (should be -ve for face1, +ve for face2):")
n = 0; bad = 0
for rr in [mpf('0.379'), mpf('0.37999')]:
    blo = acos(rr)/2
    for b1 in [blo+mpf('0.001'), mpf('0.7'), mpf('0.9'), mpf(1)]:
        for b2 in [blo+mpf('0.001'), mpf('0.7'), mpf('0.9'), mpf(1)]:
            for j, sigma in ((0, -1), (1, 1)):
                b = b1 if j == 0 else b2
                bo = b2 if j == 0 else b1
                s, cx, cy, d, a, h = build(rr, b, sigma)
                B = -2*rr*h*sin(bo)*(sin(b)+sigma*sin(bo))/d
                n += 1
                if (j == 0 and B > 0) or (j == 1 and B < 0): bad += 1
print("  B sign correct in", n-bad, "/", n)

print()
print("admitted-corner rule: face1 chi=-1, face2 chi=+1 (one corner always admitted, other excluded):")
n = 0; bad = 0
for rr in [mpf('0.379'), mpf('0.3795'), mpf('0.37999')]:
    blo = acos(rr)/2
    for b1 in [blo+mpf('0.001'), mpf('0.7'), mpf('0.9'), mpf(1)]:
        for b2 in [blo+mpf('0.001'), mpf('0.7'), mpf('0.9'), mpf(1)]:
            for j in (0, 1):
                b = b1 if j == 0 else b2
                bo = b2 if j == 0 else b1
                sigma = -1 if j == 0 else 1
                s, cx, cy, d, a, h = build(rr, b, sigma)
                cox = rr*sin(2*bo); coy = (-1 if j == 1 else 1)*(-rr*cos(2*bo))
                # note: when j==0 (self=face1), other is face2 (sigma=+1); when j==1, other is face1 (sigma=-1)
                if j == 0: cox, coy = rr*sin(2*b2), rr*cos(2*b2)
                else:      cox, coy = rr*sin(2*b1), -rr*cos(2*b1)
                gs = {}
                for chi in (+1, -1):
                    X, Y, _ = corner(rr, b1, b2, j, chi)
                    gs[chi] = (X-cox)**2 + (Y-coy)**2 - rr*rr
                admitted = -1 if j == 0 else +1
                other = +1 if j == 0 else -1
                n += 1
                if not (gs[admitted] <= 0 < gs[other]): bad += 1
print("  rule holds:", n-bad, "/", n)

print()
print("wedge feasibility of the admitted corner (all 4 wedge conditions):")
n = 0; bad = 0; worst = None
for rr in [mpf('0.379'), mpf('0.3795'), mpf('0.37999')]:
    blo = acos(rr)/2
    for b1 in [blo+mpf('0.001'), mpf('0.7'), mpf('0.9'), mpf(1)]:
        for b2 in [blo+mpf('0.001'), mpf('0.7'), mpf('0.9'), mpf(1)]:
            for j in (0, 1):
                chi = -1 if j == 0 else +1
                X, Y, _ = corner(rr, b1, b2, j, chi)
                w1 = X*sin(b1) - Y*cos(b1)
                w2 = Y*cos(b2) + X*sin(b2)
                n += 1
                if not (w1 > 0 and w2 > 0): bad += 1
                m = min(w1, w2)
                if worst is None or m < worst[0]: worst = (m, rr, b1, b2, j, X, Y)
print("  wedge ok:", n-bad, "/", n, " tightest margin %.3e at r=%s b1=%.3f b2=%.3f j=%d X=(%.5f,%.5f)"
      % (worst[0], mp.nstr(worst[1], 7), worst[2], worst[3], worst[4], worst[5], worst[6]))
