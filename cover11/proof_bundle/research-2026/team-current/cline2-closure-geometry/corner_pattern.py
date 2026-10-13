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
    return [(sg, cx + a*ex + sg*h*(-ey), cy + a*ey + sg*h*ex) for sg in (+1, -1)]

def gother(r, b1, b2, j, sgn):
    b = b1 if j == 0 else b2
    sigma = -1 if j == 0 else 1
    cs = corners(r, b, sigma)
    if cs is None: return None
    X, Y = [(x, y) for sg, x, y in cs if sg == sgn][0]
    if j == 0:
        cx2, cy2 = r*sin(2*b2), r*cos(2*b2)
    else:
        cx2, cy2 = r*sin(2*b1), -r*cos(2*b1)
    return (X-cx2)**2 + (Y-cy2)**2 - r*r

r = mpf('0.379')
print("table: g_other for the two corners; x = excluded (g_other>0)")
print("j, b_j, b_other -> sgn=+1 , sgn=-1")
bad = 0; n = 0
for (b1, b2) in [(mpf(1), mpf(1)), (mpf(1), mpf('0.9')), (mpf('0.9'), mpf(1)),
                 (mpf('0.9'), mpf('0.9')), (mpf('0.7'), mpf(1)), (mpf('1'), mpf('0.7')),
                 (mpf('0.65'), mpf('0.95'))]:
    for j in (0, 1):
        bj = b1 if j == 0 else b2
        bo = b2 if j == 0 else b1
        g1 = gother(r, b1, b2, j, +1); g2 = gother(r, b1, b2, j, -1)
        def tag(g): return "EXCL" if g > 0 else "in  "
        print("  j=%d b=%.3f bo=%.3f: sgn=+1 %s (%+.6f)   sgn=-1 %s (%+.6f)" %
              (j+1, bj, bo, tag(g1), g1, tag(g2), g2))
        # hypothesis: sgn=+1 always excluded, sgn=-1 always in
        n += 1
        if not (g1 > 0 and g2 <= 0):
            bad += 1
            print("     ^^ hypothesis FAILS here")
print("hypothesis sgn=+1 excluded / sgn=-1 admitted:", n-bad, "/", n)
print()
print("check at r = .37999:")
r = mpf('0.37999')
bad = 0; n = 0
for b1 in [mpf('0.61'), mpf('0.7'), mpf('0.85'), mpf(1)]:
    for b2 in [mpf('0.61'), mpf('0.7'), mpf('0.85'), mpf(1)]:
        for j in (0, 1):
            g1 = gother(r, b1, b2, j, +1); g2 = gother(r, b1, b2, j, -1)
            n += 1
            if not (g1 > 0 and g2 <= 0): bad += 1
print("  ", n-bad, "/", n)
print()
print("wedge check: do both corners satisfy the wedge on the whole domain?")
def wedge(cs, b1, b2):
    out = []
    for sg, X, Y in cs:
        out.append((X*sin(b1) - Y*cos(b1) > 0, Y*cos(b2) + X*sin(b2) > 0))
    return out
bad = 0; n = 0
for r in [mpf('0.379'), mpf('0.37999')]:
    blo = acos(r)/2
    for b1 in [blo+mpf('0.001'), mpf('0.7'), mpf('0.9'), mpf(1)]:
        for b2 in [blo+mpf('0.001'), mpf('0.7'), mpf('0.9'), mpf(1)]:
            for j, sigma in ((0, -1), (1, 1)):
                b = b1 if j == 0 else b2
                cs = corners(r, b, sigma)
                if cs is None: continue
                w = wedge(cs, b1, b2)
                for k, ww in enumerate(w):
                    n += 1
                    if not (ww[0] and ww[1]): bad += 1
print("  wedge satisfied for both corners:", n-bad, "/", n)
