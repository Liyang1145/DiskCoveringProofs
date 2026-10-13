from mpmath import mp, sin, cos, acos, sqrt, pi, mpf, atan, atan2
mp.dps = 30

# Geometry (lead/NORM-FACE-CORNER-CHART.md):
#   r in [.379,.37999]; acos(r)/2 < b_j <= 1 ; s = sqrt(1-r^2)
#   norm disk: center N=(s,0), radius 1-r
#   face j: center C=(r sin2b, sigma r cos2b), radius r, sigma=-1 (j=1), +1 (j=2)
#   V = N - C, d = |V| = sqrt(1 - 2 s r sin2b)
#   a = r(1 - s sin2b)/d ; h = sqrt(r^2 - a^2)
#   X± = C + a e ± h J e,  e = V/d, J(vx,vy)=(-vy,vx)
# wedge (from low_corner_jet.legal):  v sin b1 - t cos b1 > 0  and  t cos b2 + v sin b2 > 0

def corners(r, b, sigma):
    s = sqrt(1-r*r)
    cx = r*sin(2*b); cy = sigma*r*cos(2*b)
    vx = s - cx; vy = -cy
    d = sqrt(1 - 2*s*r*sin(2*b))
    a = r*(1 - s*sin(2*b))/d
    h2 = r*r - a*a
    if h2 < 0: return None
    h = sqrt(h2)
    ex = vx/d; ey = vy/d
    out = []
    for sgn in (+1, -1):
        # X = C + a e + sgn*h*J e,  J e = (-ey, ex)
        X = cx + a*ex + sgn*h*(-ey)
        Y = cy + a*ey + sgn*h*( ex)
        out.append((sgn, X, Y))
    return out, (d, a, h)

def checks(r, b1, b2, b, sigma_j, X, Y, j):
    """return feasibility flags: wedge, other-face, norm(should be 0), own-face(0)"""
    s = sqrt(1-r*r)
    wg1 = X*sin(b1) - Y*cos(b1) > 0
    wg2 = Y*cos(b2) + X*sin(b2) > 0
    # other face
    if j == 0:   # this is face1 (sigma=-1); other is face2 (sigma=+1, bearing b2)
        cx2 = r*sin(2*b2); cy2 = r*cos(2*b2)
    else:
        cx2 = r*sin(2*b1); cy2 = -r*cos(2*b1)
    goth = (X-cx2)**2 + (Y-cy2)**2 - r*r
    # this face residual
    sgj = -1 if j == 0 else 1
    cxj = r*sin(2*b); cyj = sgj*r*cos(2*b)
    grow = (X-cxj)**2 + (Y-cyj)**2 - r*r
    # norm residual
    gn = (X-s)**2 + Y*Y - (1-r)**2
    return (wg1, wg2, goth, grow, gn)

r = mpf('0.379')
print("r =", r, " s =", sqrt(1-r*r), " acos(r)/2 =", acos(r)/2)
print()
for (b1, b2) in [(mpf(1), mpf(1)), (mpf(1), mpf('0.9')), (mpf('0.9'), mpf('0.9'))]:
    print("b1=%.4f b2=%.4f" % (b1, b2))
    for j, (b, sigma) in enumerate([(b1, -1), (b2, +1)]):
        cs = corners(r, b, sigma)
        if cs is None:
            print("   face%d: no real intersection" % (j+1)); continue
        (out, aux) = cs
        print("   face%d (b=%.4f sigma=%2d): d=%.6f a=%.6f h=%.6f" % (j+1, b, sigma, aux[0], aux[1], aux[2]))
        for sgn, X, Y in out:
            ch = checks(r, b1, b2, b, sigma, X, Y, j)
            feas = ch[0] and ch[1] and ch[2] <= 0
            print("      sgn=%+d: X=(%.6f,%.6f)  wedge=%s/%s other=%+.6f own=%+.2e norm=%+.2e  FEASIBLE=%s"
                  % (sgn, X, Y, ch[0], ch[1], ch[2], ch[3], ch[4], feas))
