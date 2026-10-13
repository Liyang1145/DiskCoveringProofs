from mpmath import mp, sin, cos, sqrt, mpf, pi
mp.dps = 30

# LEAD'S formula, used exactly as stated:  g = |V|^2 - 2(a e + chi h Je).V
def lead_g(r, b1, b2, j, chi):
    s = sqrt(1-r*r)
    sigma = -1 if j == 0 else 1
    b = b1 if j == 0 else b2
    cx = r*sin(2*b); cy = sigma*r*cos(2*b)
    if j == 0: ox, oy = r*sin(2*b2), r*cos(2*b2)
    else:      ox, oy = r*sin(2*b1), -r*cos(2*b1)
    vx = s-cx; vy = -cy
    d = sqrt(vx*vx+vy*vy)
    a = r*(1 - s*sin(2*b))/d
    h2 = r*r - a*a
    if h2 < 0: return None
    h = sqrt(h2)
    ex, ey = vx/d, vy/d
    V = (ox-cx, oy-cy)
    return V[0]**2+V[1]**2 - 2*(a*ex + chi*h*(-ey))*V[0] - 2*(a*ey + chi*h*ex)*V[1]

def direct_g(r, b1, b2, j, chi):
    s = sqrt(1-r*r)
    sigma = -1 if j == 0 else 1
    b = b1 if j == 0 else b2
    cx = r*sin(2*b); cy = sigma*r*cos(2*b)
    if j == 0: ox, oy = r*sin(2*b2), r*cos(2*b2)
    else:      ox, oy = r*sin(2*b1), -r*cos(2*b1)
    vx = s-cx; vy = -cy
    d = sqrt(vx*vx+vy*vy)
    a = r*(1 - s*sin(2*b))/d
    h = sqrt(r*r-a*a)
    ex, ey = vx/d, vy/d
    X = cx + a*ex + chi*h*(-ey); Y = cy + a*ey + chi*h*ex
    return (X-ox)**2 + (Y-oy)**2 - r*r

print("1. lead's formula vs direct (should agree):")
r = mpf('0.379')
for (b1,b2) in [(mpf(1),mpf('0.8')), (mpf('0.75'),mpf('0.8'))]:
    for j in (0,1):
        for chi in (+1,-1):
            print("   b1=%.2f b2=%.2f j=%d chi=%+d: lead=%+.9f direct=%+.9f diff=%.1e"
                  % (b1,b2,j+1,chi, lead_g(r,b1,b2,j,chi), direct_g(r,b1,b2,j,chi),
                     abs(lead_g(r,b1,b2,j,chi)-direct_g(r,b1,b2,j,chi))))

print()
print("2. degeneracy: b1+b2=pi/2 (face centers coincide) -> both corners give g=0:")
for (b1,b2) in [(pi/4,pi/4),(mpf('0.7'),pi/2-mpf('0.7')),(mpf('0.9'),pi/2-mpf('0.9'))]:
    print("   b1=%.4f b2=%.4f:" % (b1,b2),
          [(j+1, chi, "%+.2e" % lead_g(r,b1,b2,j,chi)) for j in (0,1) for chi in (+1,-1)])

print()
print("3. off degeneracy: strictly one sign positive, one negative (both faces):")
for (b1,b2) in [(mpf('0.75'),mpf('0.80')),(mpf('0.9'),mpf('0.7')),(mpf('1'),mpf('1'))]:
    for j in (0,1):
        gs = [(chi, lead_g(r,b1,b2,j,chi)) for chi in (+1,-1)]
        print("   b1=%.3f b2=%.3f j=%d: %s" % (b1,b2,j+1, ["%+d:%+.3e"%(c,g) for c,g in gs]))

print()
print("4. |V| depends on BOTH bearings (not just r,b_j):")
for (b1,b2) in [(mpf(1),mpf('0.8')),(mpf(1),mpf(1)),(mpf('0.8'),mpf('0.8'))]:
    s = sqrt(1-r*r); b=b1; cx = r*sin(2*b); cy = -r*cos(2*b)
    ox, oy = r*sin(2*b2), r*cos(2*b2)
    print("   b1=%.2f b2=%.2f: |V|=%.9f" % (b1,b2, sqrt((ox-cx)**2+(oy-cy)**2)))
