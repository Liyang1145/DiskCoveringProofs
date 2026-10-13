from mpmath import mp, sin, cos, acos, sqrt, mpf, pi, atan2
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

# wedge constraints (geometric form): at p1 = (cos b1, sin b1) with outward normal e1 = p1,
#   cone condition  psi_1 <= b1  <=>  (X - p1) x e1 >= -|X-p1| sin b1
#   <=> N1 . X + m1 >= 0,  N1 = (-sin b1, cos b1),  m1 = sin b1*(cos b1 + cos b1?) ... compute exactly
def wedge_ok(r, b1, b2, X, Y):
    p1 = (cos(b1), sin(b1)); p2 = (cos(b2), -sin(b2))
    e1 = p1; e2 = p2
    # constraint at p1: cross(X-p1, e1) >= -|X-p1| sin b1
    def cross(a, b): return a[0]*b[1] - a[1]*b[0]
    def dot(a, b): return a[0]*b[0] + a[1]*b[1]
    W1 = (X-p1[0], Y-p1[1]); W2 = (X-p2[0], Y-p2[1])
    c1 = cross(W1, e1) + sqrt(dot(W1, W1))*sin(b1)
    c2 = cross(W2, e2) - sqrt(dot(W2, W2))*sin(b2)   # sign for the mirror
    return c1, c2

print("admitted corner:", "face1 chi=-1, face2 chi=+1")
n = 0; okf = 0; okw = 0; worst = None; bestobj = None
for rr in [mpf('0.379'), mpf('0.3795'), mpf('0.37999')]:
    blo = acos(rr)/2
    B = [blo+mpf('0.0005'), mpf('0.65'), mpf('0.8'), mpf('0.9'), mpf(1)]
    for b1 in B:
        for b2 in B:
            for j in (0, 1):
                chi = -1 if j == 0 else +1
                X, Y = corner(rr, b1, b2, j, chi)
                ox, oy = other_center(rr, b1, b2, j)
                g = (X-ox)**2 + (Y-oy)**2 - rr*rr
                w1, w2 = wedge_ok(rr, b1, b2, X, Y)
                n += 1
                if g <= 0: okf += 1
                if w1 >= 0 and w2 >= 0: okw += 1
                if worst is None or min(w1, w2) < worst[0]: worst = (min(w1, w2), rr, b1, b2, j)
print("  other-face admitted:", okf, "/", n)
print("  wedge admitted    :", okw, "/", n, " tightest margin %.3e at r=%s b1=%.3f b2=%.3f j=%d"
      % (worst[0], mp.nstr(worst[1], 7), worst[2], worst[3], worst[4]))
print()
print("scan: for each (r,b1,b2), which of the 4 corners (2 faces x 2 signs) pass BOTH tests?")
for rr in [mpf('0.379'), mpf('0.37999')]:
    for (b1, b2) in [(mpf(1), mpf(1)), (mpf('0.7'), mpf(1)), (mpf('0.65'), mpf('0.65'))]:
        survivors = []
        for j in (0, 1):
            for chi in (+1, -1):
                X, Y = corner(rr, b1, b2, j, chi)
                ox, oy = other_center(rr, b1, b2, j)
                g = (X-ox)**2 + (Y-oy)**2 - rr*rr
                w1, w2 = wedge_ok(rr, b1, b2, X, Y)
                if g <= 0 and w1 >= 0 and w2 >= 0:
                    survivors.append((j, chi, X, Y))
        print("  r=%s b1=%.3f b2=%.3f: %d survivors %s"
              % (mp.nstr(rr, 7), b1, b2, len(survivors),
                 [(j, chi) for j, chi, X, Y in survivors]))
