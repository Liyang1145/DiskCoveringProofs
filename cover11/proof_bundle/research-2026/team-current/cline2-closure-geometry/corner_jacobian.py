from mpmath import mp, sin, cos, acos, sqrt, mpf, atan2, pi
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

def admissible(r, b1, b2, j, chi):
    X, Y = corner(r, b1, b2, j, chi)
    ox, oy = other_center(r, b1, b2, j)
    if (X-ox)**2 + (Y-oy)**2 - r*r > mpf('1e-25'): return False
    for (p, b) in (((cos(b1), sin(b1)), b1), ((cos(b2), -sin(b2)), b2)):
        a = (X-p[0], Y-p[1]); tau = sqrt(a[0]**2+a[1]**2)
        if a[0]*p[0]+a[1]*p[1] > mpf('1e-25'): return False
        if abs(a[0]*p[1]-a[1]*p[0]) > tau*sin(b) + mpf('1e-25'): return False
    return True

# exact Jacobian condition: dg/dchi = -2 a B - 2 h Cdot, with B = Je x V, Cdot = <Je_perp, V>
def jacobian(r, b1, b2, j):
    sigma = -1 if j == 0 else 1
    b = b1 if j == 0 else b2
    s, cx, cy, d, a, h, ex, ey = build(r, b, sigma)
    ox, oy = other_center(r, b1, b2, j)
    V = (ox-cx, oy-cy)
    Je = (-ey, ex)
    B = Je[0]*V[1] - Je[1]*V[0]
    Cdot = Je[0]*V[0] + Je[1]*V[1]
    return -2*a*B - 2*h*Cdot, B, Cdot, V

print("exact exclusion rule: the excluded sign is the one with dg/dchi > 0; check against admissibility")
n = 0; ok = 0; deg = 0
for rr in [mpf('0.379'), mpf('0.37999')]:
    blo = acos(rr)/2
    for b1 in [blo+mpf('0.001'), mpf('0.65'), mpf('0.8'), mpf(1)]:
        for b2 in [blo+mpf('0.001'), mpf('0.65'), mpf('0.8'), mpf(1)]:
            for j in (0, 1):
                adm = {chi: admissible(rr, b1, b2, j, chi) for chi in (+1, -1)}
                jac, B, Cdot, V = jacobian(rr, b1, b2, j)
                n += 1
                if adm[+1] and adm[-1]:
                    deg += 1
                else:
                    exp = -1 if (jac > 0) else +1   # dg/dchi > 0 => chi=+1 excluded
                    if adm[exp] and not adm[-exp]: ok += 1
print("  matches:", ok, "/", (n-deg), " (+", deg, "both/none cases)")
print()
print("sharper: B sign per face, and V dot e:")
for rr in [mpf('0.379')]:
    for j in (0, 1):
        for (b1, b2) in [(mpf(1), mpf(1)), (mpf('0.8'), mpf(1)), (mpf('0.65'), mpf('0.65'))]:
            jac, B, Cdot, V = jacobian(rr, b1, b2, j)
            adm = {chi: admissible(rr, b1, b2, j, chi) for chi in (+1, -1)}
            print("   j=%d b1=%.3f b2=%.3f: B=%+.6f Cdot=%+.6f dg/dchi=%+.6f adm=%s"
                  % (j+1, b1, b2, B, Cdot, jac, adm))
