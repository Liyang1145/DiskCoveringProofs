from mpmath import mp, sin, cos, acos, sqrt, mpf
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
    else:      return r*sin(2*b1), -r*cos(2*b1)

print("exact bilinear form: g(X_chi) = |V|^2 + r^2 - 2 a chi B - 2 chi h Cdot")
print("  where V = C_other - C_self, B = Je x V, Cdot = <Je_perp... > ; test the sign structure")
print()
n = 0; mism = 0
data = []
for rr in [mpf('0.379'), mpf('0.37999')]:
    blo = acos(rr)/2
    for b1 in [blo+mpf('0.001'), mpf('0.7'), mpf('0.9'), mpf(1)]:
        for b2 in [blo+mpf('0.001'), mpf('0.7'), mpf('0.9'), mpf(1)]:
            for j in (0, 1):
                sigma = -1 if j == 0 else 1
                b = b1 if j == 0 else b2
                bo = b2 if j == 0 else b1
                s, cx, cy, d, a, h, ex, ey = build(rr, b, sigma)
                ox, oy = other_center(rr, b1, b2, j)
                V = (ox-cx, oy-cy)
                B = (-ey)*V[1] - (ex)*V[0]
                # g(chi) = |V|^2 + r^2 - 2 a chi B + 2 chi h |V| sin?  use direct:
                gs = {}
                for chi in (+1, -1):
                    X, Y = corner(rr, b1, b2, j, chi)
                    gs[chi] = (X-ox)**2 + (Y-oy)**2 - rr*rr
                adm = -1 if gs[-1] <= 0 else +1
                data.append((rr, b, bo, j, B/a if a != 0 else None, gs[+1], gs[-1], adm))
print("  B/a vs admitted sign (admitted = minimiser of g):")
for (rr, b, bo, j, rB, gp, gm, adm) in data[:16]:
    print("    r=%s b=%.3f bo=%.3f j=%d: B/a=%+.6f  g+=%+.6f g-=%+.6f  adm=%+d  (adm == -sign(B)? %s)"
          % (mp.nstr(rr, 7), b, bo, j+1, rB, gp, gm, adm, adm == (-1 if rB > 0 else 1)))
print()
print("count: admitted == -sign(B) ?")
ok = sum(1 for (rr, b, bo, j, rB, gp, gm, adm) in data
         if (rB > 0 and adm == -1) or (rB < 0 and adm == 1) or (rB == 0 and gm <= gp))
print("   ", ok, "/", len(data))
print()
print("count: admitted == -sign(sin b_j - sin b_o) ?  (b_o = other bearing)")
ok2 = 0
for (rr, b, bo, j, rB, gp, gm, adm) in data:
    pred = -1 if sin(b) > sin(bo) else +1
    if adm == pred: ok2 += 1
print("   ", ok2, "/", len(data))
