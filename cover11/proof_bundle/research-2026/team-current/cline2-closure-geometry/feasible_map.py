from mpmath import mp, sin, cos, acos, atan, sqrt, pi, mpf, atan2, tan
mp.dps = 25

# EXACT geometry from interval_hub_boundary.py:
#   disks (center, radius):  D1 = (r sin2b1, -r cos2b1, r)
#                            D2 = (r sin2b2, +r cos2b2, r)
#                            DN = (s, 0, 1-r),  s = sqrt(1-r^2)
#   wedge:   t <= v tan b1   and   t >= -v tan b2
# Feasible hub = D1 cap D2 cap DN cap wedge.

def feas(v, t, r, b1, b2):
    s = sqrt(1-r*r)
    d1 = (v - r*sin(2*b1))**2 + (t + r*cos(2*b1))**2
    d2 = (v - r*sin(2*b2))**2 + (t - r*cos(2*b2))**2
    dn = (v - s)**2 + t*t
    return (d1 <= r*r + mpf('1e-25'), d2 <= r*r + mpf('1e-25'),
            dn <= (1-r)**2 + mpf('1e-25'),
            t <= v*tan(b1) + mpf('1e-25'), t >= -v*tan(b2) - mpf('1e-25'))

r = mpf('0.38'); s = sqrt(1-r*r)
print("r=0.38 s=sqrt(1-r^2)=%.9f  1-r=%.9f  D1 center=(%.6f,%.6f) D2 center=(%.6f,%.6f)" %
      (s, 1-r, r*sin(2), -r*cos(2), r*sin(2), r*cos(2)))

print()
print("max feasible v (scan t) for several (b1,b2):")
for (b1, b2) in [(mpf(1), mpf(1)), (mpf(1), mpf('1.18')), (mpf('1.18'), mpf('1.18')),
                 (mpf(1), mpf('1.1'))]:
    best = None
    for i in range(-400, 401):
        t = mpf(i)/400*mpf('0.5')
        for j in range(0, 2001):
            v = mpf(j)/2000
            f = feas(v, t, r, b1, b2)
            if all(f):
                if best is None or v > best[0]:
                    best = (v, t)
    print("  b1=%.4f b2=%.4f:  max feasible v = %s at t=%s" %
          (b1, b2, mp.nstr(best[0], 8) if best else 'NONE', mp.nstr(best[1], 8) if best else '-'))

print()
print("norm-disk boundary:  DN = {(v,t): (v-s)^2+t^2 = (1-r)^2}")
print("  far branch needs v >= ?  (the boundary self-consistency: t=0 points v=0 and v=2s)")
print("  near branch: v in [0, 2s] but on the LEFT arc v<s; far: v>s")
print("  2r(1-r)/s = %.6f" % (2*r*(1-r)/s))
print()
print("far-branch locus: parametrize by t, v = s + sqrt((1-r)^2 - t^2) (far = right arc)")
for b1, b2 in [(mpf(1), mpf(1))]:
    print("  b1=%.2f b2=%.2f: scan far arc vs disk/wedge constraints:" % (b1, b2))
    cnt = 0
    for i in range(-1000, 1001):
        t = mpf(i)/1000*(1-r)
        rad = (1-r)**2 - t*t
        if rad < 0: continue
        v = s + sqrt(rad)
        f = feas(v, t, r, b1, b2)
        if f[0] and f[1] and f[3] and f[4]:
            cnt += 1
            if cnt <= 3: print("     feasible-on-DN-and-disks: v=%.6f t=%.6f" % (v, t))
    print("     total feasible far-arc points (ignoring DN itself, i.e. ON DN):", cnt)
