from mpmath import mp, sin, cos, acos, sqrt, pi, mpf, tan
mp.dps = 30

# EXACT chart from interval_cartesian_cancel.py / interval_hub_boundary.py:
#  disks: (cx, cy, rad) = (r sin2b1, -r cos2b1, r), (r sin2b2, +r cos2b2, r), (s, 0, 1-r),  s=sqrt(1-r^2)
#  wedge:  t >= -v tan b2 ,  t <= v tan b1
#  hub = (v,t) ; v = H_the_file (first coordinate)

def region(r, b1, b2, N=1200, M=400):
    s = sqrt(1-r*r)
    disks = [(r*sin(2*b1), -r*cos(2*b1), r), (r*sin(2*b2), r*cos(2*b2), r), (s, mpf(0), 1-r)]
    vlo = max(d[0]-d[2] for d in disks); vhi = min(d[0]+d[2] for d in disks)
    vlo = max(vlo, 0)
    pts = []
    for i in range(N+1):
        v = vlo + (vhi-vlo)*mpf(i)/N
        lo, hi = -mp.inf, mp.inf
        ok = True
        for (cx, cy, rad) in disks:
            q = rad*rad - (v-cx)**2
            if q < 0: ok = False; break
            rt = sqrt(q)
            lo = max(lo, cy-rt); hi = min(hi, cy+rt)
        if not ok: continue
        lo = max(lo, -v*tan(b2)); hi = min(hi, v*tan(b1))
        if hi < lo: continue
        for j in range(M+1):
            t = lo + (hi-lo)*mpf(j)/M
            pts.append((v, t))
    return pts, vlo, vhi

r = mpf('0.38')
for (b1, b2) in [(mpf(1), mpf(1)), (mpf(1), acos(r)), (acos(r), acos(r))]:
    pts, vlo, vhi = region(r, b1, b2, N=600, M=200)
    if not pts:
        print("b1=%.4f b2=%.4f: EMPTY" % (b1, b2)); continue
    vmin = min(p[0] for p in pts); vmax = max(p[0] for p in pts)
    tmin = min(p[1] for p in pts); tmax = max(p[1] for p in pts)
    tmaxabs = max(abs(p[1]) for p in pts)
    print("b1=%.4f b2=%.4f: npts=%d  v in [%.6f,%.6f]  t in [%.6f,%.6f]  |t|_max=%.6f"
          % (b1, b2, len(pts), vmin, vmax, tmin, tmax, tmaxabs))
    print("     2r(1-r)/s = %.6f ; s = %.6f ; 1-r = %.6f" % (2*r*(1-r)/sqrt(1-r*r), sqrt(1-r*r), 1-r))
    print("     r(1+min|cos2b|) = %.6f ; r(1+|cos2|) = %.6f" %
          (r*(1+min(abs(cos(2*b1)), abs(cos(2*b2)))), r*(1+abs(cos(2)))))

print()
print("for the far/polar + branch: v = s cos d + sqrt((1-r)^2 - s^2 sin^2 d), delta in [-b2,b1]")
print("  range of v on that branch (independent of the disks):")
for (b1, b2) in [(mpf(1), mpf(1)), (mpf(1), acos(r))]:
    vv = []
    for i in range(0, 801):
        d = -b2 + (b1+b2)*mpf(i)/800
        rad = (1-r)**2 - (sqrt(1-r*r))**2*sin(d)**2
        if rad < 0: continue
        vv.append(sqrt(1-r*r)*cos(d) + sqrt(rad))
    print("   b1=%.4f b2=%.4f: v_plus in [%.6f, %.6f]" % (b1, b2, min(vv), max(vv)))
