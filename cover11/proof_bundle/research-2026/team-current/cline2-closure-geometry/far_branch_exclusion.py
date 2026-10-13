from mpmath import mp, sin, cos, acos, sqrt, pi, mpf, tan, asin
mp.dps = 30

# EXACT geometry (from interval_hub_boundary.py):
#   DN: (v-s)^2 + t^2 <= (1-r)^2,  s = sqrt(1-r^2)      [hub norm disk]
#   D1: (v - r sin2b1)^2 + (t + r cos2b1)^2 <= r^2      [first face disk]
#   D2: (v - r sin2b2)^2 + (t - r cos2b2)^2 <= r^2      [second face disk]
#   wedge: -v tan b2 <= t <= v tan b1
# Claim to verify: NO point satisfies all four with v >= s (the "far"/+ polar branch).

def check(r, b1, b2, N=4000):
    s = sqrt(1-r*r)
    best = None; hits = 0
    # scan v over [s, s+(1-r)] since DN needs |v-s| <= 1-r there
    for i in range(N+1):
        v = s + (1-r)*mpf(i)/N
        # DN gives |t| <= sqrt((1-r)^2 - (v-s)^2)
        rad = (1-r)**2 - (v-s)**2
        if rad < 0: continue
        hw = sqrt(rad)
        for j in range(-60, 61):
            t = hw*mpf(j)/60
            d1 = (v - r*sin(2*b1))**2 + (t + r*cos(2*b1))**2 <= r*r
            d2 = (v - r*sin(2*b2))**2 + (t - r*cos(2*b2))**2 <= r*r
            wg = (-v*tan(b2) - mpf('1e-30') <= t) and (t <= v*tan(b1) + mpf('1e-30'))
            if d1 and d2 and wg:
                hits += 1
                if best is None or v > best[0]: best = (v, t)
    return hits, best

print("scan for feasible points on the FAR branch (v >= s):")
tot = 0
for r in [mpf(3)/8, mpf('0.376'), mpf(19)/50]:
    bhi = acos(r)
    for b1 in [mpf(1), mpf('1.05'), bhi]:
        for b2 in [mpf(1), (mpf(1)+bhi)/2, bhi]:
            hits, best = check(r, b1, b2, N=400)
            tot += hits
            print("  r=%.4f b1=%.4f b2=%.4f: hits=%d  %s" %
                  (r, b1, b2, hits, ("max v=%.6f t=%.6f" % best) if best else ""))
print("total hits:", tot)

print()
print("the decisive inequality  s > r(1 + min(sin2b1, sin2b2))  on the domain:")
worst = None
for r in [mpf(3)/8, mpf(19)/50]:
    bhi = acos(r)
    b1 = mpf(1); b2 = bhi
    s = sqrt(1-r*r)
    mx = r*(1+sin(2*b1))
    print("  r=%.4f b1=%.4f b2=%.4f: s=%.9f  r(1+sin2b1)=%.9f  s-gap=%.6f" %
          (r, b1, b2, s, mx, s-mx))
    # worst case over the domain: max of r(1+min(sin2b1,sin2b2)) at b=1
    print("      worst (max) of r(1+min(sin2b1,sin2b2)) = r(1+sin2) at b=1:")
    for rr in [mpf(3)/8, mpf(19)/50]:
        print("        r=%.4f: r(1+sin2)=%.9f  r(1+sin pi)=%.9f" % (rr, rr*(1+sin(2)), rr*(1+sin(pi))))

print()
print("also: far branch v >= s, and DN radius: v in [s, s+(1-r)] = [%.6f, %.6f]" %
      (sqrt(1-mpf('0.38')**2), sqrt(1-mpf('0.38')**2)+1-mpf('0.38')))
