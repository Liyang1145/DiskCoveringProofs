from mpmath import mp, sin, cos, acos, sqrt, pi, mpf, tan
mp.dps = 30
r = mpf(19)/50
s = sqrt(1-r*r)
b1 = mpf(1)
print("=== corrected chain (plus root) ===")
tau = r*(1+cos(2)); tmin = r*(1-cos(2))
print("|t| <= r(1+cos2) = %.9f ;  observed max|t| = 0.221863847  (ratio %.6f)"
      % (tau, mpf('0.221863847')/tau))
print("covering lower bound 2r(1-r)/s = %.9f  (= %.6f)" % (2*r*(1-r)/s, 2*r*(1-r)/(1-r)))
print()
print("(1-r)^2 - tau^2 = %.9f" % ((1-r)**2 - tau*tau))
root = sqrt((1-r)**2 - tau*tau)
print("sqrt(...) = %.9f ;  s - that = %.9f" % (root, s-root))
print("so v <= %.6f < 0.35  <  2r(1-r)/s = %.6f  <= v  -> CONTRADICTION" % (s-root, 2*r*(1-r)/(1-r)))
print()
print("=== with r >= 3/8 only (worst case for the lower bound) ===")
r0 = mpf(3)/8; s0 = sqrt(1-r0*r0); tau0 = r0*(1+cos(2))
print("r=3/8: s=%.9f 2r(1-r)/s=%.9f ; (1-r)^2-tau^2=%.9f sqrt=%.9f  v<=%.9f"
      % (s0, 2*r0*(1-r0)/s0, (1-r0)**2 - tau0*tau0, sqrt((1-r0)**2-tau0*tau0), s0-sqrt((1-r0)**2-tau0*tau0)))
print()
print("=== t-bound: max|t| over the domain ===")
def maxabs_t(r, b1, b2, N=60000):
    s = sqrt(1-r*r)
    disks = [(r*sin(2*b1), -r*cos(2*b1), r), (r*sin(2*b2), r*cos(2*b2), r), (s, mpf(0), 1-r)]
    vlo = max(0, max(d[0]-d[2] for d in disks)); vhi = min(d[0]+d[2] for d in disks)
    best = None
    for i in range(N+1):
        v = vlo + (vhi-vlo)*mpf(i)/N
        lo, hi = -mp.inf, mp.inf; ok = True
        for (cx, cy, rad) in disks:
            q = rad*rad - (v-cx)**2
            if q < 0: ok = False; break
            rt = sqrt(q); lo = max(lo, cy-rt); hi = min(hi, cy+rt)
        if not ok: continue
        lo = max(lo, -v*tan(b2)); hi = min(hi, v*tan(b1))
        if hi < lo: continue
        m = max(abs(lo), abs(hi))
        if best is None or m > best[0]: best = (m, v)
    return best
worst = None
for rr in [mpf(3)/8, mpf('0.376'), mpf('0.38')]:
    bhi = acos(rr)
    for b1 in [mpf(1), mpf('1.05'), bhi]:
        for b2 in [mpf(1), (mpf(1)+bhi)/2, bhi]:
            b = maxabs_t(rr, b1, b2, N=4000)
            if b and (worst is None or b[0] > worst[0]): worst = (b[0], rr, b1, b2, b[1])
print("  worst over grid: max|t| = %.9f at r=%s b1=%.4f b2=%.4f (v=%.6f)"
      % (worst[0], mp.nstr(worst[1],5), worst[2], worst[3], worst[4]))
print("  r(1+cos2) at r=%.5f = %.9f  -> bound holds: %s" % (worst[1], worst[1]*(1+cos(2)), worst[0] <= worst[1]*(1+cos(2))+mpf('1e-12')))
