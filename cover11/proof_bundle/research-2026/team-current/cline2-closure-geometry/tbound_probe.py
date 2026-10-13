from mpmath import mp, sin, cos, acos, sqrt, pi, mpf, tan, atan
mp.dps = 30

# EXACT chart: disks (r sin2b1, -r cos2b1, r), (r sin2b2, +r cos2b2, r), (s,0,1-r), s=sqrt(1-r^2)
# wedge t>=-v tan b2, t<=v tan b1.  Feasible hub = intersection.
# Candidate boundary: wedge line t = v tan b1 meets DN: (v-s)^2+t^2=(1-r)^2, then the
# point is checked against D1 (tangency) and D2.

def maxabs_t(r, b1, b2, N=400000):
    s = sqrt(1-r*r)
    # candidate from wedge-line cap D1 & DN intersection
    tb = r*(sin(b1) - cos(2*b1))
    vb = r*(1 + sin(b1))*cos(b1)
    cands = []
    # scan v over the feasible range from the three disks
    vlo = max(0, max(d[0]-d[2] for d in [(r*sin(2*b1), -r*cos(2*b1), r),
                                         (r*sin(2*b2), r*cos(2*b2), r),
                                         (s, mpf(0), 1-r)]))
    vhi = min(d[0]+d[2] for d in [(r*sin(2*b1), -r*cos(2*b1), r),
                                  (r*sin(2*b2), r*cos(2*b2), r),
                                  (s, mpf(0), 1-r)])
    best = None
    for i in range(N+1):
        v = vlo + (vhi-vlo)*mpf(i)/N
        lo, hi = -mp.inf, mp.inf
        ok = True
        for (cx, cy, rad) in [(r*sin(2*b1), -r*cos(2*b1), r), (r*sin(2*b2), r*cos(2*b2), r), (s, mpf(0), 1-r)]:
            q = rad*rad - (v-cx)**2
            if q < 0: ok = False; break
            rt = sqrt(q); lo = max(lo, cy-rt); hi = min(hi, cy+rt)
        if not ok: continue
        lo = max(lo, -v*tan(b2)); hi = min(hi, v*tan(b1))
        if hi < lo: continue
        m = max(abs(lo), abs(hi))
        if best is None or m > best[0]:
            best = (m, v, lo, hi)
    return best, (vb, tb)

r = mpf(19)/50
for (b1, b2) in [(mpf(1), mpf(1)), (mpf(1), acos(r)), (mpf('1.1'), mpf(1))]:
    best, cand = maxabs_t(r, b1, b2, N=20000)
    print("b1=%.4f b2=%.4f:  max|t| = %.9f at v=%.6f (t-range [%.6f,%.6f])"
          % (b1, b2, best[0], best[1], best[2], best[3]))
    print("      candidate (wedge cap D1 & DN): v*=%.6f t*=%.6f  ; t* <= 2220/10000 ? %s"
          % (cand[0], cand[1], cand[1] <= mpf('0.2220')))
