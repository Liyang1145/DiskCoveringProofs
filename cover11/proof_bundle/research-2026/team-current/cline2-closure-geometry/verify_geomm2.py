from mpmath import mp, sin, cos, tan, atan, asin, sqrt, exp, pi, mpf, cosh
mp.dps = 30
R0 = mpf(19)/50

# Test the ONLY two candidate equivalences on a grid:
#  F1 (C844'):  sin(alpha - w/2) >= e^{2|d|} sin(w/2)
#  F2 covering: s <= e^{-|d|}
#  F3 (L):      sin(alpha - w/2) >= rho^2 sin(w/2)   (rho=1 worst case)
print("grid test of candidate equivalences (rho=1):")
bad12 = bad13 = 0; n = 0
for d in [mpf('0.05'), mpf('0.1'), mpf('0.3'), mpf('0.5')]:
    for al in [mpf('0.6'), mpf('0.8'), mpf('1.0'), mpf('1.2'), mpf('1.4'), pi/2]:
        for s in [mpf('0.1'), mpf('0.2'), mpf('0.4'), mpf('0.6'), mpf('0.8'), mpf('1.0')]:
            Q = 2*s*s*(cosh(2*d) - cos(al))
            h = R0*sqrt(Q)/2
            if h/R0 >= 1: continue
            w = 2*asin(h/R0)
            F1 = sin(al - w/2) >= exp(2*abs(d))*sin(w/2) - mpf('1e-25')
            F2 = s <= exp(-abs(d)) + mpf('1e-25')
            F3 = sin(al - w/2) >= sin(w/2) - mpf('1e-25')
            n += 1
            if F1 != F2: bad12 += 1
            if F1 != F3: bad13 += 1
print("  points", n, " F1 vs F2 mismatches:", bad12, " F1 vs F3 mismatches:", bad13)

print()
print("crossing check for (I) nonempty at d scanning, rho=1:")
for d in ['0.50', '0.55', '0.5535', '0.5536', '0.56']:
    dd = mpf(d)
    smin = R0*exp(2*dd)/2; smax = exp(-dd)
    print("  d=%s s_min=%.9f s_max=%.9f nonempty=%s   (1/3)ln(2/R0)=%.9f"
          % (d, smin, smax, smin <= smax, mp.log(2/R0)/3))

print()
print("at w=w_max: is s_min alpha-independent? evaluate s = R0*sin(w_max/2)/(2 sin(al-w_max/2))/... ")
for d in ['0.1', '0.3', '0.5']:
    mu = exp(2*mpf(d))
    for al in [mpf('0.8'), mpf('1.2'), pi/2]:
        wm = al - 2*atan((mu-1)*tan(al/2)/(mu+1))
        # scale from Q: s = 2 sin(wm/2)/(R0 sqrt(2(cosh2d-cos al)))? check definition
        Q = 4*sin(wm/2)**2/R0**2
        s_from_Q = sqrt(Q/(2*(cosh(2*mpf(d))-cos(al))))
        print("  d=%s al=%.3f: s from Q at w_max = %.15f   s_min(a-)def = R0/(2 mu) = %.15f"
              % (d, al, s_from_Q, R0/(2*mu)))
