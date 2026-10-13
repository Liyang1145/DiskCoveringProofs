from mpmath import mp, sin, cos, tan, atan, asin, sqrt, exp, pi, mpf, cosh
mp.dps = 30
R0 = mpf(19)/50

print("EQUIVALENCE TEST: (C844p) vs s <= e^{-|d|}, scanning (alpha,d,s):")
bad = 0; n = 0
for d in [mpf('0.1'), mpf('0.3'), mpf('0.5')]:
    for al in [mpf('0.6'), mpf('0.8'), mpf('1.2'), mpf('1.4'), pi/2]:
        for s in [mpf('0.2'), mpf('0.4'), mpf('0.6'), mpf('0.8'), mpf(1)]:
            Q = 2*s*s*(cosh(2*d) - cos(al))
            h = R0*sqrt(Q)/2
            if h/R0 >= 1: continue
            w = 2*asin(h/R0)
            lhs = sin(al - w/2); rhs = exp(2*abs(d))*sin(w/2)
            c1 = lhs >= rhs - mpf('1e-25')
            c2 = s <= exp(-abs(d)) + mpf('1e-25')
            n += 1
            if c1 != c2:
                bad += 1
                print("  MISMATCH d=%s al=%.3f s=%s: C844=%s covering=%s" % (d, al, s, c1, c2))
print("  tested", n, "mismatches", bad)

print()
print("s_min = R0 e^{2|d|}/(2 rho) vs definition R0 sin(w_max/2)/(2 rho sin(al-w_max/2)):")
for d in ['0.1', '0.3', '0.5']:
    mu = exp(2*mpf(d))
    for al in [mpf('0.8'), mpf('1.2'), mpf('1.5'), pi/2]:
        wm = al - 2*atan((mu-1)*tan(al/2)/(mu+1))
        s1 = R0*sin(wm/2)/(2*sin(al-wm/2))
        s2 = R0*exp(2*mpf(d))/2
        print("  d=%s al=%.3f: %.18f vs %.18f diff=%.1e" % (d, al, s1, s2, s1-s2))

print()
print("nonempty: s_min <= s_max  <=>  e^{3|d|} <= 2 rho/R0 ; check the crossing:")
for d in ['0.50', '0.55', '0.5535', '0.5536', '0.56']:
    dd = mpf(d)
    smin = R0*exp(2*dd)/2; smax = exp(-dd)
    print("  d=%s: s_min=%.9f s_max=%.9f nonempty=%s  (1/3)ln(2/R0)=%.9f"
          % (d, smin, smax, smin <= smax, mp.log(2/R0)/3))
