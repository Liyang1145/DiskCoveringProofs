from mpmath import mp, sin, cos, acos, asin, atan, atan2, tan, sqrt, exp, pi, mpf, cosh
mp.dps = 30
R0 = mpf(19)/50
tmin = mpf(75)/76

print("Test:   omega_E <= omega_cov   <=>   K^2 (1+c^2) <= 1 ?")
print("  omega_E = atan2(A, E+c) ; omega_cov = asin(K e^{-|d|})")
print("  K = R0 sqrt(Q)/2, Q = 2(cosh2d - c), A=sin al, c=cos al, E=e^{2|d|}")
bad = 0; n = 0
for d in [mpf('0.0'), mpf('0.1'), mpf('0.2'), mpf('0.3'), mpf('0.5'), mpf('0.55')]:
    for al in [mpf('0.5'), mpf('0.8'), mpf('1.0'), mpf('1.2'), mpf('1.4'), mpf('1.55')]:
        c = cos(al); A = sin(al); E = exp(2*abs(d))
        Q = 2*(cosh(2*d) - c); K = R0*sqrt(Q)/2
        sE = A/sqrt(A*A + (E+c)**2)
        scov = K*exp(-abs(d))
        if scov > 1: continue
        le = sE <= scov + mpf('1e-25')
        R = K*K*(1 + c*c) <= 1 + mpf('1e-25')
        n += 1
        if le != R:
            bad += 1
            print("  MISMATCH d=%s al=%.2f: sE<=scov=%s  K^2(1+c^2)<=1=%s  K^2(1+c^2)=%.9f" % (d, al, le, R, K*K*(1+c*c)))
print("  tested", n, "mismatches", bad)

print()
print("max of K^2(1+c^2) on the admissible d-range:")
mx = None
for i in range(0, 601):
    d = mpf(i)/1000*mpf('0.56')
    for j in range(1, 628):
        al = mpf(j)/200*pi
        c = cos(al)
        Q = 2*(cosh(2*d) - c); K = R0*sqrt(Q)/2
        v = K*K*(1+c*c)
        if mx is None or v > mx[0]: mx = (v, d, al)
print("  max = %.9f at d=%.4f alpha=%.4f   (<=1: %s)" % (mx[0], mx[1], mx[2], mx[0] <= 1))

print()
print("alpha = pi branch:  (C844') <=> (E-1) sin omega <= 0")
for d in ['0.0', '0.3', '0.5']:
    E = exp(2*abs(mpf(d)))
    for om in [mpf('0.1'), mpf('0.5'), mpf('1.0')]:
        lhs = sin(pi-om) - E*sin(om)
        print("  d=%s E=%.6f om=%.2f: (sin(pi-om)-E sinom) = %.9f  = (1-E)sinom = %.9f"
              % (d, E, om, lhs, (1-E)*sin(om)))
