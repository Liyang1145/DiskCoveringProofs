from mpmath import mp, sin, cos, asin, atan2, sqrt, exp, pi, mpf, cosh
mp.dps = 30
R0 = mpf(19)/50
tmin = mpf(75)/76

print("Claim check: at d=0 the endpoint-max bound sin(al-om)>=sin(om) <=> om<=al/2,")
print("while covering is om <= asin(K), K = R0 sin(al).  Are they the same?")
for al in [mpf('0.5'), mpf('0.8'), mpf('1.0'), mpf('1.2'), mpf('1.4')]:
    K = R0*sin(al)
    print("  alpha=%.2f: al/2=%.6f  asin(R0 sin al)=%.6f  equal=%s"
          % (al, al/2, asin(K), abs(al/2 - asin(K)) < mpf('1e-25')))

print()
print("Check:  sin(alpha - omega) >= E sin(omega)   <=>   sin(omega) <= K e^{-|d|} ?")
print("   (E=e^{2|d|}, K=R0 sqrt(2(cosh2d-cos al))/2)")
bad = 0; n = 0
for d in ['0.0', '0.1', '0.2', '0.3', '0.5']:
    for al in [mpf('0.5'), mpf('0.8'), mpf('1.0'), mpf('1.2'), mpf('1.4'), mpf('1.55')]:
        E = exp(2*abs(mpf(d)))
        c = cos(al)
        Q = 2*(cosh(2*mpf(d)) - c); K = R0*sqrt(Q)/2
        for om in [mpf('0.05'), mpf('0.15'), mpf('0.25'), mpf('0.35'), mpf('0.45')]:
            if om >= al: continue
            lhs = sin(al-om) - E*sin(om) <= 0
            rhs = sin(om) - K*exp(-abs(mpf(d))) <= 0
            n += 1
            if lhs != rhs:
                bad += 1
                if bad <= 6:
                    print("  MISMATCH d=%s al=%.2f om=%.2f: C844=%s cov=%s"
                          % (d, al, om, lhs, rhs))
print("  tested", n, "mismatches", bad)

print()
print("Now the correct equivalence candidate:  K = R0 sin(al)/e^{|d|} * ... check identity")
print("  A^2 + (E+c)^2 vs (E+1)^2 sin^2 alpha  ...")
for d in ['0.0', '0.3']:
    for al in [mpf('0.8'), mpf('1.2')]:
        E = exp(2*abs(mpf(d))); c = cos(al); A = sin(al)
        print("   d=%s al=%.2f: A^2+(E+c)^2=%.9f ; (E+1)^2 A^2=%.9f"
              % (d, al, A*A + (E+c)**2, (E+1)**2*A*A))
