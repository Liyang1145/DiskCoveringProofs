from mpmath import mp, sin, cos, asin, atan2, sqrt, exp, pi, mpf, cosh, findroot
mp.dps = 30
R0 = mpf(19)/50
tmin = mpf(75)/76

def bounds(d, al):
    c = cos(al); A = sin(al); E = exp(2*abs(mpf(d)))
    Q = 2*(cosh(2*mpf(d)) - c); K = R0*sqrt(Q)/2
    omE = atan2(A, E + c) if (E + c) != 0 else None
    omC = asin(K*exp(-abs(mpf(d)))) if K*exp(-abs(mpf(d))) <= 1 else None
    return omE, omC, K, E

print("omega_E (endpoint-max) vs omega_cov (covering): which is tighter?")
for d in ['0.0', '0.1', '0.3', '0.5']:
    row = []
    for al in [mpf('0.2'), mpf('0.5'), mpf('0.8'), mpf('1.0'), mpf('1.2'), mpf('1.4'), mpf('1.55')]:
        omE, omC, K, E = bounds(d, al)
        if omE is None or omC is None:
            row.append("al=%.2f: n/a" % al); continue
        tag = "E" if omE < omC else ("C" if omC < omE else "=")
        row.append("al=%.2f %s" % (al, tag))
    print("  d=%s: %s" % (d, "  ".join(row)))

print()
print("the d=0 formula K = R0 sin(alpha) / 1 ... verify:")
for al in [mpf('0.5'), mpf('1.0'), mpf('1.4')]:
    c = cos(al)
    Q = 2*(1 - c); K = R0*sqrt(Q)/2
    print("  alpha=%.2f: K=%.9f  R0*sin(alpha)/sqrt(2(1-cos al)) *sqrt2 ... check K^2=2R0^2 sin^2(al/2) : %.9f"
          % (al, K, 2*R0*R0*sin(al/2)**2))

print()
print("closed form for omega_E:  sin(omega_E) = A/sqrt(A^2+(E+c)^2)")
for d in ['0.0', '0.3']:
    for al in [mpf('0.8'), mpf('1.2')]:
        omE, omC, K, E = bounds(d, al)
        c = cos(al); A = sin(al)
        print("   d=%s al=%.2f: sin(omE)=%.9f vs A/sqrt(A^2+(E+c)^2)=%.9f"
              % (d, al, sin(omE), A/sqrt(A*A + (E+c)**2)))

print()
print("nonempty of full fiber: omega_lo=(alpha-theta)/2 <= min(omE, omC)?  (theta=acos(B), B=c+2K^2tmin^2)")
bad = 0; n = 0
for d in ['0.0', '0.2', '0.4', '0.5']:
    for al in [mpf('0.3'), mpf('0.6'), mpf('0.9'), mpf('1.2'), mpf('1.45')]:
        c = cos(al); E = exp(2*abs(mpf(d)))
        Q = 2*(cosh(2*mpf(d)) - c); K = R0*sqrt(Q)/2
        B = c + 2*K*K*tmin*tmin
        if abs(B) > 1: continue
        th = mp.acos(B)
        lo = (al - th)/2
        omE, omC, _, _ = bounds(d, al)
        hi = min(omE, omC) if (omE is not None and omC is not None) else None
        if hi is None: continue
        n += 1
        if lo > hi:
            bad += 1
            print("   EMPTY d=%s al=%.2f: lo=%.6f hi=%.6f (omE=%.6f omC=%.6f)" % (d, al, lo, hi, omE, omC))
print("   tested", n, "empty", bad)
