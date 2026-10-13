from mpmath import mp, sin, cos, acos, asin, atan, atan2, tan, sqrt, exp, pi, mpf, cosh
mp.dps = 30
R0 = mpf(19)/50
tmin = mpf(75)/76

def geom_constraints(d, al, s):
    """direct geometric check of the two constraints at given (d, alpha, s)"""
    c = cos(al); A = sin(al)
    Q = 2*(cosh(2*mpf(d)) - c)
    K = R0*sqrt(Q)/2
    h = K*s
    if h >= 1: return None, None, K
    w = 2*asin(h); om = w/2
    lower = sin(om)*sin(al-om) >= K*K*tmin*tmin - mpf('1e-25')
    E = exp(2*abs(mpf(d)))
    upper = sin(al-om) >= E*sin(om) - mpf('1e-25')
    return lower, upper, K

def omega_interval(d, al):
    """lead's omega interval: [ (alpha-theta)/2, min( (alpha+theta)/2, atan2(A,E+c) ) ]"""
    c = cos(al); A = sin(al)
    Q = 2*(cosh(2*mpf(d)) - c)
    K = R0*sqrt(Q)/2
    E = exp(2*abs(mpf(d)))
    B = c + 2*K*K*tmin*tmin
    if B < -1: return None
    if B > 1: return ('B>1',)
    th = acos(B)
    lo = (al - th)/2
    hi = (al + th)/2
    hi2 = atan2(A, E + c) if (E + c) > 0 else None
    return lo, hi, hi2, K, B

print("=== check lower-constraint reduction: sinom sin(al-om) >= K^2 tmin^2  <=> cos(2om-al) >= cos al + 2K^2 tmin^2")
for (d, al) in [(mpf('0.3'), mpf('1.2')), (mpf('0.1'), mpf('1.4')), (mpf('0.0'), mpf('1.0')), (mpf('0.5'), mpf('0.8'))]:
    c = cos(al)
    Q = 2*(cosh(2*mpf(d)) - c); K = R0*sqrt(Q)/2
    for om in [mpf('0.3'), mpf('0.5'), mpf('0.7')]:
        if om >= al: continue
        l1 = sin(om)*sin(al-om)
        l2 = (cos(2*om-al) - c)/2
        print("  d=%s al=%.2f om=%.2f: %.15f vs %.15f  diff=%.1e" % (d, al, om, l1, l2, l1-l2))

print()
print("=== check endpoint-max reduction: sin(al-om) >= E sin om  <=>  om <= atan2(A,E+c)")
for (d, al) in [(mpf('0.3'), mpf('1.2')), (mpf('0.1'), mpf('1.4')), (mpf('0.5'), mpf('0.8'))]:
    c = cos(al); A = sin(al); E = exp(2*abs(mpf(d)))
    omstar = atan2(A, E + c)
    for om in [omstar - mpf('0.1'), omstar + mpf('0.1')]:
        lhs = sin(al-om); rhs = E*sin(om)
        print("  d=%s al=%.2f om=%.6f (om*=%s): lhs-rhs=%.3e  side=%s"
              % (d, al, om, mp.nstr(omstar, 8), lhs-rhs, 'below' if om < omstar else 'above'))

print()
print("=== full interval check: lead's omega interval vs direct geometry, scanning s ===")
bad = 0; n = 0
for d in ['0.0', '0.1', '0.3', '0.5']:
    for al in [mpf('0.8'), mpf('1.0'), mpf('1.2'), mpf('1.4'), mpf('1.5')]:
        r = omega_interval(d, al)
        if r is None or r[0] == 'B>1': continue
        lo, hi, hi2, K, B = r
        hi_eff = min(hi, hi2) if hi2 is not None else hi
        for s in [mpf('0.1'), mpf('0.2'), mpf('0.3'), mpf('0.4'), mpf('0.5'), mpf('0.6'), mpf('0.8'), mpf('1.0')]:
            h = K*s
            if h >= 1: continue
            om = asin(h)/1  # = w/2
            lo_ok = lo - mpf('1e-20') <= om
            hi_ok = om <= hi_eff + mpf('1e-20')
            in_interv = lo_ok and hi_ok
            gl, gu, _ = geom_constraints(d, al, s)
            if gl is None: continue
            n += 1
            if in_interv != (gl and gu):
                bad += 1
                if bad <= 8:
                    print("  MISMATCH d=%s al=%.2f s=%s om=%.6f interv=[%.6f,%.6f] in=%s geom=(%s,%s)"
                          % (d, al, s, om, lo, hi_eff, in_interv, gl, gu))
print("  tested", n, "mismatches", bad)
