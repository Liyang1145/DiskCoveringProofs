from mpmath import mp, sin, cos, acos, asin, atan2, sqrt, exp, pi, mpf, cosh, log
mp.dps = 25
R0 = mpf(19)/50

print("=== corrections to verify ===")
print("1. B-direction:  cos(2w-a) >= B with B=cos a + 2K^2 rho^2")
print("   B > 1  ->  ALL omega satisfy (cos <= 1 <= B);  B < -1 -> EMPTY (cos >= -1 > B)")
print("   B in [-1,1] -> |2omega - alpha| <= theta, theta = acos(B)")
for B in [mpf('1.5'), mpf('0.5'), mpf('-1.5'), mpf('-1.0'), mpf('1.0')]:
    if B > 1: tag = "ALL (no constraint)"
    elif B < -1: tag = "EMPTY"
    else: tag = "theta=%.4f -> |2w-a|<=theta" % mp.acos(B)
    print("   B=%s : %s" % (B, tag))

print()
print("2. alpha=pi, d=0 branch: K = R0 (Q=4), L-condition:")
print("   cos(2w-pi) = -cos(2w) >= -1 + 2R0^2 rho^2  <=>  sin^2 w <= R0^2 rho^2  <=>  w >= asin(R0 rho)")
print("   covering (E=1): sin w <= K = R0  ->  w <= asin(R0)")
for rho in [mpf(1), mpf(75)/76]:
    lo = asin(R0*rho); hi = asin(R0)
    print("   rho=%s: omega in [%.6f, %.6f]  (= [asin(R0 rho), asin(R0)])" % (rho, lo, hi))
print("   check numerically at d=0, alpha=pi, omega=0.3:")
for om in [mpf('0.1'), mpf('0.3'), mpf('0.39'), mpf('0.45')]:
    lhs = sin(pi-om) - sin(om)             # (C844') at E=1: vacuous
    s = sin(om)/R0
    low = sin(om)*sin(pi-om) >= R0*R0*(mpf(75)/76)**2
    cov = s <= 1
    print("     om=%.2f: (C844') lhs-rhs=%.1e  L-cond=%s (s=%.4f)  cover=%s" % (om, lhs, low, s, cov))

print()
print("3. |d| bound from u,v >= 0.19: |d| = 0.5 log(u/v) <= 0.5 log(1/0.19) =",
      mp.nstr(mpf('0.5')*log(1/mpf('0.19')), 12))
print("   (not 0.5536, which came from the removed s_min <= s_max argument)")

print()
print("4. norm bound:  sqrt(1-r^2) <= sqrt(55)/8 ; and r <= 19/50 gives sqrt(2139)/50 =",
      mp.nstr(sqrt(mpf(2139))/50, 15), " < sqrt(55)/8 =", mp.nstr(sqrt(55)/8, 15))
print("   the valid, rho-independent choice is |c| <= sqrt(55)/8")
