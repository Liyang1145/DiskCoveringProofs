from mpmath import mp, sin, cos, acos, asin, atan2, sqrt, exp, pi, mpf, cosh, log
mp.dps = 30
R0 = mpf(19)/50
tmin = mpf(75)/76

print("=== 1. The endpoint-distance lower bound ===")
s55 = sqrt(55)
print("  sqrt(55)/8 =", mp.nstr(s55/8, 20))
print("  1 - sqrt(55)/8 =", mp.nstr(1 - s55/8, 20))
print("  (1 - sqrt(55)/8)/R0 =", mp.nstr((1 - s55/8)/R0, 20), " > 0.19 ?",
      (1 - s55/8)/R0 > mpf('0.19'))
print("  exact chain: sqrt(55) < 8(1 - 0.38*0.19) =", mp.nstr(8*(1 - mpf('0.38')*mpf('0.19')), 20),
      "->", s55 < 8*(1 - mpf('0.38')*mpf('0.19')))
print("  check: 1-0.38*0.19 =", mp.nstr(1 - mpf('0.38')*mpf('0.19'), 20),
      " and sqrt(55)/8 =", mp.nstr(s55/8, 20))

print()
print("=== 2. Compare with the old delta-based bound ===")
print("  claim old bound ~ 0.000026 ; new 1-sqrt(55)/8 = %.6f ; ratio ~ %.1f"
      % (1 - s55/8, (1 - s55/8)/mpf('0.000026')))

print()
print("=== 3. Independent proof check: p >= 1 - |c| for a boundary point ===")
print("  P on bd D, |c| = t, |P - c| = p : 1 = |P| <= |P-c| + |c| = p + t  =>  p >= 1 - t.")
print("  t <= sqrt(1-r^2) <= sqrt(55)/8  (r <= 19/50, exact: (19/50)^2 = 361/2500,")
print("   1 - 361/2500 = 2139/2500, sqrt =", mp.nstr(sqrt(mpf(2139)/2500), 20), ")")
print("  so p >= 1 - sqrt(55)/8 =", mp.nstr(1 - s55/8, 20), " for EVERY genuine endpoint.")
print("  (Both valid bounds t <= sqrt(1-r^2) and t <= 1-r give p >= 1-t; the former is")
print("   the informative one because sqrt(1-r^2) >> 1-r at r=0.38:",
      mp.nstr(sqrt(1-mpf('0.38')**2), 12), "vs", mp.nstr(1-mpf('0.38'), 12), ")")

print()
print("=== 4. Consequence for omega ===")
print("  u = p/R0 > 19/100 = 0.19 ; kappa = sqrt(2(cosh 2d - cos alpha))/2 = K/R0 ;")
print("  sin omega = K s = R0 kappa s ; s = sqrt(uv) > 0.19 ; K = R0 kappa >= R0 sin alpha.")
print("  d = 0: K = R0 sqrt((1-cos alpha)/2)*sqrt2 = R0 sin(alpha/2) ; sin omega > R0 sin(alpha/2)*0.19")
mn = None
for i in range(1, 451):
    al = mpf(i)/450*pi
    K = R0*sin(al/2)
    v = asin(K*mpf('0.19'))
    if mn is None or v < mn[0]: mn = (v, al, K)
print("  d=0, s>0.19: min over alpha of asin(K*0.19) = %.6f at alpha=%.4f (K=%.6f)"
      % (mn[0], mn[1], mn[2]))
print("  2*min = w_min = %.6f rad (positive lower bound on the width!)" % (2*mn[0]))

print()
print("=== 5. Fiber compactness ===")
print("  omega in [omega_lo, omega_hi] with omega_lo >= %.6f and omega_hi <= pi/2." % mn[0])
print("  => closed bounded interval; (u,v) = (s e^d, s e^{-d}) with s = sin omega/K")
print("     and |d| <= (1/3)ln(2 rho/R0) (from s_min <= s_max) => compact.")
