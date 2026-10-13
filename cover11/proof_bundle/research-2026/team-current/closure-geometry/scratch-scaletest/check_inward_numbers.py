from mpmath import mp, asin, sin, sqrt, pi, mpf

mp.dps = 30
R = mpf(19)/50

print("=== constants in the bridge ===")
print("19/50 =", R)
print("sin(pi/8) =", mp.nstr(sin(pi/8), 20), "   (0.38 < sin(pi/8):", R < sin(pi/8), ")")
print("asin(19/50) =", mp.nstr(asin(R), 20))
print("8 asin(19/50) =", mp.nstr(8*asin(R), 20), " < pi =", mp.nstr(pi, 20), ":", 8*asin(R) < pi)
print("2 asin(19/50) < pi/2 ?", 2*asin(R) < pi/2, "  (needed for 'arc length < pi')")
print()
print("=== C464 numeric geometry ===")
for r in [mpf('0.2'), mpf('0.3'), mpf('0.38'), mpf('0.5')]:
    disc = 1 - 4*r*r*(1-r*r)
    if disc < 0:
        print("  r=%.2f: 1-2r+sqrt(r^2-r^4) < r ? (discriminant %s)" % (r, mp.nstr(disc, 8)))
        print("        rho_minus = (1 - sqrt(1-4r^2(1-r^2)))/2 = %s < 1/2" %
              mp.nstr((1 - sqrt(1-4*r*r*(1-r*r)))/2, 12))
        print("        => the inner disk does NOT contain the origin; the region split is required.")
    else:
        print("  r=%.2f: inner disk contains the origin (c <= 1)" % r)
print()
print("check the decisive inequality used in C464 algebra:")
for r in [mpf('0.2'), mpf('0.38'), mpf('0.5'), mpf('0.7')]:
    rho_minus = (1 - sqrt(1-4*r*r*(1-r*r)))/2
    rho_plus = (1 + sqrt(1-4*r*r*(1-r*r)))/2
    prod = rho_minus*rho_plus
    c = (rho_minus + rho_plus)/2
    print("  r=%.2f: rho_-=%.12f rho_+=%.12f prod=%.12f (1-r^2=%.12f) 2rho_- >= 1-r^2 ? %s  c=%.12f<=1 ? %s"
          % (r, rho_minus, rho_plus, prod, 1-r*r, 2*rho_minus >= 1-r*r, c, c <= 1))
print()
print("m >= 9 arithmetic: sin(pi/8)^2 = (2-sqrt2)/4 =", mp.nstr((2-sqrt(2))/4, 20),
      "  (19/50)^2 =", mp.nstr(R*R, 20), " R^2 < that:", R*R < (2-sqrt(2))/4)
print("  790321 > 781250 check: 889^2 =", 889**2, " 2*625^2 =", 2*625**2)
