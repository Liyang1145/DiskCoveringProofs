from mpmath import mp, sqrt, asin, sin, pi, mpf

mp.dps = 30
print("=== the correct two-root geometry (C464 setup) ===")
print("Both disks pass through the SAME two unit-circle points (the arc troughs),")
print("so their centres on the ray satisfy rho^2 - 2 rho cos(theta) + (1-r^2) = 0,")
print("with roots rho_-, rho_+ satisfying  rho_-*rho_+ = 1 - r^2 and rho_- <= rho_+ <= 1+r.")
print()
for r in [mpf('0.1'), mpf('0.2'), mpf('0.38'), mpf('0.5'), mpf('0.8')]:
    prod = 1 - r*r
    rp_max = 1 + r
    rp_min = sqrt(prod)              # rho_- = rho_+ = sqrt(1-r^2) at the double root
    # pick a representative: rho_+ = 1 (a valid choice since sqrt(1-r^2) <= 1 <= 1+r)
    rp = min(mpf(1), rp_max)
    rm = prod/rp
    c = (rm + rp)/2
    ok_2rm = 2*rm >= prod            # <=> rho_+ <= 2
    ok_c = c <= 1
    print("  r=%.2f: rho_-=%.12f rho_+=%.12f  c=%.12f  2rho_- >= 1-r^2 ? %s   c<=1 ? %s  (rho_+<=1+r: %s)"
          % (r, rm, rp, c, ok_2rm, ok_c, rp <= rp_max))
print()
print("general proof of the two needed inequalities for the allowed range 0<r<=19/50:")
print("  (i)  rho_+ <= 1+r <= 2      => 2rho_- = 2(1-r^2)/rho_+ >= (1-r^2)  [since rho_+ <= 2]")
print("  (ii) c = (rho_-+rho_+)/2 <= 1  <=>  rho_-+rho_+ <= 2  <=>  rho_+^2-2rho_++(1-r^2) <= 0")
print("       <=> rho_+ in [1-r, 1+r], its defining interval          [true]")
print()
print("explicit check of (i) at the extreme when rho_+ is maximal:")
for r in [mpf('0.38')]:
    rp = 1 + r
    print("  r=%.2f rho_+=1+r=%.12f: 2rho_-(1-r^2) = %.12f >= %.12f ? %s"
          % (r, rp, 2*(1-r*r)/rp, 1-r*r, 2*(1-r*r)/rp >= 1-r*r))
print()
print("=== bridge constants ===")
R = mpf(19)/50
print("2 asin(19/50) =", mp.nstr(2*asin(R), 15), " < pi/2 :", 2*asin(R) < pi/2)
print("8 asin(19/50) =", mp.nstr(8*asin(R), 15), " < pi   :", 8*asin(R) < pi)
print("arc half-width asin(r) for r<1 means arc length 2asin(r) < pi:", 2*asin(R) < pi)
