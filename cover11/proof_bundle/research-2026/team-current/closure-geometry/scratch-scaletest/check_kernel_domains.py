from mpmath import mp, sqrt, acos, mpf

mp.dps = 25
R = mpf(19)/50
print("R =", R, " 2R =", 2*R)
print("1-R =", 1-R, " 1+R =", 1+R)
print("3R-1 =", 3*R-1, " = 196/625 ?", 3*R-1 == mpf(196)/625, " = 7/50 ?", 3*R-1 == mpf(7)/50)
print()
print("=== kernel A: ell^2 = rho^2+e^2-2*rho*e*cos(phi) over the certified domain ===")
print("    rho in [0.62,1.38] (clip), e in [0,0.14], cos(phi) in [-1,1]")
best = None
for i in range(0, 77):
    rho = mpf('0.62') + (mpf('1.38')-mpf('0.62'))*i/76
    for j in range(0, 15):
        e = mpf('0.14')*j/14
        for cp in [mpf(-1), mpf(0), mpf(1)]:
            v = rho*rho + e*e - 2*rho*e*cp
            if best is None or v < best[0]:
                best = (v, rho, e, cp)
print("  min ell^2 found:", mp.nstr(best[0], 18), " at rho=%s e=%s cos(phi)=%s" %
      (mp.nstr(best[1], 6), mp.nstr(best[2], 6), mp.nstr(best[3], 4)))
print("  code floor '0.2304' vs true min:", mpf('0.2304') <= best[0],
      " (floor is a valid lower bound AND not binding: %s)" % (best[0] >= mpf('0.2304')))
print("  computed clip argument: rho^2+e^2+2*rho*e >= %.6f ; rho^2+e^2-2*rho*e >= %.6f"
      % (mpf('0.62')**2 + mpf('0.38')**2, mpf('0.62')**2))
print()
print("=== kernel A: the (2R) comparison uses lo(ell) >= hi(2R) ===")
print("  ell^2 >= 2.02 > 4R^2 = %.6f  -> ell > 2R, inner term skipped legitimately" % (4*R*R))
print()
print("=== kernel B (t,v,e,sgn) : same ell identity ===")
print("  ell^2 = (rho-e)^2 + 2*rho*e*(1-v), rho = cos t +- sqrt(R^2-sin^2 t), v in [-1,1]")
worst = None
for sgn in (1, -1):
    for i in range(0, 40):
        t = mp.asin(R)*i/39
        rho = mp.cos(t) + sgn*sqrt(max(0, R*R - mp.sin(t)**2))
        for j in range(15):
            e = mpf('0.14')*j/14
            for v in [mpf(-1), mpf(0), mpf(1)]:
                val = (rho-e)**2 + 2*rho*e*(1-v)
                if worst is None or val < worst[0]:
                    worst = (val, sgn, t, rho, e, v)
print("  min ell^2 =", mp.nstr(worst[0], 18), " sgn=%d t=%s rho=%s e=%s v=%s"
      % (worst[1], mp.nstr(worst[2], 6), mp.nstr(worst[3], 8), mp.nstr(worst[4], 6), mp.nstr(worst[5], 4)))
print("  rho range reached:", mp.nstr(mp.cos(mp.asin(R)) - sqrt(max(0, R*R-mp.sin(mp.asin(R))**2)), 8),
      "to", mp.nstr(mp.cos(0)+R, 8), " (compare clip [0.62,1.38])")
print()
print("=== beta domain check (both kernels assert beta >= 0.6) ===")
print("  worst case ell -> 0: cos psi = dx/ell in [-1,1]; if ell=0 then dx<0 forced?")
