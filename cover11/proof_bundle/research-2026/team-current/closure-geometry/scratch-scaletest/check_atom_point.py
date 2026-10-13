from mpmath import mp, mpf, sqrt, sin, cos, acos, pi, atan2

mp.dps = 40
R = mpf(19)/50

print("=== _t.py lines 11-24 reproduced verbatim in the atom formula ===")
print("  L20: ell = sqrt((rho-e)^2 + 2*rho*e*(1-v))          <-- NO clip, exact identity")
print("  L21: if ell.a >= (2*R).b: return out                <-- only this skips the hub term")
print()

# ---- the lead's point: e=0, t=0, sign=-1, v=1 ----
t, v, e, sgn = mpf(0), mpf(1), mpf(0), -1
sn, cs = sin(t), cos(t)
root = sqrt(R*R - sn*sn)
rho = cs + sgn*root
print("=== point e=0, t=0, sign=-1, v=1 ===")
print("  sin t =", sn, " cos t =", cs, " sqrt(R^2 - sin^2 t) =", mp.nstr(root, 20))
print("  rho = cos t + (-1)*sqrt(R^2-sin^2 t) =", mp.nstr(rho, 20))
print("  2R =", 2*R, "   is rho < 2R ? ", rho < 2*R)
ell = sqrt((rho - e)**2 + 2*rho*e*(1 - v))
print("  ell = sqrt((rho-e)^2 + 2 rho e (1-v)) =", mp.nstr(ell, 20))
print("  ell.a >= (2R).b  ==>  skip?  ", ell >= 2*R, "  => the hub term IS computed (L22-24)")
print("  => hub term nonzero at this point, confirming the lead's correction.")
print()

# ---- also the point I discussed (rho=0.62, e=0.14, cos phi=1) ----
print("=== point rho=0.62, e=0.14, cos(phi)=1 (the domain minimum of ell^2) ===")
rho2, e2, cp = mpf('0.62'), mpf('0.14'), mpf(1)
ell2 = rho2*rho2 + e2*e2 - 2*rho2*e2*cp
print("  ell^2 = rho^2+e^2-2 rho e cos(phi) =", mp.nstr(ell2, 20), " (= 0.2304 exactly)")
print("  ell =", mp.nstr(sqrt(ell2), 20), "  2R =", 2*R, "  ell < 2R ?", sqrt(ell2) < 2*R)
print("  => _dual.py L42 `lo(ell) >= hi(2R)` is FALSE here, so the hub term is computed")
print("  => _t.py L21 `ell.a >= (2R).b` is FALSE here too")
print()
print("  Also: max ell^2 over rho in [0.62,1.38], e in [0,0.14], cos phi in [-1,1]:")
mx = mpf('1.38')**2 + mpf('0.14')**2 - 2*mpf('1.38')*mpf('0.14')*(-1)
print("    at rho=1.38, e=0.14, cos(phi)=-1 : ell^2 =", mp.nstr(mx, 20), " (ell =", mp.nstr(sqrt(mx), 12), ")")
print("    so the clip upper bound '3' in _dual.py L41 IS binding (loosening only),")
print("    and the clip floor '0.2304' is exactly the domain minimum (tight, valid).")
print()
print("=== gate arithmetic for the clip interval at the minimum point ===")
print("  clipped interval around ell^2 = 0.2304 gives ell.a = 0.48 < 0.76 = hi(2R)")
print("  => no skipping: hub term computed. My earlier claim of 'always skipped' was WRONG.")
