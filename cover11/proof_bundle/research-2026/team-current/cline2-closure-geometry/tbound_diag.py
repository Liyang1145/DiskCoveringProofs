from mpmath import mp, sin, cos, acos, sqrt, pi, mpf, tan, atan, atan2
mp.dps = 30
r = mpf(19)/50
s = sqrt(1-r*r)
b1 = mpf(1); b2 = acos(r)

print("DN disk: center (s,0) radius 1-r =", 1-r, "; so max|t| on DN alone = 1-r =", 1-r)
print("D1 disk: center (%.9f, %.9f) radius r; max|t| on D1 alone = r(1+|cos2b1|) = %.6f"
      % (r*sin(2*b1), -r*cos(2*b1), r*(1+abs(cos(2*b1)))))
print("D2 disk: center (%.9f, %.9f) radius r; max|t| = %.6f"
      % (r*sin(2*b2), r*cos(2*b2), r*(1+abs(cos(2*b2)))))
print()
print("so DN is not the t-limiter; check the wedge + D1 apex:")
# tangent line from origin to D1: t = v tan b1 ; tangency point
vtan = r*sin(2*b1) + r*cos(2*b1)*tan(b1)   # from distance formula
ttan = vtan*tan(b1)
print("  D1 tangency point: v=%.9f t=%.9f  |t|=%.9f" % (vtan, ttan, abs(ttan)))
print()
print("observed max|t| = 0.221863847 at v = 0.346053;  compare r(1-sin2) =", r*(1-sin(2)))
print("  r(1+cos2) =", r*(1+cos(2)), "  r(1-cos2) =", r*(1-cos(2)))
print()
print("check: is (0.346053, 0.221863847) on a disk boundary?")
for (cx, cy, rr, nm) in [(r*sin(2*b1), -r*cos(2*b1), r, 'D1'), (r*sin(2*b2), r*cos(2*b2), r, 'D2'), (s, mpf(0), 1-r, 'DN')]:
    dst = (mpf('0.346053')-cx)**2 + (mpf('0.221863847')-cy)**2
    print("   %s: dist^2=%.9f  r^2=%.9f  on boundary=%s" % (nm, dst, rr*rr, abs(dst-rr*rr) < mpf('1e-7')))
print()
print("wedge value at that point: v tan b1 = %.9f  (t/v = %.9f = tan %.9f)" %
      (mpf('0.346053')*tan(b1), mpf('0.221863847')/mpf('0.346053'), atan(mpf('0.221863847')/mpf('0.346053'))))
print("tan b1 = %.9f ;  b2 = %.9f ; tan(pi/2 - 2 + ... ) ..." % (tan(b1), b2))
