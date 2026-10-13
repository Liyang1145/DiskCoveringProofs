from mpmath import mp, sin, cos, asin, acos, sqrt, pi, mpf, atan2
mp.dps = 30

# Hub domain: three disks (radius r): two face disks with centers
#   C1 = ( r sin 2b1 , 2r sin^2 b1 )  [a boundary point of the r-disk at c1]
#   C2 = ( r sin 2b2 , -2r sin^2 b2 ) [ditto for c2]
# and the norm disk |X| <= 1 - r ; plus the wedge between the rays at angles
#   2b1 and pi - 2b2 (the "hub cone" centered at -e_v).
# Coordinates: v along -e_v?  Here we use X = (v, t) literally as the
# problem's (v,t) with v the "radial" coordinate (constraint v <= 1-r), t the
# tangential one, and the norm-circle  (s - v)^2 + t^2 = (1-r)^2 with s = 1-r.

def face_lines(r, b1, b2):
    # exact tangent lines through the origin bounding disks (first disk, second disk)
    # D1: v sin 2b1 - t cos 2b1 <= r(1 - cos 2b1)
    # D2: v sin 2b2 + t cos 2b2 <= r(1 - cos 2b2)
    return (r*(1-cos(2*b1)), r*(1-cos(2*b2)))

def feasible(v, t, r, b1, b2, tol=0):
    s = 1 - r
    D1 = v*sin(2*b1) - t*cos(2*b1) <= r*(1-cos(2*b1)) + tol
    D2 = v*sin(2*b2) + t*cos(2*b2) <= r*(1-cos(2*b2)) + tol
    Dn = (s-v)**2 + t*t <= s*s + tol
    return D1, D2, Dn

r = mpf('0.38')
print("r =", r, " s = 1-r =", 1-r, " 2r(1-r)/s =", 2*r*(1-r)/(1-r))
b1i = mpf(1); b2i = acos(r)
print("b1 range top = acos(r) =", b2i, " rad")
for (b1, b2) in [(mpf(1), mpf(1)), (mpf(1), mpf('1.2')), (mpf('1.2'), mpf('1.2'))]:
    l1, l2 = face_lines(r, b1, b2)
    print()
    print("b1=%.4f b2=%.4f: D1 bound=%.6f D2 bound=%.6f" % (b1, b2, l1, l2))
    print("   r(1+sin2b1)=%.6f r(1+sin2b2)=%.6f  r(1-cos2)=%.6f 2r(1-r)/s=%.6f"
          % (r*(1+sin(2*b1)), r*(1+sin(2*b2)), r*(1-cos(2)), 2*r*(1-r)/(1-r)))
    # scan the norm-circle "+" branch
    print("   far-branch scan: delta from -b2 to b1, rho = s cos d + sqrt(s^2 - s^2 sin^2 d)")
    found = []
    for i in range(0, 201):
        d = -b2 + (b1+b2)*mpf(i)/200
        disc = (1-r)**2 - (1-r)**2*sin(d)**2
        if disc < 0: continue
        rho = (1-r)*cos(d) + sqrt(disc)
        v = rho*cos(d); t = rho*sin(d)
        f = feasible(v, t, r, b1, b2, tol=mpf('1e-20'))
        if all(f): found.append((d, v, t, rho))
    print("   feasible points on far branch:", len(found))
    if found:
        print("      example:", [mp.nstr(x, 8) for x in found[0]])
