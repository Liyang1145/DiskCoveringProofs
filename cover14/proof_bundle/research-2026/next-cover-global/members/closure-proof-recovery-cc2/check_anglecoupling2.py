"""Independent (non-Voronoi) geometric check of the real-face angle coupling (v).

Construction: A=(0,0); u=a(cos g, sin g); v=a(cos g,-sin g) so |Au|=|Av|=a and angle uAv=2g.
Circumcircle of {A,u,v}: centre O on the y-axis  y_O = (1 - a^2)/(2 a sin g) (A at origin, |A|=1
means O is at distance 1 from A; more generally take the circle through A,u,v and R its radius).
Everything below is exact circle geometry, no Voronoi needed.
Then:  R=|O-u|, D=|A-O|, beta=angle(A-O, u-O)  [at O]
   law-of-cosines:  D^2 = a^2 + R^2 - 2aR cos beta   must hold EXACTLY
   file's formula :  cos(angle uAv-bisector piece) = (a - R cos beta)/D
Audit: does (a-R cos beta)/D equal cos of the angle between Au and AO, with the correct branch?
"""
import math

def case(a, g):
    # circle through A=(0,0), u, v with circumradius R: centre on x=... use standard formula
    Ux, Uy = a*math.cos(g), a*math.sin(g)
    Vx, Vy = a*math.cos(g), -a*math.sin(g)
    # circumcentre of (A,u,v): solve x*Ux + y*Uy = |u|^2/2 ; x*Vx+y*Vy=|v|^2/2
    d = Ux*Vy - Uy*Vx
    r1 = (a*a)/2; r2 = (a*a)/2
    Ox = (r1*Vy - Uy*r2)/d; Oy = (Ux*r2 - r1*Vx)/d
    R = math.hypot(Ox, Oy)          # |O - A|
    D = R                            # |A-O|
    cb = ((0-Ox)*(Ux-Ox) + (0-Oy)*(Uy-Oy))/(D*R)
    lhs = (a - R*cb)/D
    # true: angle between (u-A) and (O-A):  (u-A)=(Ux,Uy), (O-A)=(Ox,Oy)
    true = (Ux*Ox + Uy*Oy)/(a*D)
    law = D*D - (a*a + R*R - 2*a*R*cb)
    return dict(a=a, g=g, R=R, D=D, cosbeta=cb, lawresid=law, file_formula=lhs, true_cos=true, diff=lhs-true)

print("--- circle-through-A,u,v geometry: is (a-R cos beta)/D = cos(angle uA, AO) ? ---")
for (a, g) in [(0.9, 0.5), (0.3, 0.9), (0.99, 0.2), (0.5, 1.2), (0.35, 1.0)]:
    r = case(a, g)
    print({k: (round(v, 12) if isinstance(v, float) else v) for k, v in r.items()})

print()
print("--- SATURATION construction, U=1/3: A on unit circle, |u|=|v|=s, angle uAv=2 acos(k(U)) ---")
U = 1/3; s = math.sqrt(1-U*U); ka = (U*U + U*U)/(2*U)   # k(a=U) = U
psi = math.acos(ka)
A = (0.0, 1.0)
u = (s*math.cos(psi), s*math.sin(psi)); v = (s*math.cos(-psi), s*math.sin(-psi))
def d(p, q): return math.dist(p, q)
a = d(A, u)
gam = math.acos(( (u[0]-A[0])*(v[0]-A[0]) + (u[1]-A[1])*(v[1]-A[1]) )/(a*a))/2
print("a=%.15f  U=%.15f   |u|=%.15f  s=%.15f" % (a, U, d((0,0), u), s))
print("angle uAv/2 = gamma = %.15f     acos k(a) = %.15f    cos gamma - k(a) = %.3e"
      % (gam, math.acos((a*a+U*U)/(2*a)), math.cos(gam) - (a*a+U*U)/(2*a)))
print("|v|=%.15f ; |A-v|=%.15f" % (d((0,0), v), d(A, v)))
# circumcircle of A,u,v
Ux, Uy = u; Vx, Vy = v
d1 = Ux*Vy - Uy*Vx; r1 = a*a/2
Ox = (r1*Vy - Uy*r1)/d1; Oy = (Ux*r1 - r1*Vx)/d1
print("circumcentre O=(%.15f,%.15f)  R=|O-A|=%.15f   |O-u|=%.15f |O-v|=%.15f"
      % (Ox, Oy, math.hypot(Ox, Oy), d((Ox, Oy), u), d((Ox, Oy), v)))
# "bisector radially inward"?  m=(u+v)/2 should be parallel to -A i.e. A-m radial
mx, my = (u[0]+v[0])/2, (u[1]+v[1])/2
print("m=(%.15f,%.15f) ; A-m=(%.15f,%.15f) parallel to A? cross=%.3e ; |m|^2=%.15f vs 1+a^2-2a cos g=%.15f"
      % (mx, my, A[0]-mx, A[1]-my, (A[0])*my - (A[1])*mx, mx*mx+my*my, 1+a*a-2*a*math.cos(gam)))
print("CHECK minimal-max-norm closed form: 1+a^2-2a cos gamma = %.15f   max(|u|^2,|v|^2)=%.15f"
      % (1+a*a-2*a*math.cos(gam), max(u[0]**2+u[1]**2, v[0]**2+v[1]**2)))
print()
print("--- lower end: a = 1-s (reverse-triangle equality), U=1/3 ---")
alow = 1 - s
print("a=1-s=%.15f ; k(a)=%.15f ; k(a)>=U? %s" % (alow, (alow*alow+U*U)/(2*alow), (alow*alow+U*U)/(2*alow) >= U))
print("2 acos k(a) = %.15f (rad) ; gamma_min = %.15f" % (2*math.acos((alow*alow+U*U)/(2*alow)), math.acos((alow*alow+U*U)/(2*alow))))
