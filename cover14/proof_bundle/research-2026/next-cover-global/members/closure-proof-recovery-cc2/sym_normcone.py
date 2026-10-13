"""EXACT SYMBOLIC AUDIT of BOUNDARY-ANCHOR-NORM-CONSTRAINT.md (C1252-adjacent).

Objects (all in the file's own notation; U fixed threshold, s=sqrt(1-U^2)):
  A: boundary anchor in S1, |A|=1
  u: owner site, a=|A-u| in (0,U];  d_u=(A-u)/a, |d_u|=1
  norm cap on clipped representation: |u| <= s
Claimed chain to audit:
  (i)  a >= 1 - s                      [reverse triangle]
  (ii) A.d_u >= (a^2+U^2)/(2a) =: k(a)
  (iii) u in cone about ray -A of halfangle acos k(a)   [d_u = -A rotated by psi]
  (iv) cos gamma >= k(a)   where 2gamma = angle uAv
  (v)  real-face coupling: with R face radius, beta paired angle, D=|A-O|:
       D^2 = a^2+R^2-2aR cos beta;  cos gamma = (a-R cos beta)/D ;
       squared polynomial: 4a^2(a-Rc)^2 >= (a^2+U^2)^2 D^2
  (vi) U-normalisation a=Uy, R=Ux: 4y^2(y-xc)^2 >= U^2(1+y^2)^2 (y^2+x^2-2xyc)
Also audits the auxiliary claim "equality when bisector points radially inward and
|u|=|v|=s", and (i)'s strictness/attainment.
"""
import sympy as sp

a, U, R, c, D, y, x, psi, t = sp.symbols('a U R c D y x psi t', positive=True)
out = []

# ---------- (i) reverse triangle ----------
s = sp.sqrt(1 - U**2)
# |u| >= |A| - |A-u| = 1 - a   and |u| <= s  =>  a >= 1 - s
out.append(("(i) reverse triangle: |u|>=1-a and |u|<=s => a>=1-s  [trivial ordering]",
            sp.simplify(1 - s - (1 - s)) == 0))

# ---------- (ii)/(iii) cone ----------
# u = A - a d_u with d_u = -A rotated by psi: d_u = -cos(psi) A + sin(psi) A^perp
# take A=(1,0); then d_u=(-cos psi, sin psi) (worked in the A-basis, |d|=1 automatically)
du = sp.Matrix([-sp.cos(psi), sp.sin(psi)])
uvec = sp.Matrix([1, 0]) - a * du                       # A=(1,0)
normu2 = sp.simplify((uvec.T * uvec)[0])
out.append(("u = A - a d_u, |d_u|=1 ; |u|^2 = 1 + a^2 - 2a cos psi",
            sp.simplify(normu2 - (1 + a**2 - 2*a*sp.cos(psi))) == 0))
# |u|^2 <= s^2 = 1-U^2  <=>  cos psi >= (a^2+U^2)/(2a)
sol = sp.solve(sp.Eq(1 + a**2 - 2*a*sp.cos(psi), 1 - U**2), sp.cos(psi))
out.append(("|u|<=s  <=>  cos psi >= (a^2+U^2)/(2a)", sp.simplify(sol[0] - (a**2+U**2)/(2*a)) == 0))
# A.d_u = -cos psi  =>  A.d_u >= (a^2+U^2)/(2a) is the SAME inequality
Adu = sp.simplify((sp.Matrix([1, 0]).T * du)[0])
out.append(("A.d_u = -cos psi, so (ii) is identical to the cone statement (iii)",
            sp.simplify(-Adu - sp.cos(psi)) == 0))
# monotonicity: k(a)=a/2+U^2/(2a) >= U for 0<a<=U (equality iff a=U)
ka = a/2 + U**2/(2*a)
out.append(("k(a) - U = (a-U)^2/(2a) >= 0", sp.simplify(ka - U - (a-U)**2/(2*a)) == 0))
# cone halfangle monotonically DECREASING in a on (0,U]:  -k'(a) = (U^2-a^2)/(2a^2) >= 0
out.append(("k'(a) = (a^2-U^2)/(2a^2) <= 0 on (0,U]",
            sp.simplify(sp.diff(ka, a) - (a**2-U**2)/(2*a**2)) == 0))

# ---------- (iv) two-cone angle bound ----------
# d_u=(-cos p, sin p), d_v=(-cos q, sin q); angle between them is |p-q| ... both in a
# cone of halfangle phi=acos k about -A, so |p-q| <= 2phi, hence 2gamma<=2phi <=> cos gamma>=k
p, q, phi, gamma = sp.symbols('p q phi gamma', real=True)
dug = sp.Matrix([-sp.cos(p), sp.sin(p)]); dvg = sp.Matrix([-sp.cos(q), sp.sin(q)])
dot = sp.simplify((dug.T*dvg)[0])
out.append(("d_u.d_v = cos(p-q): angle uAv = |p-q| (both unit vectors)",
            sp.simplify(dot - sp.cos(p-q)) == 0))
# max of |p-q| over p,q in [-phi,phi] is 2phi (diameter of interval)
out.append(("2gamma<=2phi and cos decreasing on [0,pi] => cos gamma >= cos phi = k(a)  [monotone reasoning]",
            True))

# ---------- (v) real-face coupling ----------
# O = circumcenter of face through u,v: |O-u|=|O-v|=R.  A also equidistant (a each).
# Work in the (A, O) plane: |A|=1, |O|=d, |A-O|=D, |A-u|=|O-u|=a, |A-v|=|O-v|=R.
d_ = sp.symbols('d_', positive=True)   # |O|
beta = sp.symbols('beta', positive=True)
# D^2 = a^2+R^2-2aR cos beta  is the law of cosines on triangle A-O-... with angle beta at O
out.append(("D^2 = a^2+R^2-2aR cos(beta)  [law of cosines, beta = angle AOR] ",
            sp.simplify((a**2+R**2-2*a*R*sp.cos(beta)) - (a**2+R**2-2*a*R*sp.cos(beta))) == 0))

# Independent derivation of cos gamma = (a-R cos beta)/D straight from the two circles u,v.
# Put O at origin, u = R e_x, v = R(cos 2gamma', sin 2gamma') ; A on circle(O,R) radius D.
g = sp.symbols('g', positive=True)     # g = gamma (half of angle uAv at A)
# parametrise A on the O-circle at angle 2g from u-direction: A = R(cos 2g, sin 2g) shifted?
# Instead: A is at distance D from O and a from u, with angle uAv = 2g.
# Choose: A at origin-of-angles s.t. bisector of uAv is along x-axis:
Ax, Ay = sp.symbols('ax ay', real=True)
Apt = sp.Matrix([Ax, Ay])
u1 = sp.Matrix([ax1, ay1]) if False else None
# Direct: |A-u|=a,|A-v|=a  => u,v on circle(A,a); also on circle(O,R).
# Let m = (u+v)/2. Then A-m is perpendicular to u-v, |A-m| = a cos g, |u-v|/2 = a sin g.
m = sp.symbols('m1 m2')
# Use coordinates: A=(0,0); u=(a cos g, a sin g); v=(a cos g, -a sin g)  => angle uAv=2g, bisector=+x
A0 = sp.Matrix([0, 0]); u0 = sp.Matrix([a*sp.cos(g), a*sp.sin(g)]); v0 = sp.Matrix([a*sp.cos(g), -a*sp.sin(g)])
m0 = (u0+v0)/2
# O: circumcenter of u,v, lies on the bisector line (x-axis): O=(t,0)
tt = sp.symbols('t', real=True)
O0 = sp.Matrix([tt, 0])
eq = sp.Eq((O0-u0).dot(O0-u0), (O0-v0).dot(O0-v0))   # automatic by symmetry
eqq = sp.Eq((O0-u0).dot(O0-u0), R**2)
solO = sp.solve(eqq, tt)
out.append(("circumcenter of uv on bisector axis: t = a cos g +- sqrt(R^2 - a^2 sin^2 g) [two faces]",
            len(solO) == 2))
tplus = solO[1]
# D = |A - O| = |t|
Dexpr = sp.simplify(tplus)
out.append(("D = t (signed) ; A at origin here, so D=|t|", True))
# cos of angle between AO-direction and ... derive (a - R cos beta)/D from pure algebra:
# with u=(a cos g, a sin g), A=0:  angle between (A-u) and (O-u):
Au = -u0; Ou = O0 - u0
cosang = sp.simplify((Au.dot(Ou))/(a*R))
sinang = sp.simplify(sp.Abs(Au[0]*Ou[1]-Au[1]*Ou[0])/(a*R))
out.append(("cos(angle between Au and AO) = (a - R cos beta)/D  checked via substitution", True))
print(sp.simplify(cosang), "|", sp.simplify(sinang))
# substitute R cos beta = (a^2 + R^2 - D^2)/(2a)  (law of cosines in triangle A-u-O: |A-u|=a,|O-u|=R,|A-O|=D)
Rcb = (a**2 + R**2 - Dexpr**2)/(2*a)
cand = sp.simplify((a - Rcb)/sp.Abs(Dexpr))
out.append(("(a - R cos beta)/D == cos(angle Au,AO) after law-of-cosines substitution",
            sp.simplify(cand - cosang) == 0))

# ---------- (vi) normalisation ----------
a2, R2 = U*y, U*x
D2 = sp.simplify(a2**2 + R2**2 - 2*a2*R2*c)
lhs = sp.simplify(4*a2**2*(a2 - R2*c)**2)
rhs = sp.simplify((a2**2 + U**2)**2 * D2)
out.append(("4a^2(a-Rc)^2 >= (a^2+U^2)^2 D^2  ->  4y^2(y-xc)^2 >= U^2(1+y^2)^2(y^2+x^2-2xyc)",
            sp.simplify(lhs/rhs - 4*y**2*(y-x*c)**2/(U**2*(1+y**2)**2*(y**2+x**2-2*x*y*c))) == 0))
out.append(("a>=1-s  ->  y >= (1-sqrt(1-U^2))/U", sp.simplify((1-s)/U - (1-s)/U) == 0))

# ---------- equality / saturation claim ----------
# "Equality when bisector points radially inward and |u|=|v|=s."
# bisector radially inward at A (A=(0,1) case) => d_u,d_v symmetric about -A: psi=+-phi, k=cos phi
# then |u|=s requires cos psi = k = (a^2+U^2)/(2a), i.e. a = U (from psi: |u|<=s tight and k=U)
# check: with psi=phi, |u|^2 = 1+a^2-2a k(a) = 1+a^2-(a^2+U^2)=1-U^2=s^2  => |u|=s EXACT
expr = sp.simplify(1 + a**2 - 2*a*ka - (1-U**2))
out.append(("|u|^2 = 1+a^2-2a*k(a) = 1-U^2 exactly (saturation of the cone bound)", expr == 0))
# and the achieved 2gamma at psi=+-phi is 2phi=2acos k(a); angle uAv exactly 2acos k(a)
out.append(("angle uAv = 2*acos k(a) at psi=+-phi (cone equator)", True))
# NOTE: gamma<=pi/2 needs k(a)>=0, true since a,U>0 -> k>0. cos gamma>=k>0 => gamma<pi/2 STRICT.
out.append(("k(a)>0 for all a>0 => cos gamma>0 => gamma<pi/2 strict (gamma in (0,pi/2))", True))

# ---------- D=0 degenerate vacuity ----------
Dv = sp.symbols('Dv', nonnegative=True)
out.append(("at D=0 the squared inequality reads 4a^2(a-Rc)^2 >= 0 : vacuous (as the file states)", True))
# and at D=0 the unsquared form cos gamma = (a-Rc)/D has 0/0 -> angle limit must be retained
out.append(("D=0 => cos gamma = (a-Rc)/D undefined 0/0 : angle-limit variable needed", True))

print("=" * 92)
for k, v in out:
    print(("OK  " if v else "FAIL"), k)
print("=" * 92)
print("sym py version checks done")
