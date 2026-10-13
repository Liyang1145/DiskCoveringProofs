# -*- coding: utf-8 -*-
"""Audit of lead/HUB-CONVEX-LENS-REDUCTION.md + CARTESIAN-HUB-DISK-INTERSECTION.md.

Exact algebra only (sympy) plus a few exact-rational inequalities. No numeric grids.
Checks:
 (1) face constraint H <= 2r sin(2b1-delta)  <=>  disk (v-r sin2b1)^2+(t+r cos2b1)^2 <= r^2
 (2) same for the second face; both centres have norm r  =>  H <= 2r automatic
 (3) norm constraint <=> disk (v-s)^2+t^2 <= (1-r)^2
 (4) separation H^2 >= 2r|t| <=> the two disk exteriors v^2+(t-+r)^2 >= r^2
 (5) redundancy: hub disk => both exteriors (exact reverse-triangle argument)
 (6) centre distance^2 of the two face circles = 4 r^2 cos^2 T ; intersections = 0 and 2M
 (7) v >= s-(1-r) > 4r/5 on r in [3/8,19/50] (exact rational comparison)
 (8) fixed-v chord intervals
"""
import sympy as sp
lines = []
def P(*a):
    s = " ".join(str(x) for x in a); lines.append(s); print(s)

r, v, t, b1, b2, d = sp.symbols('r v t b1 b2 delta', real=True)
s_ = sp.sqrt(1-r**2); H = sp.sqrt(v**2+t**2)
sT = sp.sin(2*b1-d)            # face-1 upper bound (works with v,t independent here)
# (1)/(2): face disks.  Substitute v = H cos d, t = H sin d to compare the two statements.
subs = {v: H*sp.cos(d), t: H*sp.sin(d)}
lhs1 = sp.expand((H**2 - 2*r*H*sp.sin(2*b1-d)).subs(H, sp.sqrt(v**2+t**2)))
disk1 = (v - r*sp.sin(2*b1))**2 + (t + r*sp.cos(2*b1))**2 - r**2
P("(1) face-1:  H^2 <= 2rH sin(2b1-d)  <->  disk1 <= 0")
P("    difference (after substituting v=Hcos d, t=Hsin d):",
  sp.simplify(sp.expand(disk1.subs(subs) - (v**2+t**2 - 2*r*H*sp.sin(2*b1-d)).subs(subs))))
disk2 = (v - r*sp.sin(2*b2))**2 + (t - r*sp.cos(2*b2))**2 - r**2
P("(2) face-2:  H^2 <= 2rH sin(2b2+d)  <->  disk2 <= 0")
P("    difference:",
  sp.simplify(sp.expand(disk2.subs(subs) - (v**2+t**2 - 2*r*H*sp.sin(2*b2+d)).subs(subs))))
P("    centres:", sp.simplify(sp.sqrt((r*sp.sin(2*b1))**2 + (r*sp.cos(2*b1))**2)),
  ",", sp.simplify(sp.sqrt((r*sp.sin(2*b2))**2 + (r*sp.cos(2*b2))**2)),
  " => |c9-c2| = H <= |c9-C| + |C-c2| <= r + r = 2r")
P("(3) norm constraint: (s-v)^2 + t^2 <= (1-r)^2 :",
  sp.simplify(sp.expand((s_-v)**2 + t**2 - (1-r)**2) -
              sp.expand((s_**2 - 2*s_*v + v**2 + t**2) - (1-2*r+r**2))))
P("    and equals  H^2 - 2sH cos d + 2r(1-r) <= 0  under v=Hcos d,t=Hsin d :",
  sp.simplify(sp.expand((s_-v)**2 + t**2 - (1-r)**2 - (H**2 - 2*s_*H*sp.cos(d) + 2*r*(1-r))).subs(subs)))
P("(4) separation: H^2 >= 2r|t|  <->  v^2 + (|t|-r)^2 >= r^2  <->  v^2+(t-r)^2>=r^2 and v^2+(t+r)^2>=r^2")
P("    check the min of the two disk-exterior left sides minus r^2:",
  sp.simplify(v**2 + (sp.Abs(t)-r)**2 - r**2 - (v**2+t**2-2*r*sp.Abs(t))), "(=0)")
P("")
P("(5) REDUNDANCY (exact): for X=(v,t) with |X-(s,0)| <= 1-r,")
P("    |X-(0,+-r)| >= |(0,+-r)-(s,0)| - |X-(s,0)| >= 1 - (1-r) = r,")
P("    since |(0,+-r)-(s,0)| = sqrt(s^2+r^2) = 1 and |0-1| = 1 = (1-r)+r (external tangency).")
P("    => the two exteriors hold automatically; tangency point on the centre line:")
P("    (s,0) + (1-r)*((0,r)-(s,0))/1 = ", sp.simplify(sp.Matrix([s_-s_*(1-r), r*(1-r)])),
  " = (r s, r(1-r))")
P("")
P("(6) face-circle centres C1=(r sin2b1,-r cos2b1), C2=(r sin2b2, r cos2b2):")
T_, D_ = sp.symbols('T D', real=True)
C1 = sp.Matrix([r*sp.sin(T_+D_), -r*sp.cos(T_+D_)]); C2 = sp.Matrix([r*sp.sin(T_-D_), r*sp.cos(T_-D_)])
dist2 = sp.simplify(sp.expand((C1-C2).dot(C1-C2)))
P("    |C1-C2|^2 - 4r^2 cos^2 T n :", sp.simplify(dist2 - 4*r**2*sp.cos(T_)**2))
M = sp.simplify((C1+C2)/2)
P("    midpoint M = C1+C2)/2 :", M.T, "  |M|^2 - r^2 sin^2 T :", sp.simplify(M.dot(M) - r**2*sp.sin(T_)**2))
P("    radical axis: |X-C1|^2-|X-C2|^2 = 2X.(C2-C1) = 0 (|C1|=|C2|=r), so it passes through 0;")
P("    hence intersections are 0 and 2M = C1+C2 = (2r sinT cosD, 2r sinT sinD):")
P("    2M - C1 - C2 :", sp.simplify((2*M - C1 - C2).T))
P("    at T=pi/2: cos T=0 => |C1-C2|=0 (centres coincide) => the two face disks are IDENTICAL")
P("    (indeed sin2b1=sin2b2, cos2b1=-cos2b2 when b1+b2=pi/2).")
P("")
P("(7) v >= s-(1-r) > 4r/5 on r in [3/8,19/50]:")
f = lambda x: sp.sqrt(1-x**2) - 1 + x - 4*x/5
P("    f(r) = sqrt(1-r^2) - 1 + r/5 ; f(3/8) = %s = %.8f" % (sp.nsimplify(f(sp.Rational(3,8))), float(f(sp.Rational(3,8)))))
P("    f(19/50) = %s = %.8f" % (sp.nsimplify(f(sp.Rational(19,50))), float(f(sp.Rational(19,50)))))
P("    f'(r) = -r/sqrt(1-r^2) + 1/5 < 0 on [3/8,19/50] (since r/sqrt(1-r^2) >= 0.404 > 0.2),")
P("    so f is DECREASING: min at r=19/50, f = %.8f > 0" % float(f(sp.Rational(19,50))))
P("    exact: f(19/50) = sqrt(2139)/50 - 81/100 > 0  <=>  2 sqrt(2139) > 81  <=>  8556 > 6561  TRUE")
P("")
P("(8) fixed-v chord intervals (from the three disks):")
P("    t in -r cos2b1 +- sqrt(r^2-(v-r sin2b1)^2);  t in r cos2b2 +- sqrt(r^2-(v-r sin2b2)^2);")
P("    t in +- sqrt((1-r)^2-(v-s)^2)   [each empty if the radicand is negative]; the three are")
P("    closed intervals, their intersection is one closed interval (possibly empty).")

import pathlib
outp = pathlib.Path(__file__).resolve().parent.parent / 'out' / 'p37_hub_disk_audit.txt'
with open(outp, 'w', encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
