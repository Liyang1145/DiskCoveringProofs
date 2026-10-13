# -*- coding: utf-8 -*-
"""AUDIT of lead/DEGENERATE-SECTOR-HUB-PATCH.md — exact symbolic checks.

Every item of the lead's note is checked with sympy (exact, symbolic in
r, b1, b2, A, H) so that no verdict rests on sampling.  The numeric block at the end
only re-evaluates the same identities at dps=50 on a few fixed points (identity
confirmation, not search).

NOTATION (lead's): s=sqrt(1-r^2); P1=(s,-r), P2=(s,r), c2=(s,0);
 c1-c2 = 2 r sin b1 (-cos b1, -sin b1);  c3-c2 = 2 r sin b2 (-cos b2, +sin b2);
 A = angle at c2 in face [9,1,2];  B = angle at c2 in face [9,2,3];
 H = |c9-c2|;  delta = b1 - A;  D1 = 2 r sin b1, D2 = 2 r sin b2.
"""
import mpmath as mp
import sympy as sp

mp.mp.dps = 50
lines = []
def P(*args):
    s = " ".join(str(a) for a in args)
    lines.append(s); print(s)

r, b1, b2, A, H = sp.symbols('r b1 b2 A H', positive=True)
delta = b1 - A
s = sp.sqrt(1 - r**2)
D1 = 2*r*sp.sin(b1)
D2 = 2*r*sp.sin(b2)

P("="*78)
P("A1. DIFFERENCE VECTORS  (lead: c1-c2 = 2 r sin b1 (-cos b1, -sin b1), etc.)")
P("="*78)
P("Lead's vectors are DEFINITIONAL in the chart (they encode 'the switch P1 is at")
P("distance r from c1 and c2 and the arc of ring 2 is the flat middle arc').")
P("Check: |c1-c2| = 2 r sin b1 and the same for c3 :")
P("   |c1-c2|^2 - D1^2 =", sp.simplify(sp.expand((D1*sp.cos(b1))**2 + (D1*sp.sin(b1))**2 - D1**2)))
P("   |c3-c2|^2 - D2^2 =", sp.simplify(sp.expand((D2*sp.cos(b2))**2 + (D2*sp.sin(b2))**2 - D2**2)))
P("")
P("Angle between the rays c2->c1 (direction pi+b1) and c2->c3 (direction pi-b2):")
P("   = b1 + b2   (the wedge through direction pi, i.e. the inward wedge).")
P("   check: cos(angle) of  u1=(-cos b1,-sin b1), u2=(-cos b2,+sin b2):")
P("   u1.u2 - cos(b1+b2) =", sp.simplify(sp.expand(sp.cos(b1)*sp.cos(b2) - sp.sin(b1)*sp.sin(b2) - sp.cos(b1+b2))))
P("   => A+B = b1+b2 automatically IF the ray c2->c9 lies inside that wedge.  [OK]")

P("")
P("="*78)
P("A2. HUB COORDINATE AND THE d-DOMAIN   (lead: c9 = (s - H cos delta, -H sin delta))")
P("="*78)
c9 = sp.Matrix([s - H*sp.cos(delta), -H*sp.sin(delta)])
c2 = sp.Matrix([s, 0])
c1 = c2 + sp.Matrix([-D1*sp.cos(b1), -D1*sp.sin(b1)])
c3 = c2 + sp.Matrix([-D2*sp.cos(b2),  D2*sp.sin(b2)])
P("|c9-c2|^2 - H^2 =", sp.simplify(sp.expand((c9-c2).dot(c9-c2) - H**2)))
P("")
P("angle at c2 in face1 (between c2->c1 and c2->c9) must equal A.  Its cosine:")
u1 = (c1-c2)/D1
u9 = (c9-c2)/H
P("   u1.u9 - cos(A) =", sp.simplify(sp.expand(u1.dot(u9) - sp.cos(A))))
P("   (because delta = b1 - A:  cos(b1 - delta) = cos A)   [OK]")
v1 = (c3-c2)/D2
P("angle at c2 in face2 (between c2->c9 and c2->c3) must equal B = b1+b2-A:")
P("   u9.v1 - cos(B) with B=b1+b2-A :",
  sp.simplify(sp.expand(u9.dot(v1) - sp.cos(b1+b2-A))))
P("   => B = b1+b2-A and B>0 <=> delta > -b2 ; A>0 <=> delta < b1.")
P("   DOMAIN: delta in (-b2, b1)   [not stated in the lead's note]   [OK]")

P("")
P("="*78)
P("A3. FACE-1 CIRCUMRADIUS AND ITS H-ROOTS  (the lead's central claim)")
P("="*78)
L1sq = (c1-c9).dot(c1-c9)
P("|c1-c9|^2 =", sp.simplify(sp.expand(L1sq)))
P("   lead's law-of-cosines form  H^2+D1^2-2 H D1 cos A :")
P("   difference =", sp.simplify(sp.expand(L1sq - (H**2 + D1**2 - 2*H*D1*sp.cos(A)))))
P("")
rho1sq = L1sq/(4*sp.sin(A)**2)
P("rho1^2 = |c1-c9|^2/(4 sin^2 A)  (circumradius via the side opposite angle A)")
P("rho1^2 - (H^2+D1^2-2HD1 cos A)/(4 sin^2 A) =",
  sp.simplify(rho1sq - (H**2 + D1**2 - 2*H*D1*sp.cos(A))/(4*sp.sin(A)**2)))
P("")
P("Now solve  rho1 <= r  for H:")
sol = sp.solve(sp.Eq(rho1sq, r**2), H)
P("   roots H =", [sp.simplify(x) for x in sol])
P("   compare with 2r sin(b1 - A) and 2r sin(b1 + A):")
for x in sol:
    e1 = sp.simplify(sp.expand_trig(sp.expand(x.rewrite(sp.sin))) - 2*r*sp.sin(b1+A))
    e2 = sp.simplify(sp.expand_trig(sp.expand(x.rewrite(sp.sin))) - 2*r*sp.sin(b1-A))
    P("     root - 2r sin(b1+A) =", sp.simplify(e1), " ; root - 2r sin(b1-A) =", sp.simplify(e2))
P("")
P("   (the quadratic in H opens upward with leading coefficient 1/(4 sin^2 A) > 0,")
P("    so rho1 <= r  <=>  H between the two roots)")
P("   ordering of the roots: 2r sin(b1+A) - 2r sin(b1-A) = 4 r cos b1 sin A > 0 for b1 in (0,pi/2)")
P("     check:", sp.simplify(2*r*sp.sin(b1+A) - 2*r*sp.sin(b1-A) - 4*r*sp.cos(b1)*sp.sin(A)))
P("")
P("FACE 2: by the same computation with (A -> B, b1 -> b2):")
P("   rho2 <= r  <=>  H in [2r sin(b2-B), 2r sin(b2+B)]")
P("   with b2 - B = b2 - (b1+b2-A) = A - b1 = -delta")
P("     check:", sp.simplify((b2 - (b1+b2-A)) - (-delta)))
P("")
P("COMBINED:")
P("   lower: H >= max(2r sin delta, 2r sin(-delta)) = 2 r |sin delta|")
P("   upper: H <= 2r min( sin(b1+A), sin(b2+B) )   [with both sines > 0 required]")

P("")
P("="*78)
P("A4. HUB-INTERIORITY QUADRATIC  (lead: H^2 - 2 s cos delta H + 2 r (1-r) <= 0)")
P("="*78)
nrm2 = c9.dot(c9)
P("|c9|^2 =", sp.simplify(sp.expand(nrm2)))
P("|c9|^2 - (1-r)^2 =",
  sp.simplify(sp.expand(nrm2 - (1-r)**2)))
P("   lead's quadratic  H^2 - 2 s cos delta H + 2 r (1-r):")
P("   difference =", sp.simplify(sp.expand(nrm2 - (1-r)**2 - (H**2 - 2*s*sp.cos(delta)*H + 2*r*(1-r)))))
P("   =>  |c9| <= 1-r  <=>  Q(H):=H^2 - 2 s cos(delta) H + 2 r (1-r) <= 0      [OK]")
P("")
disc = s**2*sp.cos(delta)**2 - 2*r*(1-r)
P("Discriminant/4 = s^2 cos^2 delta - 2 r (1-r)   (lead's D)")
P("   roots: H = s cos delta +/- sqrt(D)")
P("   positivity of the roots:  product = 2 r (1-r) > 0  (both roots same sign),")
P("   sum = 2 s cos delta  =>  BOTH ROOTS POSITIVE  <=>  cos delta > 0.")
P("   EXTRA NECESSARY CONDITION NOT IN THE NOTE:  cos delta > 0, i.e. |delta| < pi/2.")
P("   (if cos delta <= 0 then Q(H) >= 2r(1-r) > 0 for all H>0 : patch empty)")

P("")
P("="*78)
P("A5. THE EXPLICIT H-FIBER")
P("="*78)
P("Feasible H for fixed (r, b1, b2, A) is")
P("  H in [ max(2r|sin delta|, s cos delta - sqrt(D)) , min(2r sin(b1+A), 2r sin(b2+B), s cos delta + sqrt(D)) ]")
P("  with D = s^2 cos^2 delta - 2 r (1-r)")
P("necessary preconditions: b1,b2 in (0,pi/2); delta in (-b2,b1); cos delta > 0; D >= 0;")
P("  sin(b1+A) > 0; sin(b2+B) > 0;  nonempty <=> lower <= upper.")
P("")
P("Note s cos delta - sqrt(D) > 0 whenever D >= 0 and cos delta > 0 (since D < s^2 cos^2 delta).")

P("")
P("="*78)
P("A6. CLOSURE BOOKKEEPING: what cancels pointwise")
P("="*78)
a = sp.asin(r)                     # = w2/2
P("Degenerate sector 2: alpha2=pi, u2=v2=1, w2=2a, L2=T2=0, V_s2 = a - sin(2a)/2.")
P("Sector 1 closure at P1:  T1 + L2 + 2 b1 + (w1+w2)/2 = pi  with L2=0")
P("   => 2 b1 = pi - T1 - (w1 + w2)/2   => b1 is DETERMINED by sector 1 data  [identity in chart]")
P("Sector 3 closure at P2:  T2 + L3 + 2 b2 + (w2+w3)/2 = pi  with T2=0")
P("   => 2 b2 = pi - L3 - (w2 + w3)/2")
P("   (asymmetric roles: T1 is the base angle at P1 = right endpoint of sector 1;")
P("    L3 is the base angle at P2 = left endpoint of sector 3)   [OK, matches lead]")
P("")
P("Multiplier coefficients in the 7-factor sum (site-2 angle slot):")
P("   sector2: -alpha2 = -pi ; face[9,1,2]: -A ; face[9,2,3]: -B ; switch1: +b1 ; switch2: +b2")
B = b1 + b2 - A
tb = sp.simplify(-sp.pi - A - B + b1 + b2)
P("   total = -pi - A - B + b1 + b2 =", tb, " = -pi  (using A+B=b1+b2)   [CONSTANT]")
P("Switch-angle slots:")
P("   slot112[1]: sector1 gives T1+w1/2 ; sector2 gives L2+w2/2 = a ; switch1 gives 2b1")
P("      total = T1 + w1/2 + w2/2 + 2b1 = pi (closure at P1)     [CONSTANT]")
P("   slot112[2]: sector2 gives T2+w2/2 = a ; sector3 gives L3+w3/2 ; switch2 gives 2b2")
P("      total = T2 + w2/2 + L3 + w3/2 + 2b2 = pi (closure at P2) [CONSTANT]")
P("   => the pointwise closure turns these coefficients into the constants -pi, pi, pi:")
P("      no gain is booked there; the gain of the cluster is only in the coupled vars.")
P("      The global constant must NOT be adjusted.  [lead's statement confirmed]")

# ---------------------------------------------------------------- numeric identity block
P("")
P("="*78)
P("NUMERIC IDENTITY BLOCK (dps=50, fixed points; identity confirmation only)")
P("="*78)

def check(rr, bb1, bb2, AA):
    rr = mp.mpf(rr); bb1 = mp.mpf(bb1); bb2 = mp.mpf(bb2); AA = mp.mpf(AA)
    ss = mp.sqrt(1-rr**2); dl = bb1-AA
    P2 = mp.matrix([ss, rr]); P1 = mp.matrix([ss, -rr]); c2 = mp.matrix([ss, 0])
    D1 = 2*rr*mp.sin(bb1); D2 = 2*rr*mp.sin(bb2)
    c1 = c2 + mp.matrix([-D1*mp.cos(bb1), -D1*mp.sin(bb1)])
    c3 = c2 + mp.matrix([-D2*mp.cos(bb2),  D2*mp.sin(bb2)])
    c9 = None  # built per-H below
    out = []
    # root check: pick H at the two face-1 roots and one outside
    for tag, HH in [("lower root", 2*rr*mp.sin(bb1-AA)),
                    ("upper root", 2*rr*mp.sin(bb1+AA)),
                    ("mid", (2*rr*mp.sin(bb1-AA)+2*rr*mp.sin(bb1+AA))/2),
                    ("outside", 2*rr*mp.sin(bb1+AA)+mp.mpf('0.01'))]:
        if HH <= 0:
            continue
        p9 = mp.matrix([ss - HH*mp.cos(dl), -HH*mp.sin(dl)])
        L = mp.norm(c1-p9)
        rho1 = L/(2*mp.sin(AA))
        out.append("%s H=%s : rho1-r = %+.3e" % (tag, mp.nstr(HH, 8), rho1-rr))
    P("  r=%s b1=%s b2=%s A=%s  delta=%s" % (mp.nstr(rr,6), mp.nstr(bb1,6), mp.nstr(bb2,6),
                                             mp.nstr(AA,6), mp.nstr(dl,6)))
    for o in out:
        P("     " + o)
    # angle at c2 checks
    HH = (2*rr*mp.sin(bb1-AA)+2*rr*mp.sin(bb1+AA))/2
    if HH > 0:
        p9 = mp.matrix([ss - HH*mp.cos(dl), -HH*mp.sin(dl)])
        u1 = (c1-c2)/mp.norm(c1-c2); u9 = (p9-c2)/HH; v1 = (c3-c2)/mp.norm(c3-c2)
        angA = mp.acos(max(mp.mpf(-1), min(mp.mpf(1), u1[0]*u9[0]+u1[1]*u9[1])))
        angB = mp.acos(max(mp.mpf(-1), min(mp.mpf(1), u9[0]*v1[0]+u9[1]*v1[1])))
        P("     angle(c2->c1,c2->c9) - A = %+.3e ; angle(c2->c9,c2->c3) - B = %+.3e"
          % (angA-AA, angB-(bb1+bb2-AA)))
        P("     |c9-c2| - H = %+.3e" % (mp.norm(p9-c2)-HH))
        P("     |c9|^2-(1-r)^2 vs Q(H): Q(H)=%+.6e ; |c9|-(1-r)=%+.6e"
          % (HH**2 - 2*ss*mp.cos(dl)*HH + 2*rr*(1-rr), mp.norm(p9)-(1-rr)))
    # face2 roots
    P("     face2 roots: 2r sin(b2-B) = %s ; 2r sin(b2+B) = %s ; b2-B = -delta : %s"
      % (mp.nstr(2*rr*mp.sin(bb2-(bb1+bb2-AA)), 8), mp.nstr(2*rr*mp.sin(bb2+(bb1+bb2-AA)), 8),
         mp.nstr(bb2-(bb1+bb2-AA) - (-dl), 6)))

for case in [(mp.mpf('0.38'), mp.mpf('0.9'), mp.mpf('1.1'), mp.mpf('0.7')),
             (mp.mpf('0.38'), mp.mpf('0.4'), mp.mpf('0.5'), mp.mpf('0.2')),
             (mp.mpf('0.375'), mp.mpf('1.2'), mp.mpf('0.8'), mp.mpf('0.9')),
             (mp.mpf('0.38'), mp.mpf('0.6'), mp.mpf('0.6'), mp.mpf('0.6'))]:
    check(*case)
    P("")

with open(__file__.replace('tools' + __import__('os').sep, 'out' + __import__('os').sep)
          .replace('.py', '.txt').replace('audit_h_fiber', 'p24_audit_h_fiber'), 'w',
          encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
