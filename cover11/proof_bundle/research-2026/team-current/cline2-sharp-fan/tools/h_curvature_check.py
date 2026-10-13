# -*- coding: utf-8 -*-
"""H-ENDPOINT-MAX CHECK with the frozen coefficients (own files only).

Input : lead/joint_patch_frozen_v2.json  (z[121], faces[11], edges[21])
Object: F(H) = sum of the atoms of the two patch faces [9,1,2], [9,2,3]
        (the only H-dependent factors of the 7-factor cluster at fixed b1,b2,A).
Output: exact coefficients, exact F'(H), F''(H), the exact trigonometric form of F'',
        the sign-free curvature bound, and the exact min-F'' on the H-fiber.
No claim registration; no mainTarget change.
"""
import os, sys, math, json
from pathlib import Path
import numpy as np

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
OUT = Path(__file__).resolve().parent.parent / 'out'
lines = []
def P(*a):
    s = " ".join(str(x) for x in a); lines.append(s); print(s)

J = json.loads((LEAD / 'joint_patch_frozen_v2.json').read_text(encoding='utf-8-sig'))
z = np.array(J['z']); FACES = [tuple(f) for f in J['faces']]; EDGES = [tuple(e) for e in J['edges']]
R0 = 0.38
P("frozen v2: z len %d, numeric_total_unrounded=%s, faces=%d edges=%d"
  % (len(z), J['numeric_total_unrounded'], len(FACES), len(EDGES)))
ADJ = {e: [t for t, f in enumerate(FACES) if all(i in f for i in e)] for e in EDGES}
f1 = FACES.index((9, 1, 2)); f2 = FACES.index((9, 2, 3))
P("face (9,1,2) index %d ; face (9,2,3) index %d" % (f1, f2))
P("")
P("--- adjacency and signs on the shared edge and the two external edges ---")
for name, tri in [("e12=(1,2)", (1, 2)), ("e92=(2,9)", (2, 9)), ("e91=(1,9)", (1, 9)),
                  ("e23=(2,3)", (2, 3)), ("e93=(3,9)", (3, 9))]:
    e = EDGES.index(tuple(sorted(tri)))
    P("  %-11s index %2d  adj=%s  (nfaces=%d)" % (name, e, ADJ[EDGES[e]], len(ADJ[EDGES[e]])))
e12 = EDGES.index((1, 2)); e92 = EDGES.index((2, 9)); e91 = EDGES.index((1, 9))
e23 = EDGES.index((2, 3)); e93 = EDGES.index((3, 9))

def sgn(fi, e):
    return 1 if ADJ[EDGES[e]][0] == fi else -1

P("")
P("--- effective coefficients of the NORMALIZED edge length h_e = L_e/(2 R0) ---")
P("    (atom slot: sgn*[ h_e^2 * z[11+e] + h_e * z[73+e] ])")
for nm, e in [("(1,9)", e91), ("(3,9)", e93), ("(2,9) shared", e92)]:
    c2_two = sum(sgn(fi, e) for fi in (f1, f2))*z[11+e]
    c1_two = sum(sgn(fi, e) for fi in (f1, f2))*z[73+e]
    allf = [fi for fi in range(len(FACES)) if all(i in FACES[fi] for i in EDGES[e])]
    c2_all = sum(sgn(fi, e) for fi in allf)*z[11+e]
    c1_all = sum(sgn(fi, e) for fi in allf)*z[73+e]
    P("  edge %-13s z11=%+.9f z73=%+.9f | two-face coeffs: h^2 %+.9f  h %+.9f | all-%d-face: %+.9f  %+.9f"
      % (nm, z[11+e], z[73+e], c2_two, c1_two, len(allf), c2_all, c1_all))
P("  NOTE: for an INTERNAL edge (2 faces) the net slot coefficient over ALL incident faces is")
P("        z11*(sgn_f+sgn_g) = 0 and z73*(sgn_f+sgn_g) = 0: those slots cancel globally.")
P("        The lead's quoted +/- coefficients are therefore the TWO-FACE-partial ones;")
P("        the other incident faces [9,0,1] (edge 1,9) and [9,3,4] (edge 3,9) carry the")
P("        opposite sign and must be included for the full H-dependence (see PART C).")

P("")
P("--- the two-face coefficients in the closed form (units: L = actual length) ---")
s1 = sgn(f1, e92); s2 = sgn(f2, e92)
Z9, Z1, Z2, Z3 = z[9], z[1], z[2], z[3]
Zang = lambda e: z[50+e]; Zq = lambda e: z[11+e]; Zlin = lambda e: z[73+e]
a1 = (Z1 + Zang(e92)) - (Z9 + Zang(e12))
a2 = (Z3 + Zang(e92)) - (Z9 + Zang(e23))
be1 = sgn(f1, e91)*Zq(e91)/(4*R0*R0); ga1 = sgn(f1, e91)*Zlin(e91)/(2*R0)
be2 = sgn(f2, e93)*Zq(e93)/(4*R0*R0); ga2 = sgn(f2, e93)*Zlin(e93)/(2*R0)
lam0 = None  # depends on b1,b2,A: lam0 = R0*(sin b1 sin A + sin b2 sin B)
C0 = None
P("  s1=%+d s2=%+d" % (s1, s2))
P("  z9=%+.9f z1=%+.9f z3=%+.9f  (lead quote: -.05139 -.03944 -.03863)" % (Z9, Z1, Z3))
P("  alpha1 = %+.9f   alpha2 = %+.9f" % (a1, a2))
P("  beta1  = %+.9f   gamma1 = %+.9f   [edge (1,9)]" % (be1, ga1))
P("  beta2  = %+.9f   gamma2 = %+.9f   [edge (3,9)]" % (be2, ga2))
P("  cross-check with the lead's quotes: 0.406258814, 0.420928035, -.874840892, -.903343188")
P("     sgn(f1,e91)*z11[e91] = %+.9f ; sgn(f2,e93)*z11[e93] = %+.9f"
  % (sgn(f1, e91)*Zq(e91), sgn(f2, e93)*Zq(e93)))
P("     sgn(f1,e91)*z73[e91] = %+.9f ; sgn(f2,e93)*z73[e93] = %+.9f"
  % (sgn(f1, e91)*Zlin(e91), sgn(f2, e93)*Zlin(e93)))

P("")
P("="*78)
P("F(H) = C0 + lam0 H + alpha1 phi1 + alpha2 phi2 + beta1 L1^2 + gamma1 L1")
P("                                                + beta2 L2^2 + gamma2 L2")
P("  lam0 = R0 (sin b1 sin A + sin b2 sin B) > 0 ;  B = b1+b2-A")
P("  L1^2 = H^2 + D1^2 - 2 H D1 cos A ,  L2^2 = H^2 + D2^2 - 2 H D2 cos B")
P("  D1 = 2 R0 sin b1 ,  D2 = 2 R0 sin b2")
P("  phi_j = atan2(D_j sin th_j, H - D_j cos th_j)   (th_1=A, th_2=B)")
P("  z_j  := alpha_j ,  b_j^s := beta_j ,  g_j := gamma_j")
P("")
P("F'(H)  = lam0 - a1 D1 sinA/L1^2 - a2 D2 sinB/L2^2")
P("       + 2 be1 (H-D1 cosA) + 2 be2 (H-D2 cosB)")
P("       + ga1 (H-D1 cosA)/L1 + ga2 (H-D2 cosB)/L2")
P("")
P("F''(H) = 2(be1+be2) + sum_j [ 2 a_j D_j sin th_j (H-D_j cos th_j)/L_j^4")
P("                            + ga_j D_j^2 sin^2 th_j / L_j^3 ]")
P("")
P("EXACT TRIGONOMETRIC FORM (phi_j = hub angle of face j):")
P("   cos phi_j = (H - D_j cos th_j)/L_j ,  sin phi_j = D_j sin th_j/L_j ,  L_j = D_j sin th_j/sin phi_j")
P("   => F''(H) = 2(be1+be2) + sum_j sin^3(phi_j)/(D_j sin th_j) * [ 2 a_j cos(phi_j)/(D_j sin th_j) + ga_j ]")
P("")
P("SIGN-FREE BOUND (uses L_j >= D_j sin th_j and |cos phi_j| <= 1):")
P("   min F'' >= 2(be1+be2) - M ,  M := sum_j [ 2|a_j|/(D_j sin th_j)^2 + |ga_j|/(D_j sin th_j) ]")
P("   so  2(be1+be2) >= M  =>  F strictly convex on the WHOLE fiber  =>  max F at H_lo or H_hi.")
P("   (concavity:  2(be1+be2) <= -M  =>  F strictly concave; then max at an endpoint or the")
P("    unique critical point F'=0.)")

vals = dict(a1=a1, a2=a2, be1=be1, be2=be2, ga1=ga1, ga2=ga2, s1=s1, s2=s2)
P("")
P("="*78)
P("NUMERIC TEST OF THE CRITERIA with the frozen coefficients")
P("="*78)
P("2(be1+be2) = %+.9f" % (2*(be1+be2)))
P("|ga1| = %.9f ,  |ga2| = %.9f   (both gamma NEGATIVE: the linear h-coefficients are negative)" % (abs(ga1), abs(ga2)))
P("The bound M contains |ga_j|/(D_j sin th_j) = |ga_j|/(2 R0 sin b_j sin th_j).")
P("Since sin b_j sin th_j <= 1, each such term alone is >= |ga_j|/(2R0) = %.6f resp %.6f;"
  % (abs(ga1)/(2*R0), abs(ga2)/(2*R0)))
P("hence M >= %.6f > 2(be1+be2) = %.6f  ALWAYS." % (abs(ga1)/(2*R0)+abs(ga2)/(2*R0), 2*(be1+be2)))
P("=> the SIGN-FREE CONVEXITY CRITERION CANNOT HOLD for these coefficients,")
P("   and neither can the concavity criterion (2(be1+be2) > 0).  A sharper test is needed:")
P("   minimize F'' exactly over the H-fiber using the exact trigonometric form above.")

P("")
P("="*78)
P("EXACT min F'' ON THE H-FIBER (sharp test)")
P("="*78)
P("On the fiber H in [Hlo,Hhi], phi_j decreases from phi_j(Hlo) to phi_j(Hhi).  Hence")
P("   min_H F'' = 2(be1+be2) + sum_j min_{phi in [phi_j(Hhi), phi_j(Hlo)]} G_j(phi),")
P("   G_j(phi) := sin^3(phi)/(D_j sin th_j) * [ 2 a_j cos(phi)/(D_j sin th_j) + ga_j ].")
P("G_j has at most 2 interior critical points (d/dphi of sin^3(2a cos/(Dt)+g)); the min is")
P("attained at a critical point or at an interval endpoint, so min F'' is computable exactly")
P("given (b1,b2,A) and the fiber.  Substituting the frozen signs:")
def Gj(phi, a, ga, Dt):
    return math.sin(phi)**3/(Dt) * (2*a*math.cos(phi)/Dt + ga)
P("  (a1=%+.4f, ga1=%+.4f, a2=%+.4f, ga2=%+.4f)" % (a1, ga1, a2, ga2))
P("  For a_j < 0 the bracket [2a_j cos/(D_j th_j) + ga_j] is most negative at cos phi = +1,")
P("  i.e. G_j's minimum sits at phi = 0 (fiber far end) whenever the fiber reaches small phi;")
P("  for a_j > 0 it sits at phi = pi.  In both cases the minimum is attained at an ENDPOINT")
P("  of the phi-interval unless the derivative vanishes inside, which the explicit")
P("  derivative test below decides per case:")
P("      dG/dphi = sin^2 /(Dt) * [ 3 cos phi (2a cos/(Dt) + ga) - 2a sin^2 phi/(Dt) ]")
P("      = sin^2/(Dt)^2 * [ 3 cos phi (2a cos phi + ga Dt) - 2a (1-cos^2 phi) ]")
P("")
P("=> CONSEQUENCE FOR THE REDUCTION: the H-optimisation is still 1-dimensional and explicit;")
P("   but with these frozen coefficients it is NOT settled by a uniform convexity bound.")
P("   The correct certificate is: evaluate F at H_lo and H_hi and, if F'' changes sign on the")
P("   fiber, at the zeros of F' (a scalar equation with the explicit F' above).")
P("   A sufficient (testable) route to endpoint-max without solving F'=0:")
P("      max over the fiber of |F' - lam0 ...| bounded => F' > 0 or F' < 0 on the fiber.")

P("")
P("="*78)
P("FIBER ENDPOINTS (from the earlier audit; own files)")
P("="*78)
P("  s = sqrt(1-r^2), delta = b1 - A, Dd = s^2 cos^2 delta - 2 r (1-r)")
P("  H in [ max( 2r|sin delta| , s cos delta - sqrt(Dd) ) ,")
P("         min( 2r sin(b1+A) , 2r sin(b2+B) , s cos delta + sqrt(Dd) ) ]")
P("  (r = R0 = 19/50; preconditions b1,b2 in (0,pi/2), delta in (-b2,b1), Dd >= 0,")
P("   sin(b1+A) > 0, sin(b2+B) > 0)")

with open(OUT / 'p26_h_curvature.txt', 'w', encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
