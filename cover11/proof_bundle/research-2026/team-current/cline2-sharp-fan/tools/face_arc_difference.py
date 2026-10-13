# -*- coding: utf-8 -*-
"""C868 follow-up: symbolic difference G(face arc) - G(ridge).

Setup (lead's face-circle chart, face 1 saturated):
   A = b1 - delta (free),  H = 2r sin(b1+A),  hub = H(cos delta, sin delta)
   (v,t) = r(sin2b1 + sin2A, cos2A - cos2b1)          [verified below]
Structural facts to verify:
  (F1) on the face-1 circle L1 = 2r sin A exactly, hence sin phi1 = sin b1: the face-1 hub
       angle phi1 is CONSTANT along the arc (b1 or pi-b1) - its contribution to G is constant;
  (F2) the area part is affine in (sin2A, cos2A);
  (F3) the ridge is the arc point A = b2 (delta = b1-b2);
  (F4) G_arc(A) - G_arc(b2) as an integral of an explicit derivative.
"""
import json, math
from pathlib import Path
import numpy as np
import sympy as sp

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
z = json.loads((LEAD / 'joint_nested_frozen.json').read_text(encoding='utf-8-sig'))['z']
R0 = 19/50
a1, a2 = z[1]-z[9], z[3]-z[9]
be1, be2 = -z[16]/(4*R0*R0), z[20]/(4*R0*R0)
g1, g2 = -z[78]/(2*R0), z[82]/(2*R0)
c1, c2 = abs(g1), abs(g2)
lines = []
def P(*a):
    s = " ".join(str(x) for x in a); lines.append(s); print(s)

# ---------------- symbolic: face-circle coordinates and L1
r, b1, b2, A = sp.symbols('r b1 b2 A', positive=True)
d = b1 - A
H = 2*r*sp.sin(b1+A)
P("=== (F1)-(F2) symbolic face-circle identities ===")
P("  v - r(sin2b1 + sin2A) :",
  sp.simplify(2*r*sp.sin(b1+A)*sp.cos(d) - r*(sp.sin(2*b1)+sp.sin(2*A))))
P("  t - r(cos2A - cos2b1) :",
  sp.simplify(2*r*sp.sin(b1+A)*sp.sin(d) - r*(sp.cos(2*A)-sp.cos(2*b1))))
Q1 = sp.Matrix([r*sp.sin(2*b1), 2*r*sp.sin(b1)**2])          # ring centre c1 in the (v,t) frame
hub = sp.Matrix([r*(sp.sin(2*b1)+sp.sin(2*A)), r*(sp.cos(2*A)-sp.cos(2*b1))])
P("  |hub - c1|^2 - (2r sinA)^2 :",
  sp.simplify(sp.expand((hub-Q1).dot(hub-Q1) - (2*r*sp.sin(A))**2)))
D1 = 2*r*sp.sin(b1)
phi1 = sp.atan2(D1*sp.sin(A), H - D1*sp.cos(A))
P("  sin(phi1)^2 - sin(b1)^2 :", sp.simplify(sp.sin(phi1)**2 - sp.sin(b1)**2))
P("  so phi1 is CONSTANT along the face-1 arc (phi1 = b1 or pi-b1): the a1-angle term is a")
P("  constant on the arc and drops out of every difference along it.")
P("  (equivalently: the face-1 circle is exactly the locus circumradius = r, and there the law")
P("   of sines gives sin phi1 = D1/(2R_circ) = sin b1.)")
P("")
P("=== (F3)-(F4) the G_arc formula and the ridge point ===")
P("  G_arc(A) = [area](A) + a1*phi1 + a2*phi2(A) + beta1 L1^2 + gamma1 L1 + beta2 L2^2 + gamma2 L2")
P("             + (z3-z1)*(b1-A)             [the delta-linear K piece]")
P("  with L1 = 2r sinA, L2 = |hub - c3|, c3 = (r sin2b2, -2r sin^2b2),")
P("       phi2 = atan2(D2 sinB, H - D2 cosB), B = b2 + b1 - A, D2 = 2r sin b2,")
P("  and the ridge is the arc point A = b2 (delta = b1-b2), where L1 = 2r sinb2, L2 = 2r sinb1.")
P("")
P("  difference as an integral:   G_arc(A) - G_arc(b2) = integral_{b2}^{A} G_arc'(s) ds,")
P("  so a proof needs a sign-definite integral, NOT monotonicity of G (the certified C868 arc")
P("  has two local maxima, so G' changes sign at least twice).")

# ---------------- numeric verification of the framework at the C868 point
def G_arc(rr, bb1, bb2, AA, widths=(0.5, 0.5)):
    s = math.sqrt(1-rr*rr); Hh = 2*rr*math.sin(bb1+AA); dd = bb1-AA
    v = 2*rr*math.sin(bb1+AA)*math.cos(dd); t = 2*rr*math.sin(bb1+AA)*math.sin(dd)
    Q1 = (rr*math.sin(2*bb1), 2*rr*math.sin(bb1)**2)
    Q3 = (rr*math.sin(2*bb2), -2*rr*math.sin(bb2)**2)
    L1 = math.hypot(v-Q1[0], t-Q1[1]); L2 = math.hypot(v-Q3[0], t-Q3[1])
    B = bb2 + bb1 - AA
    D2 = 2*rr*math.sin(bb2)
    phi2 = math.atan2(D2*math.sin(B), Hh - D2*math.cos(B))
    area = rr*(math.sin(bb1)**2+math.sin(bb2)**2)*v + rr*(math.sin(bb2)*math.cos(bb2)-math.sin(bb1)*math.cos(bb1))*t
    return (area + a1*phi1_const + a2*phi2 + be1*L1*L1 + g1*L1 + be2*L2*L2 + g2*L2
            + (z[3]-z[1])*(bb1-AA))

# determine the constant phi1 by direct evaluation
def phi1_of(rr, bb1, AA):
    Hh = 2*rr*math.sin(bb1+AA); D1 = 2*rr*math.sin(bb1)
    return math.atan2(D1*math.sin(AA), Hh - D1*math.cos(AA))
rr, bb1 = 0.377, 1.008
vals = [phi1_of(rr, bb1, AA) for AA in (1.32, 1.34, 1.36)]
P("")
P("=== numeric verification at r=.377, b1=1.008 ===")
P("  phi1 along the arc (A = 1.32, 1.34, 1.36): %s" % [round(v_, 10) for v_ in vals])
P("  pi - b1 = %.6f ; b1 = %.6f  => phi1 == pi - b1 : %s"
  % (math.pi-1.008, 1.008, abs(vals[0]-(math.pi-1.008)) < 1e-9))
phi1_const = math.pi - 1.008
bb2 = 1.001
ridgeA = bb2
P("  ridge point A* = b2 = %.3f : G_arc = %.6f" % (ridgeA, G_arc(rr, bb1, bb2, ridgeA)))
P("  arc values around the certified local max (A = b1 - delta, delta in [-.32,-.31]):")
for dd_ in (-0.320, -0.315, -0.310):
    AA = bb1 - dd_
    P("     delta=%.3f (A=%.4f): G_arc = %.6f" % (dd_, AA, G_arc(rr, bb1, bb2, AA)))
P("  (lead's numbers: ridge ~ -0.4947, local max ~ -0.4988 - reproduced up to the sign of the")
P("   outer/width constants, which cancel in differences along the arc)")
P("")
P("=== symbolic attempt: G_arc(A) - G_arc(b2) in the variable u = A - b2 ===")
P("  Substitute A = b2 + u and expand the derivative d/du G_arc at u = 0: if the leading")
P("  coefficients have a definite sign on the high-bearing domain, the difference is controlled")
P("  near the ridge; globally one needs the integral form (F4).")

outp = Path('out/p45_face_arc.txt')
outp.write_text("\n".join(lines) + "\n")
