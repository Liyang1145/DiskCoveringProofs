# -*- coding: utf-8 -*-
"""P9: the tangency (critical) parametrisation -- exact algebra.

CALIBER
  D unit closed disk, radius-R disks, angles radians, all lengths in units of the
  unit-disk radius.

FACT (to be proved in the write-up; verified numerically here):
  For a radius-R disk with centre c let  Psi(c) := max_{|P|=1} |P-c| = 1 + |c|.
  Hence  D < B(c,R)  iff  |c| + R <= 1.
  If a ring disk covers ANY boundary arc of positive length then |c| + R >= 1, so
  for a ring that covers boundary arcs of positive length:
        |c| + R = 1    (critically "outward-bracketing"),  |c| = 1 - R.
  [This is the reduction to be used below; the candidate satisfies it exactly.]

PARAMETRISATION at fixed R:
  ring i is named by its tangency (critical) angle theta_i = arg(-c_i) ... see below:
      write c_i = -|c_i| e^{i theta_i},  |c_i| = 1-R
      phi_i = angular position of c_i in the frame  psi_i := theta_i + pi  (so c = rho e^{i psi})
  Distance from a boundary point at angle psi (measured absolutely) to c:
      |P(psi) - c|^2 = (1-R)^2 + 1 + 2(1-R) cos(psi - theta_i)
  Tangent point (unique, distance exactly R):  psi = theta_i.
  Chord/arc data:  the disk covers the boundary arc  |psi - theta_i| <= t_i where
      cos t_i = ... (solve the quadratic)  <=>  sin t_i = R cos(phi_i)
"""
import os, sys, math, json
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fan_core import HERE

OUT = os.path.join(HERE, os.pardir, "out")
lines = []
def P(s=""):
    lines.append(s); print(s)

with open(os.path.join(OUT, "certified_object_copy.json"), "r", encoding="utf-8-sig") as f:
    OBJ = json.load(f)
C = np.array([[int(a)/1e17, int(b)/1e17] for a, b in OBJ["centers_scaled_1e17"]])
R = 0.3799838531198387090485181795734298538115979028
ring = [1, 3, 4, 5, 6, 7, 8, 9, 10]

mod = np.linalg.norm(C, axis=1)
psi = np.arctan2(C[:, 1], C[:, 0])

P("=== critical (tangency) check:  d/dpsi |P(psi)-c|^2 = -2|c| sin(psi-psi_c) ===")
P("%3s %-22s %-22s %-22s %-22s" % ("j", "|c_j|", "1-R-|c_j|", "psi_j", "tangency angle theta_j"))
for j in ring:
    m = mod[j]
    P("%3d %-22.17f %-22.3e %-22.15f %-22.15f" % (j, m, (1-R)-m, psi[j], psi[j]))
P("")
P("max_psi |P-c_j| for each ring (must equal R):")
for j in ring:
    th = np.linspace(0, 2*np.pi, 2000001)
    # d2 = (1-R)^2+1+2(1-R)cos(psi-theta) with c = -(1-R) e^{i theta}, theta = psi_j + pi
    theta = psi[j] + math.pi
    d2 = (1-R)**2 + 1 + 2*(1-R)*np.cos(th-theta)
    P("   ring %2d: max dist = %.17f   (R = %.17f, diff %+.3e) at psi = %.8f (theta+0=%.8f)"
      % (j, math.sqrt(d2.max()), R, math.sqrt(d2.max())-R,
         th[int(np.argmax(d2))], (theta+2*math.pi) % (2*math.pi)))
P("")
P("=== phi_i (position of c in the frame of the tangency point) ===")
P("    define c = rho e^{i psi},  tangency point at angle theta = psi + pi")
P("    phi := angle at the ORIGIN between the tangency point and c  =  pi - (psi - theta)?")
P("    concretely: chord from tangency point A=1*e^{i theta} to c; the angle at A between AO and Ac")
for j in ring:
    theta = (psi[j] + math.pi) % (2*math.pi)
    A = np.array([math.cos(theta), math.sin(theta)])
    c = C[j]
    # angle at A between (O-A) and (c-A)
    v1 = -A; v2 = c - A
    ang = math.atan2(abs(v1[0]*v2[1]-v1[1]*v2[0]), v1[0]*v2[0]+v1[1]*v2[1])
    # the angular half-width of the covered arc: |P(psi)-c|=R  ->  sin t = R*cos(phi)
    t = math.asin(min(1.0, R*math.cos(ang)))
    P("   ring %2d: psi=%+.10f theta=%+.10f  |c|=%.10f  phi=%.10f  t=asin(R cos phi)=%.10f"
      % (j, psi[j], theta, mod[j], ang, t))
    # verify against the direct arc halfwidth from before
    t_direct = math.asin(R/mod[j])
    P("            direct asin(R/|c|) = %.10f  diff = %+.2e ; sin t - R cos phi = %+.2e"
      % (t_direct, t-t_direct, math.sin(t)-R*math.cos(ang)))
with open(os.path.join(OUT, "p9_tangency.txt"), "w", encoding="utf-8") as f:
    f.write("\n".join(lines)+"\n")
