# -*- coding: utf-8 -*-
"""P8: exact chain recursion for the inward-root ring sequence.

Claim to verify numerically (exact algebra target):
  line_i : the chord of bd D from P_{i-1} to P_i (both owned by ring i),
           with distance R from c_i and half-length r_i = h_i = sqrt(R^2 - rho_i^2)?
  Delta_i = t_i + 2 L_i,  L_i = atan2(sin t_i, rho_i - cos t_i)
  phi_i  = (theta_{i-1} + theta_i)/2 + L_i        (site lies on the angle bisector)
  Q_i = 2(L_i + L_{i+1}) = overlap_i + w_i
  gamma_i := phi_{i+1} - phi_i = pi - w_i/2 + (L_{i+1} - L_i)
  With h_i = sqrt(R^2 - rho_i^2) = hypot(-cos t_i, rho_i - sin t_i) ... (to be checked)
"""
import os, sys, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fan_core import HERE

OUT = os.path.join(HERE, os.pardir, "out")
lines = []
def P(s=""):
    lines.append(s); print(s)

import json
with open(os.path.join(OUT, "certified_object_copy.json"), "r", encoding="utf-8-sig") as f:
    OBJ = json.load(f)
C = np.array([[int(a)/1e17, int(b)/1e17] for a, b in OBJ["centers_scaled_1e17"]])
R = 0.3799838531198387090485181795734298538115979028

ring = [1, 3, 4, 5, 6, 7, 8, 9, 10]
mod = np.linalg.norm(C, axis=1)
phi = np.arctan2(C[:, 1], C[:, 0])
order = sorted(ring, key=lambda j: phi[j])
P("ring order %s" % order)

# switches
def sw_inner(i, j):
    a = C[i]; b = C[j]
    d = math.hypot(*(a-b))
    m = (a+b)/2
    hh = math.sqrt(max(R*R-d*d/4, 0.0))
    perp = np.array([-(b-a)[1], (b-a)[0]])/d
    p1 = m+hh*perp; p2 = m-hh*perp
    return p1 if np.linalg.norm(p1) <= np.linalg.norm(p2) else p2

P("")
P("per-ring chain data (ring order index k -> site j)")
P("%2s %3s %-20s %-20s %-20s %-20s %-20s" %
  ("k", "j", "rho_j", "t_j", "L_j", "Delta_j=t+2L", "h_j"))
tabs = []
for k, j in enumerate(order):
    rho = mod[j]
    t = math.asin(R/rho)
    L = math.atan2(math.sin(t), rho-math.cos(t))
    Dj = t+2*L
    hj = math.sqrt(max(R*R-rho*rho, 0.0))
    tabs.append((k, j, rho, t, L, Dj, hj))
    P("%2d %3d %-20.16f %-20.16f %-20.16f %-20.16f %-20.16f" %
      (k, j, rho, t, L, Dj, hj))

P("")
P("BOUNDARY RELATIONS:  the owned arc of ring k has half-length w_k/2 in angle;")
P("  the chord of bd D between consecutive switches seen from ring k has")
P("  half-chord h_k = sqrt(R^2-rho_k^2)  and half-angle w_k/2, so  sin(w_k/2) = h_k/R ?")

W = []
acc = []
for k in range(9):
    pm = sw_inner(order[(k-1) % 9], order[k])
    pp = sw_inner(order[k], order[(k+1) % 9])
    am = math.atan2(pm[1], pm[0]); ap = math.atan2(pp[1], pp[0])
    w = (ap-am) % (2*math.pi)
    W.append(w)
    k_, j, rho, t, L, Dj, hj = tabs[k]
    P("   k=%d ring %2d: w=%+.12f  2 asin(h/R)=%+.12f  diff=%+.2e   |w-R*...|" %
      (k, j, w, 2*math.asin(min(1.0, hj/R)), w-2*math.asin(min(1.0, hj/R))))
P("")
P("sum w = %.15f  2pi = %.15f" % (sum(W), 2*math.pi))

P("")
P("LINE-ANGLE RELATIONS")
for k in range(9):
    k_, j, rho, t, L, Dj, hj = tabs[k]
    pm = sw_inner(order[(k-1) % 9], order[k])
    pp = sw_inner(order[k], order[(k+1) % 9])
    am = math.atan2(pm[1], pm[0]); ap = math.atan2(pp[1], pp[0])
    # site angle = bisector + L?
    bis = (am+ap)/2 if abs(ap-am) < math.pi else (am+ap)/2 - math.pi*sign(ap-am)
    P("   k=%d ring %2d: phi_j=%+.15f  bisector+L=%+.15f  diff=%+.2e ; Delta_j=%.15f  (phi - theta_{k-1})=%.15f"
      % (k, j, phi[j], ((am+ap)/2 - math.pi*(1 if (ap-am) > math.pi else 0) + L),
         phi[j]-(((am+ap)/2 - math.pi*(1 if (ap-am) > math.pi else 0)) + L),
         Dj, (phi[j]-am) % (2*math.pi)))

# gamma and Q relations
P("")
P("GAMMA / Q RELATIONS  (gamma_i = phi_{i+1}-phi_i ; Q_i = 2(L_i+L_{i+1}))")
for i in range(9):
    a = tabs[i]; b = tabs[(i+1) % 9]
    gam = (b[2] and (phi[b[1]]-phi[a[1]])) % (2*math.pi)
    Q = 2*(a[4]+b[4])
    w = W[i]
    P("   i=%d: gamma=%+.15f   predicted pi - w/2 + (L_b-L_a)=%+.15f  diff=%+.2e ; Q=%.15f  gam-w/2-Q/2=%+.2e"
      % (i, gam, math.pi-w/2+(b[4]-a[4]), gam-(math.pi-w/2+(b[4]-a[4])), Q, gam-w/2-Q/2))

P("")
P("CHECK h_i = hypot(-cos t_i, rho_i - sin t_i) for the 9 rings")
for k, j, rho, t, L, Dj, hj in tabs:
    v = math.hypot(math.cos(t), rho-math.sin(t))
    P("   ring %2d: h=%.16f  hypot(cos t, rho-sin t)=%.16f  sqrt(R^2-rho^2)=%.16f  |diff|=%.2e" %
      (j, hj, v, math.sqrt(max(R*R-rho*rho, 0)), abs(v-hj)))

with open(os.path.join(OUT, "p8_chain_recursion.txt"), "w", encoding="utf-8") as f:
    f.write("\n".join(lines)+"\n")
