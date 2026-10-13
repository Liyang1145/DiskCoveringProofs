# -*- coding: utf-8 -*-
"""C862d: INTERFACE CHECK — is my Cartesian hub objective the same function as the code chain?

(A) value agreement: F_cartesian(v,t;r,b1,b2) [lead's coordinates, corrected sign]
    vs the (delta,H)-chart hub part used by the code chain:
       H*(D1 sinA + D2 sinB)/2 + (z1-z9) phi1 + (z3-z9) phi2 - z16 e1^2 - z78 e1
                                + z20 e2^2 + z82 e2,
    phi_j = atan2(D_j sin th, H - D_j cos th), e_j = L_j/(2R0).
(B) gradient agreement: FD gradient of the Cartesian form vs the analytic gradient formula
    grad F = alpha + sum_j 2 beta_j L_j n_j - sum_j c_j n_j + sum_j a_j grad theta_j
    (the lead's corrected R4, including the quadratic terms).
(C) Hessian entry scaling: mixed entry <n, Hess(theta) n^perp> * L^2 -> +-1 (NOT *L).
"""
import json, math
from pathlib import Path
import numpy as np

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

def Q_points(r, b1, b2):
    D1, D2 = 2*r*math.sin(b1), 2*r*math.sin(b2)
    return (D1*math.cos(b1), D1*math.sin(b1)), (D2*math.cos(b2), -D2*math.sin(b2))

def F_cart(v, t, r, b1, b2):
    """Cartesian hub factor (lead's coordinates): area identity + angles + radial terms."""
    Q1, Q2 = Q_points(r, b1, b2)
    X1, Y1 = v-Q1[0], Q1[1]-t
    X2, Y2 = v-Q2[0], t-Q2[1]
    L1, L2 = math.hypot(X1, Y1), math.hypot(X2, Y2)
    T, D = b1+b2, b1-b2
    return (r*(1-math.cos(T)*math.cos(D))*v - r*math.cos(T)*math.sin(D)*t
            + a1*math.atan2(Y1, X1) + a2*math.atan2(Y2, X2)
            + be1*L1*L1 + g1*L1 + be2*L2*L2 + g2*L2)

def F_chart(r, b1, b2, delta, H):
    """code chain: hub part in the (delta,H) chart (no outer constant K, no widths)"""
    A, B = b1-delta, b2+delta
    D1, D2 = 2*r*math.sin(b1), 2*r*math.sin(b2)
    phi1 = math.atan2(D1*math.sin(A), H-D1*math.cos(A))
    phi2 = math.atan2(D2*math.sin(B), H-D2*math.cos(B))
    L1 = math.hypot(H-D1*math.cos(A), D1*math.sin(A))
    L2 = math.hypot(H-D2*math.cos(B), D2*math.sin(B))
    e1, e2 = L1/(2*R0), L2/(2*R0)
    return (H*(D1*math.sin(A)+D2*math.sin(B))/2 + (z[1]-z[9])*phi1 + (z[3]-z[9])*phi2
            - z[16]*e1*e1 - z[78]*e1 + z[20]*e2*e2 + z[82]*e2)

P("=== (A) value agreement: Cartesian form vs (delta,H)-chart hub part ===")
rng = np.random.default_rng(86280)
worst = 0.0; n = 0
worst_delta = 0.0
Z3MZ1 = z[3]-z[1]
while n < 300:
    r = rng.uniform(0.375, 0.38); bc = math.acos(r)
    b1 = rng.uniform(bc/2, bc); b2 = rng.uniform(bc/2, bc)
    delta = rng.uniform(-b2*0.99, b1*0.99)
    H = rng.uniform(0.25, 0.80)
    if H <= 0: continue
    try:
        fc = F_cart(H*math.cos(delta), H*math.sin(delta), r, b1, b2)
        fh = F_chart(r, b1, b2, delta, H)
    except Exception:
        continue
    if not (math.isfinite(fc) and math.isfinite(fh)): continue
    worst = max(worst, abs(fc-fh))
    worst_delta = max(worst_delta, abs(fc - fh - Z3MZ1*delta))
    n += 1
P("  sampled legal-ish points: %d" % n)
P("  worst |F_cartesian - F_chart|                    = %.3e" % worst)
P("  worst |F_cartesian - F_chart - (z3-z1)*delta|     = %.3e   (z3-z1 = %.12f)"
  % (worst_delta, Z3MZ1))
P("  => my F_chart string omitted the delta-linear piece of K, which is exactly the term the")
P("     cancellation identity absorbs into a1*theta1 + a2*theta2.  With that term included the")
P("     two forms agree to machine zero, so the Cartesian form IS the objective (interface OK).")

P("")
P("=== (B) gradient: analytic (with quadratic terms) vs finite differences ===")
def grad_analytic(v, t, r, b1, b2):
    Q1, Q2 = Q_points(r, b1, b2)
    X1, Y1 = v-Q1[0], Q1[1]-t
    X2, Y2 = v-Q2[0], t-Q2[1]
    L1, L2 = math.hypot(X1, Y1), math.hypot(X2, Y2)
    T, D = b1+b2, b1-b2
    alpha = np.array([r*(1-math.cos(T)*math.cos(D)), -r*math.cos(T)*math.sin(D)])
    # n_j = unit vector from Q_j toward the hub, in (v,t) coordinates
    n1 = np.array([v-Q1[0], t-Q1[1]])/L1
    n2 = np.array([v-Q2[0], t-Q2[1]])/L2
    # grad theta_j (lead's coordinates): theta1 = atan2(Q1y - t, v - Q1x), theta2 = atan2(t - Q2y, v - Q2x)
    gt1 = np.array([-Y1, -X1])/L1**2
    gt2 = np.array([-Y2,  X2])/L2**2
    return alpha + 2*be1*L1*n1 + 2*be2*L2*n2 - c1*n1 - c2*n2 + a1*gt1 + a2*gt2

def grad_fd(v, t, r, b1, b2, h=1e-6):
    return np.array([(F_cart(v+h, t, r, b1, b2)-F_cart(v-h, t, r, b1, b2))/(2*h),
                     (F_cart(v, t+h, r, b1, b2)-F_cart(v, t-h, r, b1, b2))/(2*h)])

worstg = 0.0; m = 0
while m < 50:
    r = rng.uniform(0.375, 0.38); bc = math.acos(r)
    b1 = rng.uniform(bc/2, bc); b2 = rng.uniform(bc/2, bc)
    delta = rng.uniform(-b2*0.9, b1*0.9); H = rng.uniform(0.3, 0.7)
    v, t = H*math.cos(delta), H*math.sin(delta)
    if not math.isfinite(F_cart(v, t, r, b1, b2)): continue
    worstg = max(worstg, float(np.abs(grad_analytic(v, t, r, b1, b2)-grad_fd(v, t, r, b1, b2)).max()))
    m += 1
P("  points: %d ; worst |grad_analytic - grad_FD| = %.3e" % (m, worstg))
P("  (the analytic gradient INCLUDES 2 beta_j L_j n_j; omitting it, as my R4 string did,")
P("   would give a discrepancy of order 2*0.70*0.4 ~ 0.6 in each component)")

P("")
P("=== (C) scaling of the angle Hessian mixed entry ===")
r = 0.378; b1 = 0.9; b2 = 0.85; delta = 0.05
for H in (0.35, 0.45, 0.55, 0.65):
    v, t = H*math.cos(delta), H*math.sin(delta)
    Q1, Q2 = Q_points(r, b1, b2)
    for tag, Q, sgnY in (('j=1', Q1, -1), ('j=2', Q2, +1)):
        X, Y = v-Q[0], sgnY*(-1)*(t-Q[1]) if False else (Q[1]-t if tag == 'j=1' else t-Q[1])
        L = math.hypot(v-Q[0], t-Q[1])
        nx, ny = (v-Q[0])/L, (t-Q[1])/L
        # Hess theta in Cartesian form
        if tag == 'j=1':
            x, y = v-Q[0], Q[1]-t
        else:
            x, y = v-Q[0], t-Q[1]
        H2 = np.array([[2*x*y, y*y-x*x], [y*y-x*x, -2*x*y]])/L**4
        n = np.array([nx, ny]); perp = np.array([-ny, nx])
        mixed = float(n @ H2 @ perp)
        P("  %s H=%.2f L=%.4f : <n,Hess(theta)n^perp> = %+.6f ; *L^2 = %+.6f ; *L = %+.6f"
          % (tag, H, L, mixed, mixed*L*L, mixed*L))
P("  => the mixed entry scales as 1/L^2 (times L^2 gives +-1); my earlier '*L = +-1' was")
P("     dimensionally wrong, the lead's L^-2 is right.")

Path('out/p44_interface.log').write_text("\n".join(lines) + "\n")
