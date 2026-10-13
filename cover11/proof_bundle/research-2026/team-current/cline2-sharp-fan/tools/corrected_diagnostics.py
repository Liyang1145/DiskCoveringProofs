# -*- coding: utf-8 -*-
"""C862c-2: re-verify the C862b conclusions with the SIGN-CORRECTED objective.

Symbolic audit (tools/sign_audit.py) showed: in the lead's coordinates
  grad theta1 = (-Y1,-X1)/L1^2, n1 = (X1,-Y1)/L1 ; grad theta2 = (-Y2,+X2)/L2^2, n2 = (X2,Y2)/L2
  <n1, Hess(theta1) n1^perp> L1 = +1  but  <n2, Hess(theta2) n2^perp> L2 = -1
i.e. the two angle terms have OPPOSITE chirality, so
  Hess F = 2(sum beta) I - sum (c_j/L_j)(I - n_j n_j^T) + (a_1/L_1^2)(-M_1) + (a_2/L_2^2)(+M_2)
with M_j = 2 w_j w_j^T - I, w_j = n_j rotated by -pi/4.
Round 23 used the same chirality for both; these runs use the corrected one.
"""
import json, math
from pathlib import Path
import numpy as np
from scipy.optimize import differential_evolution

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
z = json.loads((LEAD / 'joint_nested_frozen.json').read_text(encoding='utf-8-sig'))['z']
R0 = 19/50
a1, a2 = z[1]-z[9], z[3]-z[9]
be1, be2 = -z[16]/(4*R0*R0), z[20]/(4*R0*R0)
g1, g2 = -z[78]/(2*R0), z[82]/(2*R0)
c1, c2 = abs(g1), abs(g2)
SUMB = 2*(be1+be2)
G = 2*math.pi - 16*math.asin(R0)
def bmin(r):
    eta = G/2
    return (math.acos(r) + math.asin(math.sin(eta)/r) - eta)/2
lines = []
def P(*a):
    s = " ".join(str(x) for x in a); lines.append(s); print(s)

def data(r, b1, b2, delta):
    """Q1,Q2 in the (v,t) frame; lead's (X1,Y1),(X2,Y2)."""
    s = math.sqrt(1-r*r)
    if not (delta > -b2 and delta < b1): return None
    A, B = b1-delta, b2+delta
    if min(A, B) <= 0: return None
    D1, D2 = 2*r*math.sin(b1), 2*r*math.sin(b2)
    Q1 = (D1*math.cos(b1), D1*math.sin(b1)); Q2 = (D2*math.cos(b2), -D2*math.sin(b2))
    return s, A, B, Q1, Q2

def fiber(r, b1, b2, delta):
    d = data(r, b1, b2, delta)
    if d is None: return None
    s, A, B, Q1, Q2 = d
    disc = s*s*math.cos(delta)**2 - 2*r*(1-r)
    if disc < 0: return None
    lo = max(2*r*abs(math.sin(delta)), s*math.cos(delta)-math.sqrt(disc))
    hi = min(2*r*math.sin(b1+A), 2*r*math.sin(b2+B), s*math.cos(delta)+math.sqrt(disc))
    return (lo, hi) if lo <= hi else None

def F(v, t, r, b1, b2):
    """SIGN-CORRECTED objective: area + a1*theta1_lead + a2*theta2_lead + radial."""
    d = data(r, b1, b2, math.atan2(t, v))
    if d is None: return float('nan')
    s, A, B, Q1, Q2 = d
    X1, Y1 = v-Q1[0], Q1[1]-t          # lead's face-1 data (note the t-sign)
    X2, Y2 = v-Q2[0], t-Q2[1]
    L1 = math.hypot(X1, Y1); L2 = math.hypot(X2, Y2)
    T, D = b1+b2, b1-b2
    return (r*(1-math.cos(T)*math.cos(D))*v - r*math.cos(T)*math.sin(D)*t
            + a1*math.atan2(Y1, X1) + a2*math.atan2(Y2, X2)
            + be1*L1*L1 + g1*L1 + be2*L2*L2 + g2*L2)

def hess(v, t, r, b1, b2):
    """analytic Hessian with OPPOSITE chirality for the two angle terms"""
    d = data(r, b1, b2, math.atan2(t, v)); s, A, B, Q1, Q2 = d
    H = np.array([[SUMB, 0.0], [0.0, SUMB]])
    for Q, c, a, sgn in ((Q1, c1, a1, -1.0), (Q2, c2, a2, +1.0)):
        L = math.hypot(v-Q[0], t-Q[1]); n = np.array([(v-Q[0])/L, (t-Q[1])/L])
        H -= (c/L)*(np.eye(2) - np.outer(n, n))
        th = -math.pi/4
        w = np.array([math.cos(th)*n[0]-math.sin(th)*n[1], math.sin(th)*n[0]+math.cos(th)*n[1]])
        H += sgn*(a/(L*L))*(2*np.outer(w, w) - np.eye(2))
    return H

def nh(v, t, r, b1, b2, h=1e-6):
    H = np.zeros((2, 2))
    H[0, 0] = (F(v+h, t, r, b1, b2)-2*F(v, t, r, b1, b2)+F(v-h, t, r, b1, b2))/h**2
    H[1, 1] = (F(v, t+h, r, b1, b2)-2*F(v, t, r, b1, b2)+F(v, t-h, r, b1, b2))/h**2
    H[0, 1] = H[1, 0] = (F(v+h, t+h, r, b1, b2)-F(v+h, t-h, r, b1, b2)
                         -F(v-h, t+h, r, b1, b2)+F(v-h, t-h, r, b1, b2))/(4*h**2)
    return H

def grad(v, t, r, b1, b2, h=1e-6):
    return np.array([(F(v+h, t, r, b1, b2)-F(v-h, t, r, b1, b2))/(2*h),
                     (F(v, t+h, r, b1, b2)-F(v, t-h, r, b1, b2))/(2*h)])

rng = np.random.default_rng(86260)
worst = 0.0; cnt = 0
while cnt < 30:
    r = rng.uniform(0.375, 0.38); bc = math.acos(r)
    b1 = rng.uniform(bc/2, bc); b2 = rng.uniform(bc/2, bc); delta = rng.uniform(-b2, b1)
    fb = fiber(r, b1, b2, delta)
    if fb is None: continue
    H_ = rng.uniform(fb[0], fb[1]); v, t = H_*math.cos(delta), H_*math.sin(delta)
    Ha = hess(v, t, r, b1, b2); Hn = nh(v, t, r, b1, b2)
    worst = max(worst, float(np.abs(Ha-Hn).max())); cnt += 1
P("calibration of the CORRECTED analytic Hessian vs finite differences over 30 legal points:")
P("   worst |analytic - numeric| = %.3e  (finite-difference error level)" % worst)

def obj_lam(y):
    r, b1, b2, delta, fh = y
    r = min(max(r, 0.375), 0.38); bc = math.acos(r); bm = bmin(r)
    if not (bm <= b1 <= bc and bm <= b2 <= bc): return 1e3
    fb = fiber(r, b1, b2, delta)
    if fb is None or not (0 <= fh <= 1): return 1e3
    H_ = fb[0] + fh*(fb[1]-fb[0])
    return float(np.linalg.eigvalsh(hess(H_*math.cos(delta), H_*math.sin(delta), r, b1, b2))[1])

P("")
P("=== DE min lambda_max with the CORRECTED objective (2 seeds x 80, width-legal) ===")
for seed in (86260, 86261):
    sol = differential_evolution(obj_lam, [(0.375, 0.38), (0.60, 1.19), (0.60, 1.19), (-1.19, 1.19), (0, 1)],
                                 seed=seed, popsize=12, maxiter=80, tol=1e-12, polish=True, init='sobol')
    r, b1, b2, delta, fh = sol.x; r = min(max(r, 0.375), 0.38)
    fb = fiber(r, b1, b2, delta)
    if fb is None: P("  seed %d: infeasible result" % seed); continue
    H_ = fb[0] + fh*(fb[1]-fb[0]); v, t = H_*math.cos(delta), H_*math.sin(delta)
    ev = np.linalg.eigvalsh(hess(v, t, r, b1, b2))
    P("  seed %d: min lambda_max = %+.6f (lam_min %+.6f) at r=%.5f b1=%.5f b2=%.5f delta=%+.5f H=%.5f"
      % (seed, ev[1], ev[0], r, b1, b2, delta, H_))
    P("          width-legal: %s (bmin=%.5f) ; H interior: %s ; sum c/L = %.4f ; trace = %+.4f"
      % (b1 >= bmin(r) and b2 >= bmin(r), bmin(r), fb[0] < H_ < fb[1], c1/0.0 if False else
         (lambda LL: c1/LL[0]+c2/LL[1])([math.hypot(v-(2*r*math.sin(b1)*math.cos(b1)),
                                                       t-(2*r*math.sin(b1)*math.sin(b1))),
                                        math.hypot(v-(2*r*math.sin(b2)*math.cos(b2)),
                                                       t+(2*r*math.sin(b2)*math.sin(b2)))]),
         ev[0]+ev[1]))

def obj_grad(y):
    r, b1, b2, delta, fh = y
    r = min(max(r, 0.375), 0.38); bc = math.acos(r); bm = bmin(r)
    if not (bm <= b1 <= bc and bm <= b2 <= bc): return 1e3
    fb = fiber(r, b1, b2, delta)
    if fb is None or not (0 <= fh <= 1): return 1e3
    H_ = fb[0] + fh*(fb[1]-fb[0])
    v, t = H_*math.cos(delta), H_*math.sin(delta)
    g = grad(v, t, r, b1, b2)
    return float(np.linalg.norm(g)) if np.isfinite(g).all() else 1e3

P("")
P("=== DE min |grad F| with the CORRECTED objective (2 seeds x 80) ===")
for seed in (86270, 86271):
    sol = differential_evolution(obj_grad, [(0.375, 0.38), (0.60, 1.19), (0.60, 1.19), (-1.19, 1.19), (0, 1)],
                                 seed=seed, popsize=12, maxiter=80, tol=1e-12, polish=True, init='sobol')
    r, b1, b2, delta, fh = sol.x; r = min(max(r, 0.375), 0.38)
    fb = fiber(r, b1, b2, delta)
    if fb is None: P("  seed %d: infeasible" % seed); continue
    H_ = fb[0] + fh*(fb[1]-fb[0]); v, t = H_*math.cos(delta), H_*math.sin(delta)
    ev = np.linalg.eigvalsh(hess(v, t, r, b1, b2)); gn = float(np.linalg.norm(grad(v, t, r, b1, b2)))
    P("  seed %d: |grad| = %.3e ; eigen = (%+.4f, %+.4f) -> %s ; r=%.5f b1=%.5f b2=%.5f delta=%+.5f H=%.5f"
      % (seed, gn, ev[0], ev[1], 'local min' if ev[0] > 0 else ('saddle' if ev[1] > 0 else 'NSD'),
         r, b1, b2, delta, H_))
    P("          width-legal: %s ; H interior: %s (fiber [%.5f, %.5f])"
      % (b1 >= bmin(r) and b2 >= bmin(r), fb[0] < H_ < fb[1], fb[0], fb[1]))

Path('out/p43_corrected.log').write_text("\n".join(lines) + "\n")
