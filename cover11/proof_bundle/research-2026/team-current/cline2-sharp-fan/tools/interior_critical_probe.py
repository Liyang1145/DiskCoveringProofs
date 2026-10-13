# -*- coding: utf-8 -*-
"""C862b: can the hub objective have an interior LOCAL MAX on legal C848 points?

Interior local max  =>  grad F = 0  AND  Hess F negative semidefinite.
Hess F = 2(beta1+beta2) I - sum_j (c_j/L_j)(I - n_j n_j^T) + sum_j (a_j/L_j^2) M_j,
  n_j = (hub - Q_j)/L_j, M_j = 2 w_j w_j^T - I, w_j = n_j rotated by -pi/4 (polar-angle Hessian).
Structural necessary conditions (from testing w = n_1 and w = n_2):
  c2/L2 + a2/L2^2 >= 2(beta1+beta2)  and  c1/L1 + a1/L1^2 >= 2(beta1+beta2)
  => L1 <= 0.4211 and L2 <= 0.4193  (roots of 2 sum beta L^2 - c_j L - a_j = 0)
and tr(Hess) = 4(beta1+beta2) - sum c_j/L_j <= 0 => sum c_j/L_j >= 5.5835.
Diagnostic: <=400 legal samples + 2 DE runs (80 iters) minimising lambda_max(Hess), and
2 DE runs minimising |grad F| with the Hessian evaluated there.
"""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
from scipy.optimize import differential_evolution

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
OUT = Path(__file__).resolve().parent.parent / 'out'
lines = []
def P(*a):
    s = " ".join(str(x) for x in a); lines.append(s); print(s)

z = json.loads((LEAD / 'joint_nested_frozen.json').read_text(encoding='utf-8-sig'))['z']
R0 = 19/50
a1, a2 = z[1]-z[9], z[3]-z[9]
be1, be2 = z[16]/(4*R0*R0)*-1, z[20]/(4*R0*R0)          # beta1 = -z16/(4R0^2), beta2 = z20/(4R0^2)
g1, g2 = -z[78]/(2*R0), z[82]/(2*R0)
c1, c2 = abs(g1), abs(g2)
SUMB = 2*(be1+be2)
P("coefficients (joint_nested_frozen.json): a1=%.9f a2=%.9f beta1=%.9f beta2=%.9f c1=%.9f c2=%.9f"
  % (a1, a2, be1, be2, c1, c2))
P("2 sum beta = %.9f ; trace condition: sum c_j/L_j >= that ; radial necessary: L1 <= %.6f, L2 <= %.6f"
  % (SUMB, max(np.roots([SUMB, -c1, -a1])), max(np.roots([SUMB, -c2, -a2]))))

def geo(r, b1, b2, delta):
    """chart geometry: returns Q1,Q2 (ring centres in the (v,t) frame), A, B or None if illegal"""
    s = math.sqrt(1-r*r)
    if not (delta > -b2 and delta < b1): return None
    A, B = b1-delta, b2+delta
    if min(A, B) <= 0: return None
    D1, D2 = 2*r*math.sin(b1), 2*r*math.sin(b2)
    Q1 = (D1*math.cos(b1), D1*math.sin(b1))        # hub = Q1 -> hub at c1
    Q2 = (D2*math.cos(b2), -D2*math.sin(b2))
    return s, A, B, D1, D2, Q1, Q2

def fiber(r, b1, b2, delta):
    g_ = geo(r, b1, b2, delta)
    if g_ is None: return None
    s, A, B, D1, D2, Q1, Q2 = g_
    disc = s*s*math.cos(delta)**2 - 2*r*(1-r)
    if disc < 0: return None
    lo = max(2*r*abs(math.sin(delta)), s*math.cos(delta)-math.sqrt(disc))
    hi = min(2*r*math.sin(b1+A), 2*r*math.sin(b2+B), s*math.cos(delta)+math.sqrt(disc))
    return (lo, hi) if lo <= hi else None

def F(v, t, r, b1, b2):
    s = math.sqrt(1-r*r); g_ = geo(r, b1, b2, math.atan2(t, v))
    s_, A, B, D1, D2, Q1, Q2 = g_
    L1 = math.hypot(v-Q1[0], t-Q1[1]); L2 = math.hypot(v-Q2[0], t-Q2[1])
    T, D = b1+b2, b1-b2
    return (r*(1-math.cos(T)*math.cos(D))*v - r*math.cos(T)*math.sin(D)*t
            + a1*math.atan2(t-Q1[1], v-Q1[0]) + a2*math.atan2(t-Q2[1], v-Q2[0])
            + be1*L1*L1 + g1*L1 + be2*L2*L2 + g2*L2)

def analytic_hess(v, t, r, b1, b2, rot=+1):
    """Hess F; rot=+1 uses w_j = n_j rotated by -pi/4 (the convention verified vs finite diffs)"""
    s = math.sqrt(1-r*r); g_ = geo(r, b1, b2, math.atan2(t, v)); s_, A, B, D1, D2, Q1, Q2 = g_
    H = np.array([[SUMB, 0.0], [0.0, SUMB]])
    for Q, L, c, a in ((Q1, math.hypot(v-Q1[0], t-Q1[1]), c1, a1),
                       (Q2, math.hypot(v-Q2[0], t-Q2[1]), c2, a2)):
        n = np.array([(v-Q[0])/L, (t-Q[1])/L])
        H -= (c/L)*(np.eye(2) - np.outer(n, n))
        th = (rot*math.pi/4)
        w = np.array([math.cos(th)*n[0] - math.sin(th)*n[1], math.sin(th)*n[0] + math.cos(th)*n[1]])
        H += (a/(L*L))*(2*np.outer(w, w) - np.eye(2))
    return H

def numeric_hess(v, t, r, b1, b2, h=1e-6):
    H = np.zeros((2, 2))
    fx = F(v+h, t, r, b1, b2) - F(v-h, t, r, b1, b2)
    fy = F(v, t+h, r, b1, b2) - F(v, t-h, r, b1, b2)
    H[0, 0] = (F(v+h, t, r, b1, b2)-2*F(v, t, r, b1, b2)+F(v-h, t, r, b1, b2))/h**2
    H[1, 1] = (F(v, t+h, r, b1, b2)-2*F(v, t, r, b1, b2)+F(v, t-h, r, b1, b2))/h**2
    H[0, 1] = H[1, 0] = (F(v+h, t+h, r, b1, b2)-F(v+h, t-h, r, b1, b2)
                         -F(v-h, t+h, r, b1, b2)+F(v-h, t-h, r, b1, b2))/(4*h**2)
    return H

def grad(v, t, r, b1, b2, h=1e-6):
    return np.array([(F(v+h, t, r, b1, b2)-F(v-h, t, r, b1, b2))/(2*h),
                     (F(v, t+h, r, b1, b2)-F(v, t-h, r, b1, b2))/(2*h)])

def sample_legal(rng):
    r = rng.uniform(0.375, 0.38); bc = math.acos(r)
    b1 = rng.uniform(bc/2, bc); b2 = rng.uniform(bc/2, bc)
    delta = rng.uniform(-b2, b1); fb = fiber(r, b1, b2, delta)
    if fb is None: return None
    H = rng.uniform(fb[0], fb[1])
    return r, b1, b2, delta, H, fb

def report(v, t, r, b1, b2, tag):
    s_ = math.sqrt(1-r*r); g_ = geo(r, b1, b2, math.atan2(t, v)); s_, A, B, D1, D2, Q1, Q2 = g_
    L1 = math.hypot(v-Q1[0], t-Q1[1]); L2 = math.hypot(v-Q2[0], t-Q2[1])
    d2r = math.sqrt(max(0.0, 1+math.cos(b1+b2)**2-2*math.cos(b1+b2)*math.cos(b1-b2)))
    ev = np.linalg.eigvalsh(hess_at(v, t, r, b1, b2))
    try: gn = float(np.linalg.norm(grad(v, t, r, b1, b2)))
    except Exception: gn = float('nan')
    return {'tag': tag, 'r': r, 'b1': b1, 'b2': b2, 'delta': math.atan2(t, v), 'H': math.hypot(v, t),
            'L1': L1, 'L2': L2, 'd_over_2r': d2r, 'lam_min': float(ev[0]), 'lam_max': float(ev[1]),
            'trace': float(ev[0]+ev[1]), 'grad_norm': gn, 'F': F(v, t, r, b1, b2),
            'sum_c_over_L': c1/L1+c2/L2, 'wedge_A': A, 'wedge_B': B,
            'hubnorm_resid': (v-s_)**2 + t*t - (1-r)**2}

P("")
P("=== calibration: analytic vs numeric Hessian — pick the rotation convention that matches ===")
def calib(rot, n=40):
    rngc = np.random.default_rng(86220); worst = 0.0; cnt = 0
    while cnt < n:
        smp = sample_legal(rngc)
        if smp is None: continue
        cnt += 1
        r, b1, b2, delta, H, fb = smp
        v, t = H*math.cos(delta), H*math.sin(delta)
        Ha = analytic_hess(v, t, r, b1, b2, rot); Hn = numeric_hess(v, t, r, b1, b2)
        worst = max(worst, float(np.abs(Ha-Hn).max()))
    return worst
w_plus, w_minus = calib(+1), calib(-1)
P("  worst |analytic - numeric| with rot=+1 (w = R(+pi/4)n): %.3e" % w_plus)
P("  worst |analytic - numeric| with rot=-1 (w = R(-pi/4)n): %.3e" % w_minus)
ROT = -1 if w_minus <= w_plus else +1
P("  using rot = %+d  (this is the polar-angle Hessian convention; the (n, n^perp) form is"
  " [[0,-1/L],[-1/L,0]], matching the lead's matrix)" % ROT)
def hess_at(v, t, r, b1, b2):
    return analytic_hess(v, t, r, b1, b2, ROT)

P("")
P("=== A. random legal diagnostic (400 samples): lambda_max and |grad| ===")
rng = np.random.default_rng(86225)
best_nd = None; best_g = None; n_nd = 0; n_legal = 0; rows = []
while n_legal < 400:
    smp = sample_legal(rng)
    if smp is None: continue
    n_legal += 1
    r, b1, b2, delta, H, fb = smp
    v, t = H*math.cos(delta), H*math.sin(delta)
    rec = report(v, t, r, b1, b2, 'random')
    rows.append(rec)
    if rec['lam_max'] < 0: n_nd += 1
    if best_nd is None or rec['lam_max'] < best_nd['lam_max']: best_nd = rec
    if rec['grad_norm'] == rec['grad_norm'] and (best_g is None or rec['grad_norm'] < best_g['grad_norm']):
        best_g = rec
P("  legal samples: %d ; with lambda_max(Hess) < 0 (locally concave): %d" % (n_legal, n_nd))
P("  min lambda_max over samples = %.6f   at r=%.5f b1=%.5f b2=%.5f delta=%+.5f H=%.5f"
  % (best_nd['lam_max'], best_nd['r'], best_nd['b1'], best_nd['b2'], best_nd['delta'], best_nd['H']))
P("     (L1=%.4f L2=%.4f sum c/L=%.4f trace=%.4f, d/(2r)=%.4f)"
  % (best_nd['L1'], best_nd['L2'], best_nd['sum_c_over_L'], best_nd['trace'], best_nd['d_over_2r']))
P("  min |grad| over samples = %.6f at r=%.5f b1=%.5f b2=%.5f delta=%+.5f (lam_max there = %.4f)"
  % (best_g['grad_norm'], best_g['r'], best_g['b1'], best_g['b2'], best_g['delta'], best_g['lam_max']))
P("  sampled lambda_max range: [%.4f, %.4f] ; fraction ND = %.3f"
  % (min(x['lam_max'] for x in rows), max(x['lam_max'] for x in rows), n_nd/len(rows)))

P("")
P("=== B. DE minimising lambda_max(Hess) over legal points (2 seeds x 80 iters) ===")
def obj_nd(y):
    r, b1, b2, delta, fh = y
    bc = math.acos(min(max(r, 0.375), 0.38))
    if not (bc/2 < b1 <= bc and bc/2 < b2 <= bc): return 1e3
    fb = fiber(r, b1, b2, delta)
    if fb is None: return 1e3
    H = fb[0] + fh*(fb[1]-fb[0])
    v, t = H*math.cos(delta), H*math.sin(delta)
    return float(np.linalg.eigvalsh(hess_at(v, t, r, b1, b2))[1])
de_rows = []
for seed in (86230, 86231):
    sol = differential_evolution(obj_nd, [(0.375, 0.38), (0.59, 1.19), (0.59, 1.19), (-1.19, 1.19), (0, 1)],
                                 seed=seed, popsize=12, maxiter=80, tol=1e-10, polish=True, init='sobol')
    r, b1, b2, delta, fh = sol.x
    fb = fiber(r, b1, b2, delta); H = fb[0] + fh*(fb[1]-fb[0])
    v, t = H*math.cos(delta), H*math.sin(delta)
    rec = report(v, t, r, b1, b2, 'DE-lambda_max'); rec['seed'] = seed; rec['nfev'] = int(sol.nfev)
    de_rows.append(rec)
    P("  seed %d: min lambda_max = %.6f at r=%.5f b1=%.5f b2=%.5f delta=%+.5f H=%.5f ; |grad|=%.5f"
      % (seed, rec['lam_max'], rec['r'], rec['b1'], rec['b2'], rec['delta'], rec['H'], rec['grad_norm']))
    P("     L1=%.4f L2=%.4f sum c/L=%.4f trace=%.4f d/(2r)=%.4f"
      % (rec['L1'], rec['L2'], rec['sum_c_over_L'], rec['trace'], rec['d_over_2r']))

P("")
P("=== C. DE minimising |grad F| (stationarity) and the Hessian there ===")
def obj_grad(y):
    r, b1, b2, delta, fh = y
    bc = math.acos(min(max(r, 0.375), 0.38))
    if not (bc/2 < b1 <= bc and bc/2 < b2 <= bc): return 1e3
    fb = fiber(r, b1, b2, delta)
    if fb is None: return 1e3
    H = fb[0] + fh*(fb[1]-fb[0])
    v, t = H*math.cos(delta), H*math.sin(delta)
    return float(np.linalg.norm(grad(v, t, r, b1, b2)))
st_rows = []
for seed in (86240, 86241):
    sol = differential_evolution(obj_grad, [(0.375, 0.38), (0.59, 1.19), (0.59, 1.19), (-1.19, 1.19), (0, 1)],
                                 seed=seed, popsize=12, maxiter=80, tol=1e-10, polish=True, init='sobol')
    r, b1, b2, delta, fh = sol.x
    fb = fiber(r, b1, b2, delta); H = fb[0] + fh*(fb[1]-fb[0])
    v, t = H*math.cos(delta), H*math.sin(delta)
    rec = report(v, t, r, b1, b2, 'DE-stationary'); rec['seed'] = seed; rec['nfev'] = int(sol.nfev)
    st_rows.append(rec)
    P("  seed %d: min |grad| = %.6e at r=%.5f b1=%.5f b2=%.5f delta=%+.5f H=%.5f ; lam_max=%.4f lam_min=%.4f"
      % (seed, rec['grad_norm'], rec['r'], rec['b1'], rec['b2'], rec['delta'], rec['H'],
         rec['lam_max'], rec['lam_min']))
    P("     L1=%.4f L2=%.4f d/(2r)=%.4f F=%.6f" % (rec['L1'], rec['L2'], rec['d_over_2r'], rec['F']))

P("")
P("=== verdict inputs ===")
P("  * any sample with lambda_max < 0 ? %s (%d of %d)" % (n_nd > 0, n_nd, n_legal))
P("  * best DE lambda_max = %.6f (< 0 would certify a concave point) " % min(x['lam_max'] for x in de_rows))
P("  * best near-stationary point has lam_max = %.4f (>= 0 => a saddle, not an interior max)"
  % min(x['lam_max'] for x in st_rows))

(OUT / 'p41_interior_critical.json').write_text(json.dumps(
    {'scope': 'diagnostic only, not a certificate; legal C848 hub points, current coefficients',
     'samples': rows, 'de_lambda_max': de_rows, 'de_stationary': st_rows}, indent=1, default=float))
with open(OUT / 'p41_interior_critical.txt', 'w', encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")

