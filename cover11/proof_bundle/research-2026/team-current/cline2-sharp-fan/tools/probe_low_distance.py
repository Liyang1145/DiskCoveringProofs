# -*- coding: utf-8 -*-
"""C862 obligation: bounded numeric search over the LOW-DISTANCE complement d/(2r) < 1.38.

Reuses the probe_nested_patch.py objective structure (boundary-first chart + nested patch),
but OVERRIDES the frozen coefficients with the CURRENT joint_nested_frozen.json (the probe's
chain loads the old joint_patch_frozen_v2.json).
Exploratory only: sampling is NOT a certificate.
Records the legal best outer/hub/widths and every margin.
"""
import os, json, math, sys
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
from scipy.optimize import differential_evolution, minimize_scalar

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
sys.path.insert(0, str(LEAD))     # the exec'd chain imports sibling modules by name
OUT = Path(__file__).resolve().parent.parent / 'out'
P = LEAD
m = "\nif __name__"
s_arc = (P / 'check_arc_chart.py').read_text(encoding='utf-8')
assert s_arc.count(m) == 1
nsa = {'__file__': str(P / 'check_arc_chart.py')}
exec(s_arc.split(m)[0], nsa)                       # brings in chart, reduced, sectorleft, width, g, ns
inner = nsa['ns']                                  # namespace of check_joint_reduced.py
OLDZ = np.array(inner['z'], dtype=float)
NEWZ = np.array(json.loads((P / 'joint_nested_frozen.json').read_text(encoding='utf-8-sig'))['z'], dtype=float)
inner['z'] = NEWZ                                  # <-- the override: patch/reduced now see the CURRENT z
R, pi, g = nsa['R'], nsa['pi'], nsa['g']
width, sectorleft, chart, reduced = nsa['width'], nsa['sectorleft'], nsa['chart'], nsa['reduced']
z = NEWZ

def d_over_2r(b1, b2):
    T, D = b1 + b2, b1 - b2
    return math.sqrt(max(0.0, 1 + math.cos(T)**2 - 2*math.cos(T)*math.cos(D)))

def scalarmax(fun, lo, hi):
    grid = np.linspace(lo, hi, 13); vals = [fun(x) for x in grid]
    choices = list(zip(vals, grid))
    for j in range(1, 12):
        if vals[j] >= max(vals[j-1], vals[j+1]):
            ss = minimize_scalar(lambda x: -fun(x), bounds=(grid[j-1], grid[j+1]),
                                 method='bounded', options={'xatol': 1e-10})
            choices.append((-ss.fun, ss.x))
    return max(choices)

def margins(r, b1, b2, A, B, delta, H, lo, hi, W1, W3, w1, w3):
    s = math.sqrt(1-r*r)
    # hub-norm disk in (v,t) frame: (v-s)^2+t^2 <= (1-r)^2 with v=H cos d, t=H sin d
    v, t = H*math.cos(delta), H*math.sin(delta)
    normres = (v-s)**2 + t**2 - (1-r)**2
    d1res = (v - r*math.sin(2*b1))**2 + (t + r*math.cos(2*b1))**2 - r*r
    d2res = (v - r*math.sin(2*b2))**2 + (t - r*math.cos(2*b2))**2 - r*r
    return {'H_lo': lo, 'H_hi': hi, 'H_fiber_margin': hi-lo, 'H_at_hi': H-hi,
            'hubnorm_residual': normres, 'face1_disk_residual': d1res, 'face2_disk_residual': d2res,
            'wedge_margin_A': A, 'wedge_margin_B': B, 'delta': delta,
            'width1_margin': w1-g, 'width3_margin': w3-g,
            'W1-g': W1-g, 'W3-g': W3-g, 'd_over_2r': d_over_2r(b1, b2)}

def evaluate(y, detail=False, cap_distance=1.38):
    r, q1, q2, qA = y
    bc = math.acos(r); b1 = bc*(.5+.5*q1); b2 = bc*(.5+.5*q2); A = qA*(b1+b2); B = b1+b2-A; delta = b1-A
    if d_over_2r(b1, b2) >= cap_distance: return None          # COMPLEMENT FILTER
    s = math.sqrt(1-r*r); disc = s*s*math.cos(delta)**2 - 2*r*(1-r)
    if disc < 0: return None
    lo = max(2*r*abs(math.sin(delta)), s*math.cos(delta)-math.sqrt(disc))
    hi = min(2*r*math.sin(b1+A), 2*r*math.sin(b2+B), s*math.cos(delta)+math.sqrt(disc))
    W1, W3 = width(r, b1), width(r, b2)
    if lo > hi or min(W1, W3) < g: return None
    D1, D2 = 2*r*math.sin(b1), 2*r*math.sin(b2)
    def hf(H):
        h1 = math.atan2(D1*math.sin(A), H-D1*math.cos(A)); h2 = math.atan2(D2*math.sin(B), H-D2*math.cos(B))
        e1 = math.hypot(H-D1*math.cos(A), D1*math.sin(A))/(2*R); e3 = math.hypot(H-D2*math.cos(B), D2*math.sin(B))/(2*R)
        return (H*(D1*math.sin(A)+D2*math.sin(B))/2 + (z[1]-z[9])*h1 + (z[3]-z[9])*h2
                - z[16]*e1*e1 - z[78]*e1 + z[20]*e3*e3 + z[82]*e3)
    def wf(w, b, i):
        a, u = sectorleft(r, b, w); tt = r/R
        L = math.atan2(tt*math.sin(a), u-tt*math.cos(a))
        mu, h, d, dl = (z[1], z[112], z[34], z[96]) if i == 1 else (z[3], z[115], z[39], z[101])
        return R*r*u*math.sin(a)/2 + (w-math.sin(w))/2 - mu*a - d*u*u - dl*u + h*(L+w/2)
    hm, H = scalarmax(hf, lo, hi); fm, w1 = scalarmax(lambda w: wf(w, b1, 1), g, W1)
    gm_, w3 = scalarmax(lambda w: wf(w, b2, 3), g, W3)
    w2 = 2*math.asin(r)
    K = (pi*(z[113]+z[114]-z[2]) + z[1]*(b1-pi+A) + z[3]*(b2-pi+B)
         + (w2-math.sin(w2))/2 + r*r*(math.sin(2*b1)+math.sin(2*b2))/2)
    total = K + hm + fm + gm_
    if not detail: return total
    y7 = [r, b1, b2, (w1-g)/(W1-g), (w3-g)/(W3-g), qA, (H-lo)/(hi-lo)]
    x = chart(y7)
    if x is None: return None
    direct = reduced(x)
    fh = hf(H); fw1 = wf(w1, b1, 1); fw3 = wf(w3, b2, 3)
    return {'value': total, 'r': r, 'b1': b1, 'b2': b2, 'A': A, 'B': B, 'delta': delta, 'H': H,
            'w1': w1, 'w3': w3, 'K': K, 'hub_term': fh, 'width1_term': fw1, 'width3_term': fw3,
            'H_argmax_is_hi': bool(abs(H-hi) < 1e-9),
            'margins': margins(r, b1, b2, A, B, delta, H, lo, hi, W1, W3, w1, w3),
            'chart': y7, 'direct_value': direct, 'direct_vs_sum': direct-total,
            'parts_minus_total': fh+fw1+fw3+K-total}

# ---- sanity: the override really changed the coefficients -------------------------────
# NOTE: evaluate() uses the module-level NEWZ, so the correct test is on the exec'd chain
# (patch/reduced), which is what the detail path cross-checks against.
test_y = [0.3772, 0.60, 0.70, 0.55]
v_new = evaluate(test_y)
y7 = [0.3772, math.acos(0.3772)*(0.5+0.5*0.60), math.acos(0.3772)*(0.5+0.5*0.70),
      0.5, 0.5, 0.55, 0.5]
x_test = chart(y7)
inner['z'] = OLDZ; r_old = None if x_test is None else reduced(x_test)
inner['z'] = NEWZ; r_new = None if x_test is None else reduced(x_test)
print('[check] evaluate() with CURRENT z =', None if v_new is None else round(v_new, 9))
print('[check] exec-chain reduced(): CURRENT z =', None if r_new is None else round(r_new, 9),
      '| OLD v2 z =', None if r_old is None else round(r_old, 9),
      '| override effective:', (r_new != r_old))
print('[check] detail path agrees with the sum:', end=' ')
dd = evaluate(test_y, True)
print(dd is not None and abs(dd['direct_value'] - dd['value']) < 1e-8)

if __name__ == '__main__':
    rows = []
    for seed in range(2):
        def f(y):
            v = evaluate(y); return 1e3 if v is None else -v
        sol = differential_evolution(f, [(.375, .38), (0, 1), (0, 1), (.0001, .9999)],
                                     seed=8620+seed, popsize=12, maxiter=80, tol=1e-9,
                                     polish=True, init='sobol')
        rr = evaluate(sol.x, True)
        rr['seed'] = 8620+seed; rr['y'] = list(sol.x); rr['nfev'] = int(sol.nfev)
        rows.append(rr)
        print(json.dumps({k: rr[k] for k in ('seed', 'value', 'r', 'b1', 'b2', 'A', 'delta', 'H',
                                             'w1', 'w3', 'H_argmax_is_hi', 'nfev')}, indent=1), flush=True)
        print('   margins:', json.dumps(rr['margins'], indent=1), flush=True)
    best = max(rows, key=lambda a: a['value'])
    print('[BEST over complement]', best['value'], 'at r=%.6f b1=%.6f b2=%.6f d/(2r)=%.6f'
          % (best['r'], best['b1'], best['b2'], best['margins']['d_over_2r']))
    print('[threshold 28.107045] gap =', 28.107045 - best['value'])
    (OUT / 'p40_low_distance_probe.json').write_text(json.dumps(
        {'scope': 'exploratory bounded search over d/(2r)<1.38 complement; NOT a certificate',
         'coefficients': 'joint_nested_frozen.json', 'runs': rows}, indent=2, default=float))

