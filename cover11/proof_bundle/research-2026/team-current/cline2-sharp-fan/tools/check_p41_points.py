# -*- coding: utf-8 -*-
"""Are the C862b diagnostic points INTERIOR to the lens?  (standalone re-definition)"""
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
SUMB = 2*(be1+be2)

def geo(r, b1, b2, delta):
    s = math.sqrt(1-r*r)
    if not (delta > -b2 and delta < b1): return None
    A, B = b1-delta, b2+delta
    if min(A, B) <= 0: return None
    D1, D2 = 2*r*math.sin(b1), 2*r*math.sin(b2)
    return s, A, B, (D1*math.cos(b1), D1*math.sin(b1)), (D2*math.cos(b2), -D2*math.sin(b2))

def fiber(r, b1, b2, delta):
    g = geo(r, b1, b2, delta)
    if g is None: return None
    s, A, B, Q1, Q2 = g
    disc = s*s*math.cos(delta)**2 - 2*r*(1-r)
    if disc < 0: return None
    lo = max(2*r*abs(math.sin(delta)), s*math.cos(delta)-math.sqrt(disc))
    hi = min(2*r*math.sin(b1+A), 2*r*math.sin(b2+B), s*math.cos(delta)+math.sqrt(disc))
    return (lo, hi) if lo <= hi else None

def F(v, t, r, b1, b2):
    g = geo(r, b1, b2, math.atan2(t, v)); s, A, B, Q1, Q2 = g
    L1 = math.hypot(v-Q1[0], t-Q1[1]); L2 = math.hypot(v-Q2[0], t-Q2[1])
    T, D = b1+b2, b1-b2
    return (r*(1-math.cos(T)*math.cos(D))*v - r*math.cos(T)*math.sin(D)*t
            + a1*math.atan2(t-Q1[1], v-Q1[0]) + a2*math.atan2(t-Q2[1], v-Q2[0])
            + be1*L1*L1 + g1*L1 + be2*L2*L2 + g2*L2)

def hess(v, t, r, b1, b2):
    g = geo(r, b1, b2, math.atan2(t, v)); s, A, B, Q1, Q2 = g
    H = np.array([[SUMB, 0.0], [0.0, SUMB]])
    for Q, c, a in ((Q1, c1, a1), (Q2, c2, a2)):
        L = math.hypot(v-Q[0], t-Q[1]); n = np.array([(v-Q[0])/L, (t-Q[1])/L])
        H -= (c/L)*(np.eye(2) - np.outer(n, n))
        th = -math.pi/4
        w = np.array([math.cos(th)*n[0]-math.sin(th)*n[1], math.sin(th)*n[0]+math.cos(th)*n[1]])
        H += (a/(L*L))*(2*np.outer(w, w) - np.eye(2))
    return H

J = json.loads(Path('out/p41_interior_critical.json').read_text())
def check(tag, r, b1, b2, delta, H_):
    fb = fiber(r, b1, b2, delta)
    if fb is None: print(tag, 'INFEASIBLE'); return
    lo, hi = fb; v, t = H_*math.cos(delta), H_*math.sin(delta)
    g = geo(r, b1, b2, delta); ev = np.linalg.eigvalsh(hess(v, t, r, b1, b2))
    print('%s  r=%.5f b1=%.5f b2=%.5f delta=%+.5f H=%.6f' % (tag, r, b1, b2, delta, H_))
    print('   fiber [%.6f, %.6f]  INTERIOR H: %s  (hi-H=%.2e, H-lo=%.2e)  wedge interior: %s'
          % (lo, hi, lo < H_ < hi, hi-H_, H_-lo, g[1] > 0 and g[2] > 0))
    print('   Hess eigenvalues (%.4f, %.4f)   F=%.6f' % (ev[0], ev[1], F(v, t, r, b1, b2)))

for row in J['de_stationary']:
    check('DE-stationary seed %d' % row['seed'], row['r'], row['b1'], row['b2'], row['delta'], row['H'])
for row in J['de_lambda_max']:
    check('DE-lambda_max  seed %d' % row['seed'], row['r'], row['b1'], row['b2'], row['delta'], row['H'])
b = J['samples'][int(np.argmin([x['lam_max'] for x in J['samples']]))]
check('random best-ND', b['r'], b['b1'], b['b2'], b['delta'], b['H'])
